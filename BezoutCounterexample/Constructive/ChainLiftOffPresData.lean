import BezoutCounterexample.Constructive.ChainLiftOffPres
import BezoutCounterexample.Constructive.ChainLiftCanon
import BezoutCounterexample.Constructive.Groebner
import BezoutCounterexample.Principalization.ChainLiftEnum

/-!
# The torsor presentation as data (Task A C2 remainder, leaf)

`exists_offStep` (ChainLiftOffPres) takes its relations `G'` from `exists_ker_list` (a generating
list of the kernel, an existential) and clears denominators with `fin_choice`. Here both are data:

* `denOf`, `clearWith`, `toQZ_clearWith`: clearing the denominators of a rational polynomial by
  the product of the denominators of its coefficients (no choice);
* `kerIdeal`, `kerList`: the kernel of `aeval f` modulo `(G₀)` and its canonical generators
  (`canonGens` over `enumPoly`, membership decided by `mem_lspan_dec`), `kerList_spec`;
* `presList`: the integer relations of the torsor presentation, `presList_spec` (the presentation
  property of `exists_offStep`);
* `offStepOf`, `offStepOf_spec`: the `OffStep` of `exists_offStep` as a definition.

Leaf module.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace BezoutCounterexample.Constructive

open MvPolynomial

section Clear

variable {σ : Type*} [DecidableEq σ]

omit [DecidableEq σ] in

/-- The product of the denominators of the coefficients. -/
def denOf (q : MvPolynomial σ ℚ) : ℕ := ∏ m ∈ q.support, (q.coeff m).den

theorem denOf_pos (q : MvPolynomial σ ℚ) : 0 < denOf q :=
  Finset.prod_pos fun m _ => (q.coeff m).den_pos

lemma coeff_monomial_ne' {R : Type*} [CommSemiring R] {m n : σ →₀ ℕ} (h : n ≠ m) (a : R) :
    (monomial n a : MvPolynomial σ R).coeff m = 0 := by
  rw [coeff_monomial]; exact ite_eq_right_iff.2 fun h' => absurd h' h

lemma dvd_den_mul_int' {q : ℚ} {D : ℕ} (h : q.den ∣ D) : ∃ z : ℤ, (D : ℚ) * q = z := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨q.num * m, ?_⟩
  push_cast
  have := Rat.mul_den_eq_num q
  calc ((q.den : ℚ) * m) * q = (q * q.den) * m := by ring
    _ = q.num * m := by rw [this]

omit [DecidableEq σ] in
/-- The integer polynomial `D · q` (when `denOf q ∣ D`). -/
def clearWith (D : ℕ) (q : MvPolynomial σ ℚ) : MvPolynomial σ ℤ :=
  ∑ m ∈ q.support, monomial m (((D : ℚ) * q.coeff m).num)

theorem toQZ_clearWith (q : MvPolynomial σ ℚ) {D : ℕ} (h : denOf q ∣ D) :
    toQZ (clearWith D q) = (D : MvPolynomial σ ℚ) * q := by
  ext m
  rw [coeff_map, ← map_natCast C, coeff_C_mul, clearWith, coeff_sum]
  by_cases hm : m ∈ q.support
  · rw [Finset.sum_eq_single m (fun b _ hb => coeff_monomial_ne' hb _) (fun h' => absurd hm h'),
      coeff_monomial, ite_eq_left_iff.2 fun h' => absurd rfl h']
    obtain ⟨w, hw⟩ := dvd_den_mul_int' ((Finset.dvd_prod_of_mem _ hm).trans h)
    change ((((D : ℚ) * q.coeff m).num : ℤ) : ℚ) = _
    rw [hw, Rat.num_intCast]
  · rw [Finset.sum_eq_zero fun b hb => coeff_monomial_ne' (fun h' : b = m => hm (by rw [← h']; exact hb)) _,
      MvPolynomial.notMem_support_iff.1 hm, mul_zero]
    rfl

end Clear

section Ker

variable {n m : ℕ}

/-- The kernel of `ℚ[Y_m] → ℚ[Y_n] ⧸ (G₀)`, `Y ↦ f`. -/
def kerIdeal (G₀ : List (MvPolynomial (Fin n) ℚ)) (f : Fin m → MvPolynomial (Fin n) ℚ) :
    Ideal (MvPolynomial (Fin m) ℚ) :=
  Ideal.comap (aeval f).toRingHom (lspan G₀)

theorem mem_kerIdeal (G₀ : List (MvPolynomial (Fin n) ℚ)) (f : Fin m → MvPolynomial (Fin n) ℚ)
    (h : MvPolynomial (Fin m) ℚ) : h ∈ kerIdeal G₀ f ↔ aeval f h ∈ lspan G₀ := Iff.rfl

theorem kerIdeal_fg (G₀ : List (MvPolynomial (Fin n) ℚ)) (f : Fin m → MvPolynomial (Fin n) ℚ) :
    ∃ L : List (MvPolynomial (Fin m) ℚ), kerIdeal G₀ f = lspan L := by
  obtain ⟨L, hL⟩ := exists_ker_list G₀ f
  exact ⟨L, Ideal.ext fun h => hL h⟩

/-- **The canonical generators of the kernel** (`canonGens` over `enumPoly`). -/
def kerList (G₀ : List (MvPolynomial (Fin n) ℚ)) (f : Fin m → MvPolynomial (Fin n) ℚ) :
    List (MvPolynomial (Fin m) ℚ) :=
  canonGens (enumPoly m) (enumPoly_surjective m) mem_lspan_dec (kerIdeal G₀ f) (kerIdeal_fg G₀ f)

theorem kerList_spec (G₀ : List (MvPolynomial (Fin n) ℚ)) (f : Fin m → MvPolynomial (Fin n) ℚ)
    (h : MvPolynomial (Fin m) ℚ) : aeval f h ∈ lspan G₀ ↔ h ∈ lspan (kerList G₀ f) := by
  rw [kerList, lspan_canonGens]; exact Iff.rfl

/-- Clearing the denominators of a list does not change its span over `ℚ`. -/
theorem lspan_map_clear (L : List (MvPolynomial (Fin m) ℚ)) :
    lspan ((L.map fun q => clearWith (denOf q) q).map toQZ) = lspan L := by
  apply le_antisymm
  · rw [lspan, Ideal.span_le]
    intro p hp
    simp only [List.map_map, Set.mem_ofPred_eq, List.mem_map, Function.comp_apply] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [toQZ_clearWith q dvd_rfl]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span hq)
  · rw [lspan, Ideal.span_le]
    intro q hq
    have hD : ((denOf q : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (denOf_pos q).ne'
    have hmem : toQZ (clearWith (denOf q) q) ∈
        lspan ((L.map fun q => clearWith (denOf q) q).map toQZ) :=
      Ideal.subset_span (List.mem_map.2 ⟨_, List.mem_map.2 ⟨q, hq, rfl⟩, rfl⟩)
    have : q = C ((denOf q : ℚ))⁻¹ * toQZ (clearWith (denOf q) q) := by
      rw [toQZ_clearWith q dvd_rfl, ← mul_assoc, ← map_natCast C, ← C_mul, inv_mul_cancel₀ hD,
        C_1, one_mul]
    rw [SetLike.mem_coe, this]
    exact Ideal.mul_mem_left _ _ hmem

end Ker

section Pres

variable {N r : ℕ}
variable (G : List (MvPolynomial (Fin N) ℤ)) (g : Fin r → MvPolynomial (Fin N) ℤ) (d : Fin r → ℕ)

/-- **The integer relations of the torsor presentation**, as data. -/
def presList : List (MvPolynomial (Fin (N + (1 + (r + r)))) ℤ) :=
  (kerList (H₀ G g d) (fvec g d)).map fun q => clearWith (denOf q) q

theorem presList_spec (h : MvPolynomial (Fin (N + (1 + (r + r)))) ℚ) :
    aeval (fvec g d) h ∈ lspan (H₀ G g d) ↔ h ∈ lspan ((presList G g d).map toQZ) := by
  rw [presList, lspan_map_clear, ← kerList_spec]

/-- **The `OffStep` of the torsor presentation**, as data (`exists_offStep`). -/
def offStepOf {D₂ : ℕ} (hD : D₂ ≠ 0) (E : Fin r → ℕ) (hEd : ∀ i, E i * d i = D₂)
    (hE : ∀ i, Even (E i)) : OffStep N (N + (1 + (r + r))) (Fin r) := by
  -- the lift
  have hlift : ∀ w s y σ, PtG G w → 0 < s → (∀ i, evalR w (g i) = s ^ d i * y i) →
      ∑ i, y i * σ i = 1 → PtG (presList G g d) (ptQ w s y σ) := by
    intro w s y σ hw hs hg hσ P hP
    obtain ⟨t, -, hst⟩ := exists_inv_pos hs
    have hts : t * s = 1 := by rw [mul_comm]; exact hst
    have h1 := (presList_spec G g d (toQZ P)).2 (Ideal.subset_span (List.mem_map_of_mem hP))
    -- the substituted polynomial lies in `(H₀)`, so an integer multiple lies in `(H₀Z)`
    have h2 : toQZ (aeval (fvecZ g d) P) ∈ lspan ((H₀Z G g d).map toQZ) := by
      rw [toQZ_aeval]; exact h1
    obtain ⟨D, hD, hDmem⟩ := int_mem (H₀Z G g d) _ h2
    have h3 := evalR_eq_zero_of_mem (evalR_H₀Z G g d w hw t s y σ hts hg hσ) hDmem
    have h4 : evalR (ptB w t s σ) ((D : MvPolynomial _ ℤ) * aeval (fvecZ g d) P) =
        (D : ℝ) * evalR (ptQ w s y σ) P := by
      rw [show evalR (ptB w t s σ) ((D : MvPolynomial _ ℤ) * aeval (fvecZ g d) P) =
        (D : ℝ) * evalR (ptB w t s σ) (aeval (fvecZ g d) P) by simp [evalR], evalR_aeval]
      rw [show (fun j => evalR (ptB w t s σ) (fvecZ g d j)) = ptQ w s y σ from
        funext fun j => evalR_fvecZ g d w t s y σ hts hg j]
    rw [h4] at h3
    obtain ⟨u, -, hu⟩ := exists_inv_pos (Nat.cast_pos.2 hD : (0 : ℝ) < D)
    calc evalR (ptQ w s y σ) P = (D * u) * evalR (ptQ w s y σ) P := by rw [hu, one_mul]
      _ = u * ((D : ℝ) * evalR (ptQ w s y σ) P) := by ring
      _ = 0 := by rw [h3, mul_zero]
  exact {
    Pt := PtG G
    Pt' := PtG (presList G g d)
    g := fun i w => evalR w (g i)
    d := d
    E := E
    D₂ := D₂
    hD := hD
    hEd := hEd
    hE := hE
    Q := ptQ
    π := fun x k => x (Fin.castAdd _ k)
    lift_mem := fun w s y σ hw hs hg hσ => ⟨hlift w s y σ hw hs hg hσ,
      funext fun k => ptQ_left w s y σ k⟩
    g_bdd := fun C => (uniform_bdd_lip g C).1
    g_lip := fun C => (uniform_bdd_lip g C).2
    Q_bdd := fun C S => ⟨|C| + |S| + 1, fun w s y σ hw hs hy hσ j => by
      refine ptQ_cases (fun v => |v| ≤ |C| + |S| + 1) w s y σ (fun k => ?_) ?_ (fun i => ?_)
        (fun i => ?_) j
      · have := (hw k).trans (le_abs_self C); linarith [abs_nonneg S]
      · have := hs.trans (le_abs_self S); linarith [abs_nonneg C]
      · linarith [hy i, abs_nonneg C, abs_nonneg S]
      · linarith [hσ i, abs_nonneg C, abs_nonneg S]⟩
    Q_lip := fun C S => ⟨1, zero_le_one, fun w w' s s' y y' σ σ' δ _ _ _ _ _ _ _ _ hw hs hy hσ j => by
      rw [one_mul]
      exact ptQ_cases₂ (fun v v' => |v - v'| ≤ δ) w w' s s' y σ y' σ' hw hs hy hσ j⟩ }

theorem offStepOf_spec {D₂ : ℕ} (hD : D₂ ≠ 0) (E : Fin r → ℕ) (hEd : ∀ i, E i * d i = D₂)
    (hE : ∀ i, Even (E i)) :
    (offStepOf G g d hD E hEd hE).Pt = PtG G ∧ (offStepOf G g d hD E hEd hE).Pt' = PtG (presList G g d) ∧
      (offStepOf G g d hD E hEd hE).g = (fun i w => evalR w (g i)) ∧
      (offStepOf G g d hD E hEd hE).d = d ∧ (offStepOf G g d hD E hEd hE).E = E ∧
      (offStepOf G g d hD E hEd hE).π = (fun x k => x (Fin.castAdd _ k)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Pres

end BezoutCounterexample.Constructive
