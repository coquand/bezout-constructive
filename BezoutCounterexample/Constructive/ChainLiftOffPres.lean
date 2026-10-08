import Mathlib
import BezoutCounterexample.Constructive.ChainLiftOff
import BezoutCounterexample.Constructive.ChainLiftSquare
import BezoutCounterexample.Constructive.Kernel
import BezoutCounterexample.Constructive.PresentedOps

/-!
# The torsor presentation and its `OffStep` (bridge (f), certificate level)

Base `B = ℚ[Y] ⧸ (G)` (`G` integer relations in `N` variables), filtration generators
`gᵢ ∈ ℤ[Y]` of degrees `dᵢ`. The torsor `B' = J(gᵢ T^{dᵢ})` over the Rees algebra embeds in
`J_{B[T^±]}(gᵢ T^{dᵢ}) = ℚ[Y, T, W, σ] ⧸ (H₀)`, `H₀ = (G, T W - 1, Σ σᵢ gᵢ T^{dᵢ} - 1)`. Its
coordinates are `(Y, s, y, σ)` with `s ↦ W = T⁻¹`, `yᵢ ↦ gᵢ T^{dᵢ}`. The relations `G'` are the
kernel of `ℚ[Y, s, y, σ] → ℚ[Y, T, W, σ] ⧸ (H₀)`, by elimination (`exists_ker_list`), cleared to
`ℤ`.

`exists_offStep`: the `OffStep` with `Q (w, s, y, σ) = (w, s, y, σ)` and `π` the projection.
`lift_mem` is evaluation: `(w, T ↦ 1/s, W ↦ s, σ)` kills `H₀` when `gᵢ(w) = sᵈⁱ yᵢ` and
`Σ yᵢ σᵢ = 1`, and the composite with the substitution is evaluation at `(w, s, y, σ)`.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

open MvPolynomial

/-! ## Integer and rational polynomials -/

section IntQ

variable {σ : Type*}

/-- `ℤ[Y] → ℚ[Y]`. -/
noncomputable abbrev toQZ : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)

/-- **Clearing denominators** of one rational polynomial. -/
theorem int_clear (p : MvPolynomial σ ℚ) :
    ∃ (D : ℕ) (q : MvPolynomial σ ℤ), 0 < D ∧ toQZ q = (D : MvPolynomial σ ℚ) * p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, C a.num, a.den_pos, ?_⟩
    rw [map_C, ← map_natCast C, ← C_mul]
    congr 1
    simp only [eq_intCast, Int.cast_natCast]
    rw [mul_comm, Rat.mul_den_eq_num]
  | add p q hp hq =>
    obtain ⟨D, a, hD, ha⟩ := hp
    obtain ⟨D', b, hD', hb⟩ := hq
    refine ⟨D * D', C (D' : ℤ) * a + C (D : ℤ) * b, Nat.mul_pos hD hD', ?_⟩
    rw [map_add, map_mul, map_mul, ha, hb, map_C, map_C]
    simp only [eq_intCast, Int.cast_natCast, ← map_natCast C]
    push_cast
    simp only [map_mul, map_natCast]
    ring
  | mul_X p i hp =>
    obtain ⟨D, a, hD, ha⟩ := hp
    exact ⟨D, a * X i, hD, by rw [map_mul, ha, map_X, mul_assoc]⟩

end IntQ

/-- Members of an extended ideal have integer multiples in the integer ideal. -/
theorem int_mem {σ : Type*} (L : List (MvPolynomial σ ℤ)) (Z : MvPolynomial σ ℤ)
    (h : toQZ Z ∈ lspan (L.map toQZ)) : ∃ D : ℕ, 0 < D ∧ (D : MvPolynomial σ ℤ) * Z ∈ lspan L := by
  have hspan : lspan (L.map toQZ) =
      Ideal.span (Set.range fun j : Fin L.length => toQZ (L.get j)) := by
    show Ideal.span _ = Ideal.span _
    congr 1
    ext x
    simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨j, rfl⟩ := List.get_of_mem ha
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, List.get_mem L j, rfl⟩
  rw [hspan, Ideal.mem_span_range_iff_exists_fun] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨cq, hcq⟩ := fin_choice (α := ℕ × MvPolynomial σ ℤ)
    (P := fun j c => 0 < c.1 ∧ toQZ c.2 = (c.1 : MvPolynomial σ ℚ) * a j) fun j => by
      obtain ⟨D, q, hD, hq⟩ := int_clear (a j)
      exact ⟨(D, q), hD, hq⟩
  -- the product of the denominators
  set D : ℕ := ∏ j, (cq j).1
  have hD : 0 < D := Finset.prod_pos fun j _ => (hcq j).1
  have hDj : ∀ j, ∃ E : ℕ, D = E * (cq j).1 := fun j =>
    ⟨∏ j' ∈ Finset.univ.erase j, (cq j').1, (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm⟩
  obtain ⟨E, hE⟩ := fin_choice (α := ℕ) (P := fun j E => D = E * (cq j).1) hDj
  refine ⟨D, hD, ?_⟩
  have : (D : MvPolynomial σ ℤ) * Z = ∑ j, (E j : MvPolynomial σ ℤ) * (cq j).2 * L.get j := by
    apply MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ))
    show toQZ _ = toQZ _
    rw [map_mul, map_natCast, ← ha, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, map_natCast, (hcq j).2, hE j, Nat.cast_mul]
    ring
  rw [this]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (List.get_mem L j))

/-- `map` commutes with substitution. -/
lemma toQZ_aeval {σ τ : Type*} (f : σ → MvPolynomial τ ℤ) (P : MvPolynomial σ ℤ) :
    toQZ (aeval f P) = aeval (fun j => toQZ (f j)) (toQZ P) := by
  have : (toQZ : MvPolynomial τ ℤ →+* _).comp (aeval f).toRingHom =
      (aeval (R := ℚ) fun j => toQZ (f j)).toRingHom.comp toQZ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C,
        algebraMap_eq, map_C]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, map_X]
  exact congrArg (fun φ : MvPolynomial σ ℤ →+* _ => φ P) this

/-- Real evaluation commutes with substitution. -/
lemma evalR_aeval {M N : ℕ} (x : Fin M → ℝ) (f : Fin N → MvPolynomial (Fin M) ℤ)
    (P : MvPolynomial (Fin N) ℤ) : evalR x (aeval f P) = evalR (fun j => evalR x (f j)) P := by
  have : (eval₂Hom (Int.castRingHom ℝ) x).comp (aeval f).toRingHom =
      eval₂Hom (Int.castRingHom ℝ) (fun j => evalR x (f j)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C,
        algebraMap_eq, coe_eval₂Hom, eval₂_C]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
        coe_eval₂Hom, eval₂_X]; rfl
  exact congrArg (fun φ : MvPolynomial (Fin N) ℤ →+* ℝ => φ P) this

/-! ## The presentation -/

section Pres

variable {N r : ℕ}

/-- Variables of `ℤ[Y, T, W, σ]`. -/
def tpY (k : Fin N) : Fin (N + (2 + r)) := Fin.castAdd _ k
def tpT : Fin (N + (2 + r)) := Fin.natAdd N (Fin.castAdd r 0)
def tpW : Fin (N + (2 + r)) := Fin.natAdd N (Fin.castAdd r 1)
def tpσ (i : Fin r) : Fin (N + (2 + r)) := Fin.natAdd N (Fin.natAdd 2 i)

/-- `ℤ[Y] → ℤ[Y, T, W, σ]`. -/
noncomputable abbrev embYZ : MvPolynomial (Fin N) ℤ →ₐ[ℤ] MvPolynomial (Fin (N + (2 + r))) ℤ :=
  rename tpY

variable (G : List (MvPolynomial (Fin N) ℤ)) (g : Fin r → MvPolynomial (Fin N) ℤ) (d : Fin r → ℕ)

/-- The relations of `J_{B[T^±]}(gᵢ T^{dᵢ})`, over `ℤ`. -/
noncomputable def H₀Z : List (MvPolynomial (Fin (N + (2 + r))) ℤ) :=
  G.map embYZ ++ [X tpT * X tpW - 1, ∑ i, X (tpσ i) * embYZ (g i) * X tpT ^ d i - 1]

/-- The same relations over `ℚ`. -/
noncomputable def H₀ : List (MvPolynomial (Fin (N + (2 + r))) ℚ) := (H₀Z G g d).map toQZ

/-- The substitution `Y ↦ Y`, `s ↦ W`, `yᵢ ↦ gᵢ T^{dᵢ}`, `σ ↦ σ`, over `ℤ`. -/
noncomputable def fvecZ : Fin (N + (1 + (r + r))) → MvPolynomial (Fin (N + (2 + r))) ℤ :=
  Fin.append (fun k => X (tpY k)) (Fin.append (fun _ : Fin 1 => X tpW)
    (Fin.append (fun i => embYZ (g i) * X tpT ^ d i) (fun i => X (tpσ i))))

/-- The same substitution over `ℚ`. -/
noncomputable def fvec : Fin (N + (1 + (r + r))) → MvPolynomial (Fin (N + (2 + r))) ℚ :=
  fun j => toQZ (fvecZ g d j)

/-- The point `(w, s, y, σ)`. -/
def ptQ (w : Fin N → ℝ) (s : ℝ) (y σ : Fin r → ℝ) : Fin (N + (1 + (r + r))) → ℝ :=
  Fin.append w (Fin.append (fun _ : Fin 1 => s) (Fin.append y σ))

/-- The point `(w, 1/s, s, σ)` of `ℤ[Y, T, W, σ]`. -/
def ptB (w : Fin N → ℝ) (t s : ℝ) (σ : Fin r → ℝ) : Fin (N + (2 + r)) → ℝ :=
  Fin.append w (Fin.append (fun j : Fin 2 => if j = 0 then t else s) σ)

lemma ptB_iY (w : Fin N → ℝ) (t s : ℝ) (σ : Fin r → ℝ) (k : Fin N) :
    ptB w t s σ (tpY k) = w k := by simp [ptB, tpY]
lemma ptB_iT (w : Fin N → ℝ) (t s : ℝ) (σ : Fin r → ℝ) : ptB (r := r) w t s σ tpT = t := by
  simp [ptB, tpT]
lemma ptB_iW (w : Fin N → ℝ) (t s : ℝ) (σ : Fin r → ℝ) : ptB (r := r) w t s σ tpW = s := by
  simp [ptB, tpW]
lemma ptB_iσ (w : Fin N → ℝ) (t s : ℝ) (σ : Fin r → ℝ) (i : Fin r) :
    ptB w t s σ (tpσ i) = σ i := by simp [ptB, tpσ]

lemma evalR_embYZ (w : Fin N → ℝ) (t s : ℝ) (σ : Fin r → ℝ) (p : MvPolynomial (Fin N) ℤ) :
    evalR (ptB w t s σ) (embYZ (r := r) p) = evalR w p := by
  have : ptB w t s σ ∘ tpY = w := funext fun k => ptB_iY w t s σ k
  show eval₂ (Int.castRingHom ℝ) (ptB w t s σ) (rename tpY p) = eval₂ (Int.castRingHom ℝ) w p
  rw [eval₂_rename, this]

/-- **The substituted point is the evaluation point.** -/
lemma evalR_fvecZ (w : Fin N → ℝ) (t s : ℝ) (y σ : Fin r → ℝ) (hts : t * s = 1)
    (hg : ∀ i, evalR w (g i) = s ^ d i * y i) (j : Fin (N + (1 + (r + r)))) :
    evalR (ptB w t s σ) (fvecZ g d j) = ptQ w s y σ j := by
  refine Fin.addCases (fun k => ?_) (fun j => ?_) j
  · simp only [fvecZ, ptQ, Fin.append_left, evalR_X, ptB_iY]
  refine Fin.addCases (fun _ => ?_) (fun j => ?_) j
  · simp only [fvecZ, ptQ, Fin.append_left, Fin.append_right, evalR_X, ptB_iW]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [fvecZ, ptQ, Fin.append_right, Fin.append_left]
    have h1 : evalR (ptB w t s σ) (embYZ (g i) * X tpT ^ d i) =
        evalR w (g i) * t ^ d i := by
      show eval₂ (Int.castRingHom ℝ) (ptB w t s σ) (embYZ (g i) * X tpT ^ d i) = _
      rw [eval₂_mul, eval₂_pow, eval₂_X]
      change evalR (ptB w t s σ) (embYZ (g i)) * ptB w t s σ tpT ^ d i = _
      rw [evalR_embYZ, ptB_iT]
    rw [h1, hg i]
    calc s ^ d i * y i * t ^ d i = (t * s) ^ d i * y i := by ring
      _ = y i := by rw [hts, one_pow, one_mul]
  · simp only [fvecZ, ptQ, Fin.append_right, evalR_X, ptB_iσ]

/-- **The relations `H₀` vanish at `(w, 1/s, s, σ)`.** -/
lemma evalR_H₀Z (w : Fin N → ℝ) (hw : PtG G w) (t s : ℝ) (y σ : Fin r → ℝ) (hts : t * s = 1)
    (hg : ∀ i, evalR w (g i) = s ^ d i * y i) (hσ : ∑ i, y i * σ i = 1) :
    PtG (H₀Z G g d) (ptB w t s σ) := by
  intro h hh
  simp only [H₀Z, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with ⟨P, hP, rfl⟩ | rfl | rfl
  · rw [evalR_embYZ]; exact hw P hP
  · simp only [evalR, eval₂_sub, eval₂_mul, eval₂_X, eval₂_one, ptB_iT, ptB_iW, hts, sub_self]
  · simp only [evalR, eval₂_sub, eval₂_sum, eval₂_mul, eval₂_pow, eval₂_X, eval₂_one, ptB_iσ,
      ptB_iT]
    rw [sub_eq_zero, ← hσ]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := evalR_embYZ w t s σ (g i)
    have h2 := hg i
    simp only [evalR] at h1 h2
    rw [h1, h2]
    calc σ i * (s ^ d i * y i) * t ^ d i = (t * s) ^ d i * (y i * σ i) := by ring
      _ = y i * σ i := by rw [hts, one_pow, one_mul]

/-- The point of the torsor over `(w, s, y, σ)` projects to `w`. -/
lemma ptQ_left (w : Fin N → ℝ) (s : ℝ) (y σ : Fin r → ℝ) (k : Fin N) :
    ptQ w s y σ (Fin.castAdd _ k) = w k := by simp [ptQ]

/-- Coordinates of `ptQ`, by cases. -/
lemma ptQ_cases (P : ℝ → Prop) (w : Fin N → ℝ) (s : ℝ) (y σ : Fin r → ℝ) (hw : ∀ k, P (w k))
    (hs : P s) (hy : ∀ i, P (y i)) (hσ : ∀ i, P (σ i)) (j : Fin (N + (1 + (r + r)))) :
    P (ptQ w s y σ j) := by
  refine Fin.addCases (fun k => ?_) (fun j => ?_) j
  · simpa [ptQ] using hw k
  refine Fin.addCases (fun _ => ?_) (fun j => ?_) j
  · simpa [ptQ] using hs
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [ptQ, Fin.append_right, Fin.append_left]; exact hy i
  · simp only [ptQ, Fin.append_right]; exact hσ i

/-- Coordinates of two points `ptQ`, by cases. -/
lemma ptQ_cases₂ (P : ℝ → ℝ → Prop) (w w' : Fin N → ℝ) (s s' : ℝ) (y σ y' σ' : Fin r → ℝ)
    (hw : ∀ k, P (w k) (w' k)) (hs : P s s') (hy : ∀ i, P (y i) (y' i)) (hσ : ∀ i, P (σ i) (σ' i))
    (j : Fin (N + (1 + (r + r)))) : P (ptQ w s y σ j) (ptQ w' s' y' σ' j) := by
  refine Fin.addCases (fun k => ?_) (fun j => ?_) j
  · simpa [ptQ] using hw k
  refine Fin.addCases (fun _ => ?_) (fun j => ?_) j
  · simpa [ptQ] using hs
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [ptQ, Fin.append_right, Fin.append_left]; exact hy i
  · simp only [ptQ, Fin.append_right]; exact hσ i

/-- Uniform bounds and Lipschitz constants for finitely many integer polynomials. -/
lemma uniform_bdd_lip (g : Fin r → MvPolynomial (Fin N) ℤ) (C : ℝ) :
    (∃ M, 0 ≤ M ∧ ∀ i w, Bdd C w → |evalR w (g i)| ≤ M) ∧
      ∃ L, 0 ≤ L ∧ ∀ i, LipR C L (fun w => evalR w (g i)) := by
  have hC : 0 ≤ |C| := abs_nonneg C
  have hb : ∀ w : Fin N → ℝ, Bdd C w → Bdd |C| w := fun w hw k => (hw k).trans (le_abs_self C)
  constructor
  · obtain ⟨M, hM, hMb⟩ := exists_uniform (fun i M => ∀ w, Bdd |C| w → |evalR w (g i)| ≤ M)
      (fun i M M' h hMM' w hw => (h w hw).trans hMM')
      (fun i => by
        obtain ⟨M, -, hM, -, hb, -⟩ := poly_bdd_lip |C| hC (g i)
        exact ⟨M, hM, hb⟩) Finset.univ
    exact ⟨M, hM, fun i w hw => hMb i (Finset.mem_univ i) w (hb w hw)⟩
  · rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      refine ⟨0, le_rfl, fun i w w' δ _ _ _ => ?_⟩
      have : w = w' := funext fun k => k.elim0
      rw [this, sub_self, abs_zero, zero_mul]
    · obtain ⟨L, hL, hLb⟩ := exists_uniform (fun i L => LipR |C| L (fun w => evalR w (g i)))
        (fun i L L' h hLL' w w' δ hw hw' hc => (h w w' δ hw hw' hc).trans
          (mul_le_mul_of_nonneg_right hLL' ((abs_nonneg _).trans (hc ⟨0, hN⟩))))
        (fun i => by
          obtain ⟨-, L, -, hL, -, hl⟩ := poly_bdd_lip |C| hC (g i)
          exact ⟨L, hL, hl⟩) Finset.univ
      exact ⟨L, hL, fun i w w' δ hw hw' hc =>
        hLb i (Finset.mem_univ i) w w' δ (hb w hw) (hb w' hw') hc⟩

/-- **The torsor presentation and its `OffStep`.** `G'` presents the subring of
`ℚ[Y, T, W, σ] ⧸ (H₀)` generated by `Y, W, gᵢ T^{dᵢ}, σ` (last conjunct). -/
theorem exists_offStep {D₂ : ℕ} (hD : D₂ ≠ 0) (E : Fin r → ℕ) (hEd : ∀ i, E i * d i = D₂)
    (hE : ∀ i, Even (E i)) :
    ∃ (G' : List (MvPolynomial (Fin (N + (1 + (r + r)))) ℤ))
      (O : OffStep N (N + (1 + (r + r))) (Fin r)),
      O.Pt = PtG G ∧ O.Pt' = PtG G' ∧ O.g = (fun i w => evalR w (g i)) ∧ O.d = d ∧ O.E = E ∧
      O.π = (fun x k => x (Fin.castAdd _ k)) ∧ ∀ h : MvPolynomial (Fin (N + (1 + (r + r)))) ℚ,
        aeval (fvec g d) h ∈ lspan (H₀ G g d) ↔ h ∈ lspan (G'.map toQZ) := by
  obtain ⟨L, hL⟩ := exists_ker_list (H₀ G g d) (fvec g d)
  obtain ⟨cq, hcq⟩ := fin_choice (α := ℕ × MvPolynomial (Fin (N + (1 + (r + r)))) ℤ)
    (P := fun j a => 0 < a.1 ∧ toQZ a.2 = (a.1 : MvPolynomial _ ℚ) * L.get j) fun j => by
      obtain ⟨D, q, hD, hq⟩ := int_clear (L.get j)
      exact ⟨(D, q), hD, hq⟩
  set G' : List (MvPolynomial (Fin (N + (1 + (r + r)))) ℤ) := List.ofFn fun j => (cq j).2
  have hspan : lspan (G'.map toQZ) = lspan L := by
    apply le_antisymm
    · rw [lspan, Ideal.span_le]
      intro p hp
      simp only [G', List.map_ofFn, Set.mem_setOf_eq, List.mem_ofFn, Function.comp_apply] at hp
      obtain ⟨j, rfl⟩ := hp
      rw [(hcq j).2]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (List.get_mem L j))
    · rw [lspan, Ideal.span_le]
      intro p hp
      obtain ⟨j, rfl⟩ := List.get_of_mem hp
      have hD : ((cq j).1 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (hcq j).1.ne'
      have hmem : toQZ (cq j).2 ∈ lspan (G'.map toQZ) :=
        Ideal.subset_span (List.mem_map.2 ⟨_, List.mem_ofFn.2 ⟨j, rfl⟩, rfl⟩)
      have : L.get j = C ((cq j).1 : ℚ)⁻¹ * toQZ (cq j).2 := by
        rw [(hcq j).2, ← mul_assoc, ← map_natCast C, ← C_mul, inv_mul_cancel₀ hD, C_1, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ hmem
  -- the lift
  have hlift : ∀ w s y σ, PtG G w → 0 < s → (∀ i, evalR w (g i) = s ^ d i * y i) →
      ∑ i, y i * σ i = 1 → PtG G' (ptQ w s y σ) := by
    intro w s y σ hw hs hg hσ P hP
    obtain ⟨t, -, hst⟩ := exists_inv_pos hs
    have hts : t * s = 1 := by rw [mul_comm]; exact hst
    have hPL : toQZ P ∈ lspan L := hspan ▸ Ideal.subset_span (List.mem_map_of_mem hP)
    have h1 := (hL _).2 hPL
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
  refine ⟨G', {
    Pt := PtG G
    Pt' := PtG G'
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
      exact ptQ_cases₂ (fun v v' => |v - v'| ≤ δ) w w' s s' y σ y' σ' hw hs hy hσ j⟩ },
    rfl, rfl, rfl, rfl, rfl, rfl, fun h => by rw [hL, hspan]⟩

end Pres

end BezoutCounterexample.Constructive
