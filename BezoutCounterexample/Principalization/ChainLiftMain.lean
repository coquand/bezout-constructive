import Mathlib
import BezoutCounterexample.MainTheorem
import BezoutCounterexample.Principalization.ChainLiftConstruction
import BezoutCounterexample.Constructive.ChainLiftMoebius
import BezoutCounterexample.Constructive.ChainLiftChoice

/-!
# Theorem 1.1 by chain lifting (`main_theorem_tower`)

Lemma 5.3 for `TowerConstruction.R`, proved by chain lifting instead of the nonorientability of
the line bundle (5.2): the five elements `p, q, u, v, μ` descend to a stage `A_N`, they are
represented by polynomials over the presentation `G_N` (with integer numerators), and evaluation
at the real points of `G_N` gives functions satisfying the Möbius relation over the plane
coordinates `w ∘ σ_N`. The tower of `A_N` lifts chains from the plane (`TowerLift.chainLift`), so
`no_moebius_lift` gives a contradiction.
-/

noncomputable section

namespace BezoutCounterexample

open Principalization Constructive MvPolynomial Matrix TowerConstruction

/-- Evaluation of a rational polynomial at a real point. -/
abbrev evQ {N : ℕ} (w : Fin N → ℝ) : MvPolynomial (Fin N) ℚ →+* ℝ := (aeval w).toRingHom

lemma evQ_toQ {N : ℕ} (w : Fin N → ℝ) (Q : MvPolynomial (Fin N) ℤ) : evQ w (toQ Q) = evalR w Q := by
  have : (evQ w).comp toQ = eval₂Hom (Int.castRingHom ℝ) w :=
    MvPolynomial.ringHom_ext (fun a => by simp) (fun i => by simp)
  exact RingHom.congr_fun this Q

/-- At a real point of `G`, evaluation kills `(G)`. -/
lemma evQ_lspan {N : ℕ} {G : List (MvPolynomial (Fin N) ℤ)} {w : Fin N → ℝ} (hw : PtG G w)
    {P : MvPolynomial (Fin N) ℚ} (hP : P ∈ lspan (G.map toQ)) : evQ w P = 0 := by
  have : lspan (G.map toQ) ≤ RingHom.ker (evQ w) := by
    rw [lspan, Ideal.span_le]
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    rw [SetLike.mem_coe, RingHom.mem_ker, evQ_toQ]
    exact hw g' hg'
  exact this hP

/-- Polynomial functions with rational coefficients are bounded and Lipschitz on boxes. -/
lemma ratPoly_bdd_lip {N : ℕ} (P : MvPolynomial (Fin N) ℚ) (C : ℝ) :
    ∃ M L, 0 ≤ L ∧ (∀ w, Bdd C w → |evQ w P| ≤ M) ∧ LipR C L (fun w => evQ w P) := by
  obtain ⟨D, Q, hD, hQ⟩ := exists_int_mul P
  obtain ⟨M, L, hM, hL, hb, hl⟩ := poly_bdd_lip |C| (abs_nonneg C) Q
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  -- `D · P = Q`: no division in `ℝ`; `1 ≤ D` gives `|x| ≤ |D x|`
  have hval : ∀ w, (D : ℝ) * evQ w P = evalR w Q := fun w => by
    have := congrArg (evQ w) hQ
    rw [evQ_toQ, map_mul, map_natCast] at this
    exact this.symm
  have hle : ∀ x : ℝ, |x| ≤ |(D : ℝ) * x| := fun x => by
    rw [abs_mul, abs_of_nonneg (zero_le_one.trans hD1)]
    exact le_mul_of_one_le_left (abs_nonneg x) hD1
  have hbox : ∀ w : Fin N → ℝ, Bdd C w → Bdd |C| w := fun w h k => (h k).trans (le_abs_self C)
  refine ⟨M, L, hL, fun w hw => ?_, fun w w' δ hw hw' h => ?_⟩
  · exact (hle _).trans (by rw [hval]; exact hb w (hbox w hw))
  · show |evQ w P - evQ w' P| ≤ L * δ
    refine (hle _).trans ?_
    rw [mul_sub, hval, hval]
    exact hl w w' δ (hbox w hw) (hbox w' hw') h

lemma ptG_nil : PtG ([] : List (MvPolynomial (Fin 2) ℤ)) = fun _ => True :=
  funext fun _ => propext ⟨fun _ => trivial, fun _ g hg => absurd hg List.not_mem_nil⟩

/-- **Lemma 5.3 for `TowerConstruction.R`, by chain lifting.** -/
theorem key_obstruction_tower :
    ¬ ∃ p q u v μ : TowerConstruction.R,
      μ * (![p, q] ᵥ* (M.map TowerConstruction.R.ι) ⬝ᵥ ![u, v]) = 1 := by
  rintro ⟨p, q, u, v, μ, hrel⟩
  obtain ⟨N, w, hw⟩ := TowerConstruction.R.exists_of_fin 5 ![p, q, u, v, μ]
  have hrelN : w 4 * (![w 0, w 1] ᵥ* (M.map (TowerConstruction.ι N)) ⬝ᵥ ![w 2, w 3]) = 1 := by
    apply TowerConstruction.R.of_injective N
    have e : ∀ t, TowerConstruction.R.of N (w t) = ![p, q, u, v, μ] t := hw
    simp only [vecMul_M_dotProduct, map_mul, map_add, map_sub, map_one,
      TowerConstruction.R.of_ι, e] at hrel ⊢
    simpa using hrel
  rw [vecMul_M_dotProduct] at hrelN
  set S := stage N
  -- polynomial representatives over the presentation
  have hsurj : ∀ a : A N, ∃ P : MvPolynomial (Fin S.N) ℚ, S.eq (Ideal.Quotient.mk _ P) = a :=
    fun a => by
      obtain ⟨P, hP⟩ := Ideal.Quotient.mk_surjective (S.eq.symm a)
      exact ⟨P, by rw [hP, RingEquiv.apply_symm_apply]⟩
  obtain ⟨P, hP⟩ := finite_choice_dep fun t : Fin 5 => hsurj (w t)
  have hx : S.eq (Ideal.Quotient.mk _ (X (S.σ 0))) = TowerConstruction.ι N x := by
    rw [S.compat, base_eq]; rfl
  have hy : S.eq (Ideal.Quotient.mk _ (X (S.σ 1))) = TowerConstruction.ι N y := by
    rw [S.compat, base_eq]; rfl
  -- the relation, as a polynomial in `(G_N)`
  set E : MvPolynomial (Fin S.N) ℚ := P 4 * ((P 0 * (1 + X (S.σ 0)) + P 1 * X (S.σ 1)) * P 2 +
    (P 0 * X (S.σ 1) + P 1 * (1 - X (S.σ 0))) * P 3) - 1
  have hE : E ∈ lspan (S.G.map toQ) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← S.eq.map_eq_zero_iff]
    simp only [E, map_sub, map_mul, map_add, map_one, hP, hx, hy]
    rw [hrelN, sub_self]
  -- the functions
  set f : Fin 5 → (Fin S.N → ℝ) → ℝ := fun t z => evQ z (P t)
  refine no_moebius_lift (PtG S.G) (fun z => z ∘ S.σ) ?_ (f 0) (f 1) (f 2) (f 3) (f 4)
    (fun z hz => ?_) (fun C => ?_) (fun C => ?_)
  · have := (TowerLift.chainLift S.tower).1
    rwa [ptG_nil] at this
  · have h0 := evQ_lspan hz hE
    simp only [E, map_sub, map_mul, map_add, map_one] at h0
    simp only [f, Function.comp_apply]
    have e0 : evQ z (X (S.σ 0)) = z (S.σ 0) := by simp
    have e1 : evQ z (X (S.σ 1)) = z (S.σ 1) := by simp
    rw [e0, e1] at h0
    linear_combination h0
  · obtain ⟨Mb, hMb⟩ := finite_choice_dep fun t : Fin 5 => ratPoly_bdd_lip (P t) C
    refine ⟨∑ t, |Mb t|, fun z _ hzC => ?_⟩
    have hle : ∀ t, |f t z| ≤ ∑ t, |Mb t| := fun t => by
      obtain ⟨_, _, hb, _⟩ := hMb t
      exact ((hb z hzC).trans (le_abs_self _)).trans
        (Finset.single_le_sum (fun i _ => abs_nonneg (Mb i)) (Finset.mem_univ t))
    exact ⟨hle 0, hle 1, hle 4, hle 2, hle 3⟩
  · obtain ⟨_, L2, hL2, -, hl2⟩ := ratPoly_bdd_lip (P 2) C
    obtain ⟨_, L3, hL3, -, hl3⟩ := ratPoly_bdd_lip (P 3) C
    refine ⟨L2 + L3, add_nonneg hL2 hL3, fun z z' δ hz hz' h => ?_, fun z z' δ hz hz' h => ?_⟩
    · have h3 : 0 ≤ L3 * δ := (abs_nonneg _).trans (hl3 z z' δ hz hz' h)
      exact (hl2 z z' δ hz hz' h).trans (by linarith)
    · have h2 : 0 ≤ L2 * δ := (abs_nonneg _).trans (hl2 z z' δ hz hz' h)
      exact (hl3 z z' δ hz hz' h).trans (by linarith)

/-- **The forward direction of `isSmithNormalForm_iff_chain`**, given a zero test (C9): the only
direction used, without `Nat.find` or `Classical.propDecidable`. -/
lemma isSmithNormalForm_chain {S : Type*} [CommRing S] (hz : ∀ x : S, x = 0 ∨ x ≠ 0) {m n : ℕ}
    {D : Matrix (Fin m) (Fin n) S} (h : IsSmithNormalForm D) :
    ∃ d : ℕ → S, (∀ i j, D i j = if (i : ℕ) = j then d i else 0) ∧
      ∀ k, k + 1 < min m n → d k ∣ d (k + 1) := by
  obtain ⟨d, r, -, hD, hnz, hdiv⟩ := h
  refine ⟨d, hD, fun k hk => ?_⟩
  rcases Nat.lt_or_ge (k + 1) r with hkr | hkr
  · exact hdiv k hkr
  · rcases hz (d (k + 1)) with h0 | h0
    · rw [h0]; exact dvd_zero _
    · exact absurd ((hnz (k + 1) hk).1 h0) (Nat.not_lt.2 hkr)

/-- **Zero test in `R`**: an element comes from a stage, where the zero test decides, and the maps
to `R` are injective. -/
lemma TowerConstruction.R.zeroTest (x : TowerConstruction.R) : x = 0 ∨ x ≠ 0 := by
  obtain ⟨n, a, rfl⟩ := TowerConstruction.R.exists_of x
  rcases (TowerConstruction.A n).zeroTest a with h | h
  · exact Or.inl (by rw [h, map_zero])
  · exact Or.inr fun h0 => h (TowerConstruction.R.of_injective n (by rw [h0, map_zero]))

/-- `M` has no Smith normal form over `TowerConstruction.R` (as in `not_hasSmithNormalForm`). -/
theorem span_entries_M_map_tower :
    (Ideal.span {TowerConstruction.R.ι (1 + x), TowerConstruction.R.ι y,
      TowerConstruction.R.ι (1 - x)} : Ideal TowerConstruction.R) = ⊤ := by
  have h := congrArg (Ideal.map TowerConstruction.R.ι) span_entries_M
  rwa [Ideal.map_span, Ideal.map_top, Set.image_insert_eq, Set.image_pair] at h

theorem not_hasSmithNormalForm_tower : ¬ HasSmithNormalForm (M.map TowerConstruction.R.ι) := by
  rintro ⟨G, hMG, hG⟩
  obtain ⟨d, hd, hdiv⟩ := isSmithNormalForm_chain TowerConstruction.R.zeroTest hG
  have hd12 : d 0 ∣ d 1 := hdiv 0 (by norm_num)
  have htop : (Ideal.span {d 0, d 1} : Ideal TowerConstruction.R) = ⊤ := by
    have hGmem : ∀ i j, G i j ∈ (Ideal.span {d 0, d 1} : Ideal TowerConstruction.R) := by
      intro i j
      fin_cases i <;> fin_cases j
      · rw [hd]; exact Ideal.subset_span (by simp)
      · rw [hd]; simp
      · rw [hd]; simp
      · rw [hd]; exact Ideal.subset_span (by simp)
    have hM := hMG.entry_mem _ hGmem
    rw [eq_top_iff, ← span_entries_M_map_tower, Ideal.span_le]
    rintro r (rfl | rfl | rfl)
    · simpa [M] using hM 0 0
    · simpa [M] using hM 0 1
    · simpa [M] using hM 1 1
  have hunit : IsUnit (d 0) := by
    have h : (Ideal.span {d 0, d 1} : Ideal TowerConstruction.R) = Ideal.span {d 0} := by
      rw [Ideal.span_insert, sup_eq_left.2 (Ideal.span_singleton_le_span_singleton.2 hd12)]
    rwa [h, Ideal.span_singleton_eq_top] at htop
  obtain ⟨P, Q, hPQ⟩ := hMG
  have h00 : ![(P : Matrix (Fin 2) (Fin 2) TowerConstruction.R) 0 0,
      (P : Matrix (Fin 2) (Fin 2) TowerConstruction.R) 0 1] ᵥ*
      (M.map TowerConstruction.R.ι) ⬝ᵥ ![(Q : Matrix (Fin 2) (Fin 2) TowerConstruction.R) 0 0,
        (Q : Matrix (Fin 2) (Fin 2) TowerConstruction.R) 1 0] = d 0 := by
    have h : ((P : Matrix (Fin 2) (Fin 2) TowerConstruction.R) * M.map TowerConstruction.R.ι *
        Q) 0 0 = d 0 := by
      rw [hPQ, hd]; simp
    rw [← h]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  obtain ⟨μ, hμ⟩ := hunit.exists_left_inv
  exact key_obstruction_tower ⟨_, _, _, _, μ, by rw [h00, hμ]⟩

/-- **Theorem 1.1, by chain lifting along HM's tower.** -/
theorem main_theorem_tower :
    ∃ (R : Type) (_ : CommRing R),
      IsDomain R ∧ IsBezout R ∧ ¬ IsElementaryDivisorDomain R :=
  ⟨TowerConstruction.R, inferInstance, TowerConstruction.R.isDomain,
    TowerConstruction.R.isBezout, fun h => not_hasSmithNormalForm_tower (h.2 2 2 _)⟩

end BezoutCounterexample

