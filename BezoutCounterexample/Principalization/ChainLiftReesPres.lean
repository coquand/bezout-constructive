import Mathlib
import BezoutCounterexample.Principalization.Rees
import BezoutCounterexample.Constructive.ChainLiftSmoothCert

/-!
# A presentation of the extended Rees algebra in `(Y, s, y)` (Task B, Rees layer S6a)

Generic in the filtration and in the generators. `A ≅ ℚ[Y] ⧸ (G)` (`e`, `G` integer relations), `Φ` a
filtration of `A` with `F_j = A` for `j ≤ 0`, and generators `yᵢ = C(gᵢ) T^{δᵢ}` with `gᵢ ∈ ℤ[Y]`,
`gᵢ ∈ F_{δᵢ}`, which generate the Rees algebra together with `s = T⁻¹` (R2: `hgen`).

`ℚ[Y, s, y] → A[T^±]`, `Y ↦ Y`, `s ↦ T⁻¹`, `yᵢ ↦ C(gᵢ) T^{δᵢ}` (`reesVec`), factors through
`B_Q = ℚ[Y, T, W] ⧸ (G, T W - 1)` (`reesFvec`), and `β : B_Q → A[T^±]` has the left inverse
`γ = eval₂ φA T` (Laurent), so the kernel is that of `ℚ[Y, s, y] → B_Q`: explicit by elimination
(`exists_ker_list`), cleared to `ℤ`.

* `reesβ_injective`, `aeval_reesVec`;
* `exists_reesPres`: integer relations `GR` with `ker = (GR)` and
  `ℚ[Y, s, y] ⧸ (GR) ≃+* ReesAlg Φ` sending the variables to `(Y, s, y)`.

This is the Rees half of `ChainLiftBridgeTorsor` (no `σ`), stated for any generator family, so that the
D3.5 consumer switch from `gensF` to `canonGensF` can use it unchanged.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

variable {A : Type} [CommRing A] [Algebra ℚ A] {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ))
  (e : SmoothCert.QB G ≃+* A)

/-- Variables of `ℚ[Y, T, W]`. -/
def rpY (k : Fin (m + n)) : Fin ((m + n) + 2) := Fin.castAdd 2 k
def rpT : Fin ((m + n) + 2) := Fin.natAdd (m + n) 0
def rpW : Fin ((m + n) + 2) := Fin.natAdd (m + n) 1

/-- The relations of `A[T^±]`: `G` and `T W - 1`. -/
def reesH₀ : List (MvPolynomial (Fin ((m + n) + 2)) ℚ) :=
  (G.map (rename rpY) ++ [X rpT * X rpW - 1]).map toQZ

/-- `B_Q = ℚ[Y, T, W] ⧸ (G, T W - 1)`. -/
abbrev ReesBQ := MvPolynomial (Fin ((m + n) + 2)) ℚ ⧸ lspan (reesH₀ G)

/-- `A`'s element of a rational polynomial in `Y`. -/
def toAq (p : MvPolynomial (Fin (m + n)) ℚ) : A := e (Ideal.Quotient.mk _ p)

omit [Algebra ℚ A] in
/-- Two ring homs out of `ℚ[V]` agree on constants. -/
lemma ratHom_C {V R : Type*} [Ring R] (f g : MvPolynomial V ℚ →+* R) (q : ℚ) :
    f (MvPolynomial.C q) = g (MvPolynomial.C q) :=
  RingHom.congr_fun (RingHom.ext_rat (f.comp MvPolynomial.C) (g.comp MvPolynomial.C)) q

/-- The values of `β` on `(Y, T, W)`. -/
def reesBvec : Fin ((m + n) + 2) → A[T;T⁻¹] :=
  Fin.append (fun k => LaurentPolynomial.C (toAq G e (X k))) (fun j : Fin 2 => if j = 0 then T 1 else T (-1))

lemma aeval_reesBvec_rename (p : MvPolynomial (Fin (m + n)) ℚ) :
    aeval (reesBvec G e) (rename rpY p) = LaurentPolynomial.C (toAq G e p) := by
  rw [aeval_rename]
  have : (aeval (reesBvec G e ∘ rpY)).toRingHom =
      (LaurentPolynomial.C : A →+* A[T;T⁻¹]).comp (e.toRingHom.comp (Ideal.Quotient.mk _)) := by
    refine MvPolynomial.ringHom_ext (fun q => ?_) (fun k => ?_)
    · exact ratHom_C _ _ q
    · simp [reesBvec, rpY, toAq]
  exact RingHom.congr_fun this p

lemma reesBvec_T : reesBvec G e rpT = T 1 := by simp [reesBvec, rpT]
lemma reesBvec_W : reesBvec G e rpW = T (-1) := by simp [reesBvec, rpW]

/-- `β : B_Q → A[T^±]`. -/
def reesβ : ReesBQ G →ₐ[ℚ] A[T;T⁻¹] :=
  Ideal.Quotient.liftₐ _ (aeval (reesBvec G e)) fun h hh => by
    have hle : lspan (reesH₀ G) ≤ RingHom.ker (aeval (reesBvec G e)).toRingHom := by
      rw [lspan, Ideal.span_le]
      intro x hx
      simp only [reesH₀, Set.mem_setOf_eq, List.mem_map, List.mem_append, List.mem_singleton] at hx
      obtain ⟨P, hP | rfl, rfl⟩ := hx
      · obtain ⟨g, hg, rfl⟩ := hP
        show aeval (reesBvec G e) (toQZ (rename rpY g)) = 0
        have h0 : Ideal.Quotient.mk (lspan (G.map toQZ)) (toQZ g) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (List.mem_map_of_mem hg))
        rw [toQZ, map_rename, aeval_reesBvec_rename]
        unfold toAq
        rw [h0, map_zero, map_zero]
      · show aeval (reesBvec G e) (toQZ (X rpT * X rpW - 1)) = 0
        rw [map_sub, map_mul, map_one, map_X, map_X, map_sub, map_mul, map_one, aeval_X, aeval_X,
          reesBvec_T, reesBvec_W, ← T_add]
        norm_num [T_zero]
    exact hle hh

lemma reesβ_mk (p : MvPolynomial (Fin ((m + n) + 2)) ℚ) :
    reesβ G e (Ideal.Quotient.mk _ p) = aeval (reesBvec G e) p := rfl

/-- `A → B_Q`, through the presentation. -/
def reesφA : A →+* ReesBQ G :=
  (Ideal.Quotient.lift (lspan (G.map toQZ)) ((Ideal.Quotient.mk _).comp (rename rpY).toRingHom)
    fun p hp => by
      have hle : lspan (G.map toQZ) ≤ RingHom.ker ((Ideal.Quotient.mk (lspan (reesH₀ G))).comp
          (rename (rpY (m := m) (n := n))).toRingHom) := by
        rw [lspan, Ideal.span_le]
        intro x hx
        simp only [Set.mem_setOf_eq, List.mem_map] at hx
        obtain ⟨P, hP, rfl⟩ := hx
        show Ideal.Quotient.mk _ (rename rpY (toQZ P)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        refine Ideal.subset_span (List.mem_map.2 ⟨rename rpY P,
          List.mem_append_left _ (List.mem_map_of_mem hP), ?_⟩)
        rw [toQZ, map_rename]
      exact hle hp).comp e.symm.toRingHom

lemma reesφA_toAq (p : MvPolynomial (Fin (m + n)) ℚ) :
    reesφA G e (toAq G e p) = Ideal.Quotient.mk _ (rename rpY p) := by
  simp [reesφA, toAq]

lemma mem_reesH₀_TW : (X rpT * X rpW - 1 : MvPolynomial (Fin ((m + n) + 2)) ℚ) ∈ lspan (reesH₀ G) :=
  Ideal.subset_span (List.mem_map.2 ⟨X rpT * X rpW - 1, List.mem_append_right _ (by simp), by simp⟩)

/-- The unit `T` of `B_Q`. -/
def reesUT : (ReesBQ G)ˣ where
  val := Ideal.Quotient.mk _ (X rpT)
  inv := Ideal.Quotient.mk _ (X rpW)
  val_inv := by
    rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact mem_reesH₀_TW G
  inv_val := by
    rw [mul_comm, ← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact mem_reesH₀_TW G

/-- `γ : A[T^±] → B_Q`, the left inverse of `β`. -/
def reesγ : A[T;T⁻¹] →+* ReesBQ G := LaurentPolynomial.eval₂ (reesφA G e) (reesUT G)

/-- **`γ ∘ β = id`.** -/
theorem reesγβ : (reesγ G e).comp (reesβ G e).toRingHom = RingHom.id _ := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun q => ?_) (fun v => ?_))
  · exact ratHom_C (((reesγ G e).comp (reesβ G e).toRingHom).comp (Ideal.Quotient.mk _))
      ((RingHom.id _).comp (Ideal.Quotient.mk _)) q
  show reesγ G e (reesβ G e (Ideal.Quotient.mk _ (X v))) = Ideal.Quotient.mk _ (X v)
  rw [reesβ_mk, aeval_X]
  refine Fin.addCases (fun k => ?_) (fun j => ?_) v
  · have hk : (Fin.castAdd 2 k : Fin ((m + n) + 2)) = rpY k := rfl
    rw [hk]
    simp only [reesBvec, rpY, Fin.append_left, reesγ, LaurentPolynomial.eval₂_C]
    rw [reesφA_toAq, rename_X]; rfl
  · fin_cases j
    · have : (Fin.natAdd (m + n) (0 : Fin 2)) = rpT := rfl
      simp only [Fin.zero_eta, Fin.isValue] at this ⊢
      rw [this, reesBvec_T, reesγ, LaurentPolynomial.eval₂_T, zpow_one]; rfl
    · have : (Fin.natAdd (m + n) (1 : Fin 2)) = rpW := rfl
      simp only [Fin.mk_one, Fin.isValue] at this ⊢
      rw [this, reesBvec_W, reesγ, LaurentPolynomial.eval₂_T, zpow_neg, zpow_one]; rfl

theorem reesβ_injective : Function.Injective (reesβ G e) := by
  intro x y h
  have hx := RingHom.congr_fun (reesγβ G e) x
  have hy := RingHom.congr_fun (reesγβ G e) y
  simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hx hy
  rw [← hx, ← hy, h]

/-! ### The map from `ℚ[Y, s, y]` -/

variable {r : ℕ} (gZ : Fin r → MvPolynomial (Fin (m + n)) ℤ) (δ : Fin r → ℕ)

/-- The substitution `Y ↦ Y`, `s ↦ W`, `yᵢ ↦ gᵢ T^{δᵢ}` into `ℚ[Y, T, W]`. -/
def reesFvec : Fin ((m + n) + (1 + r)) → MvPolynomial (Fin ((m + n) + 2)) ℚ :=
  Fin.append (fun k => X (rpY k))
    (Fin.append (fun _ : Fin 1 => X rpW) (fun i => toQZ (rename rpY (gZ i)) * X rpT ^ δ i))

/-- The generators `yᵢ = C(gᵢ) T^{δᵢ}`. -/
def reesYL (i : Fin r) : A[T;T⁻¹] := LaurentPolynomial.C (toAq G e (toQZ (gZ i))) * T (δ i : ℤ)

/-- `Y ↦ Y`, `s ↦ T⁻¹`, `yᵢ ↦ C(gᵢ) T^{δᵢ}` into `A[T^±]`. -/
def reesVec : Fin ((m + n) + (1 + r)) → A[T;T⁻¹] :=
  Fin.append (fun k => LaurentPolynomial.C (toAq G e (X k))) (Fin.append (fun _ : Fin 1 => T (-1)) (reesYL G e gZ δ))

lemma toAq_surjective (a : A) : ∃ p, toAq G e p = a := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (e.symm a)
  exact ⟨p, by rw [toAq, hp, RingEquiv.apply_symm_apply]⟩

/-- On polynomials in `Y` the Rees map is `C ∘ toAq`. -/
lemma aeval_reesVec_rename (p : MvPolynomial (Fin (m + n)) ℚ) :
    aeval (reesVec G e gZ δ) (rename (Fin.castAdd (1 + r)) p) = LaurentPolynomial.C (toAq G e p) := by
  rw [aeval_rename]
  have : (aeval (reesVec G e gZ δ ∘ Fin.castAdd (1 + r))).toRingHom =
      (LaurentPolynomial.C : A →+* A[T;T⁻¹]).comp (e.toRingHom.comp (Ideal.Quotient.mk _)) := by
    refine MvPolynomial.ringHom_ext (fun q => ?_) (fun k => ?_)
    · exact ratHom_C _ _ q
    · simp [reesVec, toAq]
  exact RingHom.congr_fun this p

/-- **The map to `A[T^±]` factors through `B_Q`.** -/
theorem aeval_reesVec (h : MvPolynomial (Fin ((m + n) + (1 + r))) ℚ) :
    aeval (reesVec G e gZ δ) h = reesβ G e (Ideal.Quotient.mk _ (aeval (reesFvec gZ δ) h)) := by
  have hβ : (reesβ G e).comp (Ideal.Quotient.mkₐ ℚ (lspan (reesH₀ G))) = aeval (reesBvec G e) :=
    Ideal.Quotient.liftₐ_comp _ _ _
  have : (aeval (reesVec G e gZ δ) : MvPolynomial _ ℚ →ₐ[ℚ] A[T;T⁻¹]) =
      ((reesβ G e).comp (Ideal.Quotient.mkₐ ℚ (lspan (reesH₀ G)))).comp (aeval (reesFvec gZ δ)) := by
    rw [hβ, comp_aeval]
    congr 1
    funext v
    refine Fin.addCases (fun k => ?_) (fun v => ?_) v
    · simp only [reesVec, reesFvec, Fin.append_left, aeval_X]
      rw [show reesBvec G e (rpY k) = LaurentPolynomial.C (toAq G e (X k)) by simp [reesBvec, rpY]]
    refine Fin.addCases (fun _ => ?_) (fun i => ?_) v
    · simp only [reesVec, reesFvec, Fin.append_left, Fin.append_right, aeval_X]
      rw [reesBvec_W]
    · simp only [reesVec, reesFvec, Fin.append_right, map_mul, map_pow, aeval_X, reesYL]
      rw [toQZ, map_rename, aeval_reesBvec_rename, reesBvec_T, T_pow, mul_one]
  rw [this]; rfl

/-- **Kernel**: `h(Y, T⁻¹, y) = 0` in `A[T^±]` iff `h(Y, W, g T^δ) ∈ (G, T W - 1)`. -/
theorem aeval_reesVec_eq_zero_iff (h : MvPolynomial (Fin ((m + n) + (1 + r))) ℚ) :
    aeval (reesVec G e gZ δ) h = 0 ↔ aeval (reesFvec gZ δ) h ∈ lspan (reesH₀ G) := by
  rw [aeval_reesVec, ← map_zero (reesβ G e), (reesβ_injective G e).eq_iff,
    Ideal.Quotient.eq_zero_iff_mem]

/-- **Integer relations of the Rees map**: the kernel of `ℚ[Y, s, y] → A[T^±]` is generated by an
explicit list of integer polynomials. -/
theorem exists_reesKer : ∃ GR : List (MvPolynomial (Fin ((m + n) + (1 + r))) ℤ),
    ∀ h, aeval (reesVec G e gZ δ) h = 0 ↔ h ∈ lspan (GR.map toQZ) := by
  obtain ⟨L, hL⟩ := exists_ker_list (reesH₀ G) (reesFvec gZ δ)
  obtain ⟨cq, hcq⟩ := fin_choice (α := ℕ × MvPolynomial (Fin ((m + n) + (1 + r))) ℤ)
    (P := fun j a => 0 < a.1 ∧ toQZ a.2 = (a.1 : MvPolynomial _ ℚ) * L.get j) fun j => by
      obtain ⟨D, q, hD, hq⟩ := int_clear (L.get j)
      exact ⟨(D, q), hD, hq⟩
  refine ⟨List.ofFn fun j => (cq j).2, fun h => ?_⟩
  rw [aeval_reesVec_eq_zero_iff, hL]
  suffices hspan : lspan ((List.ofFn fun j => (cq j).2).map toQZ) = lspan L by rw [hspan]
  apply le_antisymm
  · rw [lspan, Ideal.span_le]
    intro p hp
    simp only [List.map_ofFn, Set.mem_setOf_eq, List.mem_ofFn, Function.comp_apply] at hp
    obtain ⟨j, rfl⟩ := hp
    rw [(hcq j).2]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (List.get_mem L j))
  · rw [lspan, Ideal.span_le]
    intro p hp
    obtain ⟨j, rfl⟩ := List.get_of_mem hp
    have hD : ((cq j).1 : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (hcq j).1.ne'
    have hmem : toQZ (cq j).2 ∈ lspan ((List.ofFn fun j => (cq j).2).map toQZ) :=
      Ideal.subset_span (List.mem_map.2 ⟨_, List.mem_ofFn.2 ⟨j, rfl⟩, rfl⟩)
    have : L.get j = C ((cq j).1 : ℚ)⁻¹ * toQZ (cq j).2 := by
      rw [(hcq j).2, ← mul_assoc, ← map_natCast C, ← C_mul, inv_mul_cancel₀ hD, C_1, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hmem

/-- **Adding known relations**: any integer polynomials in the kernel can be appended to the
relations (the ideal over `ℚ` is unchanged), so that they lie in `(GR)` over `ℤ`. -/
theorem exists_reesKer_ext (Xs : List (MvPolynomial (Fin ((m + n) + (1 + r))) ℤ))
    (hXs : ∀ x ∈ Xs, aeval (reesVec G e gZ δ) (toQZ x) = 0) :
    ∃ GR : List (MvPolynomial (Fin ((m + n) + (1 + r))) ℤ), (∀ x ∈ Xs, x ∈ GR) ∧
      ∀ h, aeval (reesVec G e gZ δ) h = 0 ↔ h ∈ lspan (GR.map toQZ) := by
  obtain ⟨GR, hGR⟩ := exists_reesKer G e gZ δ
  refine ⟨GR ++ Xs, fun x hx => List.mem_append_right _ hx, fun h => ?_⟩
  rw [hGR]
  have hle : lspan ((GR ++ Xs).map toQZ) = lspan (GR.map toQZ) := by
    apply le_antisymm
    · rw [lspan, Ideal.span_le]
      intro p hp
      simp only [List.map_append, List.mem_append, List.mem_map, Set.mem_ofPred_eq] at hp
      rcases hp with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · exact Ideal.subset_span (List.mem_map_of_mem hx)
      · exact (hGR _).1 (hXs x hx)
    · exact Ideal.span_mono fun p hp => by
        simp only [List.map_append, List.mem_append, Set.mem_ofPred_eq] at hp ⊢
        exact Or.inl hp
  rw [hle]

/-! ### The Rees algebra -/

variable (Φ : WFil A) (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
  (hgF : ∀ i, toAq G e (toQZ (gZ i)) ∈ Φ.F (δ i))
  (hgen : ∀ (j : ℤ) (f : A), f ∈ Φ.F j →
    LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (insert (T (-1)) (Set.range (reesYL G e gZ δ))))

include hneg hgF in
lemma reesVec_mem (v : Fin ((m + n) + (1 + r))) : reesVec G e gZ δ v ∈ ReesAlg Φ := by
  refine Fin.addCases (fun k => ?_) (fun v => ?_) v
  · simp only [reesVec, Fin.append_left]
    rw [LaurentPolynomial.C_eq_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  refine Fin.addCases (fun _ => ?_) (fun i => ?_) v
  · simp only [reesVec, Fin.append_left, Fin.append_right]
    have := C_mul_T_mem_ReesAlg (Φ := Φ) (f := (1 : A)) (j := -1) (by rw [hneg _ (by omega)]; trivial)
    rwa [map_one, one_mul] at this
  · simp only [reesVec, Fin.append_right, reesYL]
    exact C_mul_T_mem_ReesAlg (hgF i)

include hneg hgF hgen in
/-- **The Rees map is onto** (R2). -/
theorem reesAlg_le_range : (ReesAlg Φ : Set A[T;T⁻¹]) ⊆ Set.range (aeval (R := ℚ) (reesVec G e gZ δ)) := by
  -- `C a` and the generators are in the range, and the range is closed under `C a • _`
  have hC : ∀ a : A, LaurentPolynomial.C a ∈ Set.range (aeval (R := ℚ) (reesVec G e gZ δ)) := by
    intro a
    obtain ⟨p, rfl⟩ := toAq_surjective G e a
    exact ⟨_, aeval_reesVec_rename G e gZ δ p⟩
  have hadj : ∀ x ∈ Algebra.adjoin A (insert (T (-1)) (Set.range (reesYL G e gZ δ))),
      x ∈ Set.range (aeval (R := ℚ) (reesVec G e gZ δ)) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | ⟨i, rfl⟩
      · exact ⟨X (Fin.natAdd _ (Fin.castAdd r 0)), by simp [reesVec]⟩
      · exact ⟨X (Fin.natAdd _ (Fin.natAdd 1 i)), by simp [reesVec]⟩
    | algebraMap a => rw [← LaurentPolynomial.C_eq_algebraMap]; exact hC a
    | add x y _ _ hx hy =>
      obtain ⟨p, rfl⟩ := hx; obtain ⟨q, rfl⟩ := hy; exact ⟨p + q, map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨p, rfl⟩ := hx; obtain ⟨q, rfl⟩ := hy; exact ⟨p * q, map_mul _ _ _⟩
  intro p hp
  have hp' : p = ∑ j ∈ p.coeff.support, LaurentPolynomial.C (p.coeff j) * T j := by
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [single_eq_C_mul_T]
  rw [hp']
  have hsum : ∀ s : Finset ℤ, ∑ j ∈ s, LaurentPolynomial.C (p.coeff j) * T j ∈ Set.range (aeval (R := ℚ) (reesVec G e gZ δ)) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => exact ⟨0, by simp⟩
    | cons j s hj ih =>
      rw [Finset.sum_cons]
      obtain ⟨q, hq⟩ := ih
      obtain ⟨q', hq'⟩ := hadj _ (hgen j _ (hp j))
      exact ⟨q' + q, by rw [map_add, hq, hq']⟩
  exact hsum _

include hneg hgF in
/-- The map `ℚ[Y, s, y] → ReesAlg Φ`. -/
def reesPresMap : MvPolynomial (Fin ((m + n) + (1 + r))) ℚ →+* ReesAlg Φ :=
  (aeval (reesVec G e gZ δ)).toRingHom.codRestrict (ReesAlg Φ).toSubring fun h => by
    induction h using MvPolynomial.induction_on with
    | C q =>
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, IsScalarTower.algebraMap_apply ℚ A]
      exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      exact reesVec_mem G e gZ δ Φ hneg hgF v

include hneg hgF hgen in
/-- **The presentation of the Rees algebra in `(Y, s, y)`.** -/
theorem exists_reesPres : ∃ (GR : List (MvPolynomial (Fin ((m + n) + (1 + r))) ℤ))
    (E : MvPolynomial (Fin ((m + n) + (1 + r))) ℚ ⧸ lspan (GR.map toQZ) ≃+* ReesAlg Φ),
    (∀ h, aeval (reesVec G e gZ δ) h = 0 ↔ h ∈ lspan (GR.map toQZ)) ∧
    ∀ h, (E (Ideal.Quotient.mk _ h) : A[T;T⁻¹]) = aeval (reesVec G e gZ δ) h := by
  obtain ⟨GR, hGR⟩ := exists_reesKer G e gZ δ
  have hker : RingHom.ker (reesPresMap G e gZ δ Φ hneg hgF) = lspan (GR.map toQZ) := by
    ext h
    rw [RingHom.mem_ker, ← hGR, ← Subtype.val_injective.eq_iff]
    rfl
  have hsurj : Function.Surjective (reesPresMap G e gZ δ Φ hneg hgF) := by
    rintro ⟨p, hp⟩
    obtain ⟨h, hh⟩ := reesAlg_le_range G e gZ δ Φ hneg hgF hgen hp
    exact ⟨h, Subtype.ext hh⟩
  refine ⟨GR, (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj),
    hGR, fun h => ?_⟩
  rfl

end BezoutCounterexample.Principalization
