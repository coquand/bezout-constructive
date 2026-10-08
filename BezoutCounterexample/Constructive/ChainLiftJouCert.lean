import Mathlib
import BezoutCounterexample.Constructive.ChainLiftSmoothCert

/-!
# Smoothness certificates for Jouanolou rings (wish 4, Jouanolou layer)

From a certificate of `B = ℚ[Y_{m+n}]/(G)` (`SmoothCert m n G`) and elements `y₀ … y_r` of
`ℤ[Y]`, a certificate of `J_B(y) = B[σ₀ … σ_r]/(Σ yⱼσⱼ − 1)` of dimension `n + r`
(`SmoothCert.jou`), in the presentation `jouG G y` on the variables `Y, σ` (`colE`).

The pieces are `P ∧ D(yⱼ)`: the relations of `P` and the equation `E = Σ yₖσₖ − 1`, the
coordinates of `P` and the `σₖ`, `k ≠ j`. The Jacobian is block triangular: the block of `P`,
and in the `σ`-columns the identity with row `j` replaced by `y` (determinant `yⱼ`). The cover is
`C = C · (E + 1) ≡ Σ_{k,j} uₖσⱼ · hₖyⱼ`. Only ideal membership; no primes.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

open MvPolynomial

namespace JouCert

variable {m n r : ℕ}

/-- The variables of the Jouanolou presentation: the old ones, then `σ₀ … σ_r`. -/
def colE (m n r : ℕ) : Fin (m + n) ⊕ Fin (r + 1) ≃ Fin ((m + 1) + (n + r)) :=
  finSumFinEquiv.trans (finCongr (by omega))

lemma colE_injective_inl : Function.Injective fun i : Fin (m + n) => colE m n r (Sum.inl i) :=
  fun _ _ h => Sum.inl_injective ((colE m n r).injective h)

/-- An old polynomial in the new variables. -/
noncomputable abbrev Y (r : ℕ) (p : MvPolynomial (Fin (m + n)) ℤ) :
    MvPolynomial (Fin ((m + 1) + (n + r))) ℤ :=
  rename (fun i => colE m n r (Sum.inl i)) p

/-- The variable `σₖ`. -/
abbrev σv (m n : ℕ) (k : Fin (r + 1)) : Fin ((m + 1) + (n + r)) := colE m n r (Sum.inr k)

/-- The equation `Σ yₖσₖ − 1`. -/
noncomputable def eqn (y : Fin (r + 1) → MvPolynomial (Fin (m + n)) ℤ) :
    MvPolynomial (Fin ((m + 1) + (n + r))) ℤ :=
  ∑ k, Y r (y k) * X (σv m n k) - 1

/-- The Jouanolou presentation `(G, Σ yₖσₖ − 1)`. -/
noncomputable def jouG (G : List (MvPolynomial (Fin (m + n)) ℤ))
    (y : Fin (r + 1) → MvPolynomial (Fin (m + n)) ℤ) :
    List (MvPolynomial (Fin ((m + 1) + (n + r))) ℤ) :=
  G.map (Y r) ++ [eqn y]

lemma Y_mem {G : List (MvPolynomial (Fin (m + n)) ℤ)} {p : MvPolynomial (Fin (m + n)) ℤ}
    (hp : p ∈ lspan G) (y : Fin (r + 1) → MvPolynomial (Fin (m + n)) ℤ) :
    Y r p ∈ lspan (jouG G y) := by
  have h1 : (lspan G).map (rename fun i => colE m n r (Sum.inl i)) ≤ lspan (jouG G y) := by
    rw [lspan, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact Ideal.subset_span (List.mem_append_left _ (List.mem_map_of_mem hg))
  exact h1 (Ideal.mem_map_of_mem _ hp)

lemma eqn_mem (G : List (MvPolynomial (Fin (m + n)) ℤ))
    (y : Fin (r + 1) → MvPolynomial (Fin (m + n)) ℤ) : eqn y ∈ lspan (jouG G y) :=
  Ideal.subset_span (List.mem_append_right _ (List.mem_singleton_self _))

lemma Y_mem_ofFn {k : ℕ} {L : Fin k → MvPolynomial (Fin (m + n)) ℤ}
    {p : MvPolynomial (Fin (m + n)) ℤ} (hp : p ∈ lspan (List.ofFn L))
    {L' : List (MvPolynomial (Fin ((m + 1) + (n + r))) ℤ)} (hL : ∀ i, Y r (L i) ∈ L') :
    Y r p ∈ lspan L' := by
  have h1 : (lspan (List.ofFn L)).map (rename fun i => colE m n r (Sum.inl i)) ≤ lspan L' := by
    rw [lspan, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
    exact Ideal.subset_span (hL i)
  exact h1 (Ideal.mem_map_of_mem _ hp)

/-! ### The row order of a piece -/

/-- `Fin 1 ⊕ Fin r ≃ Fin (r + 1)`: `inl ↦ j`, `inr t ↦ j.succAbove t`. -/
def jEquiv (j : Fin (r + 1)) : Fin 1 ⊕ Fin r ≃ Fin (r + 1) :=
  ((Equiv.sumComm _ _).trans ((Equiv.sumCongr (Equiv.refl _) finOneEquiv).trans
    (Equiv.optionEquivSumPUnit _).symm)).trans (finSuccEquiv' j).symm

lemma jEquiv_inl (j : Fin (r + 1)) (a : Fin 1) : jEquiv j (Sum.inl a) = j := by
  simp [jEquiv]

lemma jEquiv_inr (j : Fin (r + 1)) (t : Fin r) : jEquiv j (Sum.inr t) = j.succAbove t := by
  simp [jEquiv]

/-- The rows of a piece: the relations of `P` and `E` first, then the coordinates of `P` and the
`σₖ`, `k ≠ j`; indexed by `Fin (m + n) ⊕ Fin (r + 1)` (`inr j` is `E`). -/
def rowE (m n : ℕ) (j : Fin (r + 1)) : Fin ((m + 1) + (n + r)) ≃ Fin (m + n) ⊕ Fin (r + 1) :=
  finSumFinEquiv.symm.trans <|
    (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm).trans <|
      (Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumCongr finSumFinEquiv (jEquiv j))

lemma rowE_castSucc (j : Fin (r + 1)) (i : Fin m) :
    rowE m n j (Fin.castAdd (n + r) i.castSucc) = Sum.inl (Fin.castAdd n i) := by
  simp [rowE, Fin.castSucc]

lemma rowE_last (j : Fin (r + 1)) :
    rowE m n j (Fin.castAdd (n + r) (Fin.last m)) = Sum.inr j := by
  have : (Fin.last m) = Fin.natAdd m (0 : Fin 1) := rfl
  simp [rowE, this, jEquiv_inl]

lemma rowE_natAdd_castAdd (j : Fin (r + 1)) (i : Fin n) :
    rowE m n j (Fin.natAdd (m + 1) (Fin.castAdd r i)) = Sum.inl (Fin.natAdd m i) := by
  simp [rowE]

lemma rowE_natAdd_natAdd (j : Fin (r + 1)) (t : Fin r) :
    rowE m n j (Fin.natAdd (m + 1) (Fin.natAdd n t)) = Sum.inr (j.succAbove t) := by
  simp [rowE, jEquiv_inr]

/-! ### Determinants -/

/-- Rows and columns reindexed by two different equivalences: the determinant up to a sign. -/
lemma det_submatrix_equiv_equiv {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [CommRing R] (M : Matrix κ κ R) (ρ e : ι ≃ κ) :
    (M.submatrix ρ e).det = ((Equiv.Perm.sign (e.symm.trans ρ) : ℤ) : R) * M.det := by
  have : M.submatrix ρ e = (M.submatrix (e.symm.trans ρ) id).submatrix e e := by
    ext i j; simp
  rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_permute]

/-- The identity with row `j` replaced by `v` has determinant `v j`. -/
lemma det_updateRow_one {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (j : ι)
    (v : ι → R) : (Matrix.updateRow (1 : Matrix ι ι R) j v).det = v j := by
  have h : Matrix.updateRow (1 : Matrix ι ι R) j v =
      1 + Matrix.replicateCol Unit (Pi.single j (1 : R)) *
        Matrix.replicateRow Unit (v - Pi.single j (1 : R)) := by
    ext k l
    by_cases hk : k = j
    · subst hk
      by_cases hl : l = k
      · subst hl; simp [Matrix.mul_apply]
      · simp [Matrix.mul_apply, Matrix.one_apply, hl, Ne.symm hl]
    · simp [Matrix.mul_apply, Matrix.updateRow_ne hk, hk, Matrix.one_apply]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, Pi.single_apply]

end JouCert

open JouCert

namespace SquarePiece

variable {m n r : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}

/-- The rows of the piece `P ∧ D(yⱼ)`, indexed by `Fin (m + n) ⊕ Fin (r + 1)`. -/
noncomputable def jouRows (P : SquarePiece m n G) (y : Fin (r + 1) → MvPolynomial (Fin (m + n)) ℤ)
    (j : Fin (r + 1)) : Fin (m + n) ⊕ Fin (r + 1) → MvPolynomial (Fin ((m + 1) + (n + r))) ℤ :=
  Sum.elim (fun i => Y r (P.F i)) fun k => if k = j then eqn y else X (σv m n k)

lemma pderiv_Y_σ (p : MvPolynomial (Fin (m + n)) ℤ) (k : Fin (r + 1)) :
    pderiv (σv m n k) (Y r p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [show Y r (p * X i) = Y r p * X (colE m n r (Sum.inl i)) by simp [Y], Derivation.leibniz,
      hp, pderiv_X, Pi.single_apply,
      if_neg (fun h => Sum.inl_ne_inr ((colE m n r).injective h))]
    simp

lemma pderiv_σ_σ (k l : Fin (r + 1)) :
    pderiv (σv m n l) (X (σv m n k) : MvPolynomial (Fin ((m + 1) + (n + r))) ℤ) =
      if k = l then 1 else 0 := by
  rw [pderiv_X, Pi.single_apply]
  by_cases h : k = l
  · subst h; simp
  · rw [if_neg (fun h' => h (Sum.inr_injective ((colE m n r).injective h'))), if_neg h]

lemma pderiv_eqn (y : Fin (r + 1) → MvPolynomial (Fin (m + n)) ℤ) (l : Fin (r + 1)) :
    pderiv (σv m n l) (eqn y) = Y r (y l) := by
  simp only [eqn, map_sub, map_sum, Derivation.leibniz, pderiv_Y_σ, smul_zero, add_zero,
    pderiv_σ_σ, smul_eq_mul, Derivation.map_one_eq_zero, sub_zero]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- The Jacobian of the piece in the `Fin (m + n) ⊕ Fin (r + 1)` order. -/
lemma jac_jouRows_det (P : SquarePiece m n G) (y : Fin (r + 1) → MvPolynomial (Fin (m + n)) ℤ)
    (j : Fin (r + 1)) :
    (Matrix.of fun a b => pderiv (colE m n r b) (P.jouRows y j a)).det =
      Y r (jacPoly P.F).det * Y r (y j) := by
  set M := Matrix.of fun a b => pderiv (colE m n r b) (P.jouRows y j a)
  have h12 : M.toBlocks₁₂ = 0 := by
    ext i k; simp [M, Matrix.toBlocks₁₂, jouRows, pderiv_Y_σ]
  have h11 : M.toBlocks₁₁ =
      (rename fun i => colE m n r (Sum.inl i)).toRingHom.mapMatrix (jacPoly P.F) := by
    ext i l
    simp [M, Matrix.toBlocks₁₁, jouRows, jacPoly, pderiv_rename colE_injective_inl]
  have h22 : M.toBlocks₂₂ = Matrix.updateRow 1 j fun l => Y r (y l) := by
    ext k l
    by_cases hk : k = j
    · subst hk
      simp [M, Matrix.toBlocks₂₂, jouRows, pderiv_eqn]
    · simp only [M, Matrix.toBlocks₂₂, Matrix.of_apply, jouRows, Sum.elim_inr, if_neg hk,
        Matrix.updateRow_ne hk, pderiv_σ_σ, Matrix.one_apply]
  rw [← Matrix.fromBlocks_toBlocks M, h12, Matrix.det_fromBlocks_zero₁₂, h11, h22,
    det_updateRow_one, ← RingHom.map_det]
  rfl

/-- **The piece `P ∧ D(yⱼ)` of the Jouanolou presentation.** -/
noncomputable def jou (P : SquarePiece m n G) (y : Fin (r + 1) → MvPolynomial (Fin (m + n)) ℤ)
    (j : Fin (r + 1)) : SquarePiece (m + 1) (n + r) (jouG G y) where
  F := P.jouRows y j ∘ rowE m n j
  hn := by have := P.hn; omega
  eqmem := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simp only [Function.comp_apply, rowE_last, jouRows, Sum.elim_inr, ite_true]
      exact eqn_mem G y
    | cast i =>
      simp only [Function.comp_apply, rowE_castSucc, jouRows, Sum.elim_inl]
      exact Y_mem (P.eqmem i) y
  h := Y r P.h * Y r (y j)
  e := P.e + 1
  f := P.f
  U := (((Equiv.Perm.sign ((colE m n r).symm.symm.trans (rowE m n j)) : ℤˣ) : ℤ) :
      MvPolynomial (Fin ((m + 1) + (n + r))) ℤ) * Y r P.U * Y r P.h * Y r (y j) ^ P.e
  detc := by
    set s : MvPolynomial (Fin ((m + 1) + (n + r))) ℤ :=
      (((Equiv.Perm.sign ((colE m n r).symm.symm.trans (rowE m n j)) : ℤˣ) : ℤ) :
        MvPolynomial (Fin ((m + 1) + (n + r))) ℤ)
    have hjac : jacPoly (P.jouRows y j ∘ rowE m n j) =
        (Matrix.of fun a b => pderiv (colE m n r b) (P.jouRows y j a)).submatrix (rowE m n j)
          (colE m n r).symm := by
      ext i v; simp [jacPoly]
    have hs : s * s = 1 := by
      simp only [s, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
        Int.cast_one]
    rw [hjac, det_submatrix_equiv_equiv, jac_jouRows_det]
    have hmem := Y_mem (r := r) P.detc y
    have key : s * (Y r (jacPoly P.F).det * Y r (y j)) *
          (s * Y r P.U * Y r P.h * Y r (y j) ^ P.e) - (Y r P.h * Y r (y j)) ^ (P.e + 1) =
        (s * s) * (Y r ((jacPoly P.F).det * P.U - P.h ^ P.e)) * Y r P.h * Y r (y j) ^ (P.e + 1) := by
      simp only [Y, map_sub, map_mul, map_pow]
      linear_combination (rename (fun i => colE m n r (Sum.inl i)) P.h ^ (P.e + 1) *
        rename (fun i => colE m n r (Sum.inl i)) (y j) ^ (P.e + 1)) * hs
    rw [key, hs, one_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hmem)
  genc := by
    intro g hg
    have hE : ∀ i : Fin m, Y r (P.F (Fin.castAdd n i)) ∈
        List.ofFn fun i : Fin (m + 1) => (P.jouRows y j ∘ rowE m n j) (Fin.castAdd (n + r) i) :=
      fun i => List.mem_ofFn.2 ⟨i.castSucc, by
        simp only [Function.comp_apply, rowE_castSucc, jouRows, Sum.elim_inl]⟩
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
      have := Y_mem_ofFn (r := r) (P.genc g₀ hg₀) hE
      rw [show Y r (P.h ^ P.f * g₀) = Y r P.h ^ P.f * Y r g₀ by simp [Y]] at this
      rw [mul_pow, mul_comm (Y r P.h ^ P.f), mul_assoc]
      exact Ideal.mul_mem_left _ _ this
    · rw [List.mem_singleton.1 hg]
      refine Ideal.mul_mem_left _ _ (Ideal.subset_span (List.mem_ofFn.2 ⟨Fin.last m, ?_⟩))
      simp [rowE_last, jouRows]

end SquarePiece

namespace SmoothCert

variable {m n r : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}

/-- **A certificate of the Jouanolou ring** `J_B(y) = B[σ]/(Σ yⱼσⱼ − 1)`, of dimension `n + r`. -/
noncomputable def jou (hG : SmoothCert m n G) (y : Fin (r + 1) → MvPolynomial (Fin (m + n)) ℤ) :
    SmoothCert (m + 1) (n + r) (jouG G y) where
  K := hG.K * (r + 1)
  P t := (hG.P (finProdFinEquiv.symm t).1).jou y (finProdFinEquiv.symm t).2
  C := hG.C
  hC := hG.hC
  u t := Y r (hG.u (finProdFinEquiv.symm t).1) * X (σv m n (finProdFinEquiv.symm t).2)
  cover := by
    have hsum : ∑ t : Fin (hG.K * (r + 1)),
        Y r (hG.u (finProdFinEquiv.symm t).1) * X (σv m n (finProdFinEquiv.symm t).2) *
          ((hG.P (finProdFinEquiv.symm t).1).jou y (finProdFinEquiv.symm t).2).h =
        Y r (∑ k, hG.u k * (hG.P k).h) * (eqn y + 1) := by
      rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
      simp only [Equiv.symm_apply_apply, SquarePiece.jou]
      rw [eqn, sub_add_cancel]
      simp only [Y, map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [hsum]
    have h1 := Y_mem (r := r) hG.cover y
    have h2 := Ideal.mul_mem_left (lspan (jouG G y)) (Y r (∑ k, hG.u k * (hG.P k).h))
      (eqn_mem G y)
    have : ((hG.C : ℕ) : MvPolynomial (Fin ((m + 1) + (n + r))) ℤ) -
        Y r (∑ k, hG.u k * (hG.P k).h) * (eqn y + 1) =
        Y r ((hG.C : MvPolynomial (Fin (m + n)) ℤ) - ∑ k, hG.u k * (hG.P k).h) -
          Y r (∑ k, hG.u k * (hG.P k).h) * eqn y := by
      simp only [map_sub, map_natCast]; ring
    rw [this]
    exact Ideal.sub_mem _ h1 h2

end SmoothCert

end BezoutCounterexample.Constructive
