import Mathlib

/-!
# The Jacobian-minor cover (§2.2, milestone C1): linear algebra

* `sum_minors_of_sq`: a matrix with `E² = c E` and `tr E = m c` over a `ℚ`-algebra has
  `Σ_{|S| = m} det E_SS = c^m`. For `f = det (1 + X E)` one has `m c f = (1 + c X) f'`
  (first-order Taylor expansion of `f(x) f(ε) = f(x + ε (1 + c x))` in the dual numbers), so the
  coefficients satisfy `(k+1) c_{k+1} = c (m - k) c_k`, and `c_m = c^m` after cancelling `m!`.
  No inverses, no rank idempotents.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

open Polynomial Matrix DualNumber TrivSqZeroExt

section Minors

variable {R : Type*} [CommRing R] {r : Type*} [Fintype r] [DecidableEq r]

/-- `det (1 + X E)`. -/
noncomputable abbrev detPoly (E : Matrix r r R) : R[X] := det (1 + (X : R[X]) • E.map C)

lemma aeval_detPoly {S : Type*} [CommRing S] [Algebra R S] (E : Matrix r r R) (a : S) :
    aeval a (detPoly E) = det (1 + a • E.map (algebraMap R S)) := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite, aeval_C]
  exact mul_comm _ _

/-- Multiplicativity of `det (1 + a E)` for `E² = c E`. -/
lemma detPoly_mul {S : Type*} [CommRing S] [Algebra R S] (E : Matrix r r R) (c : R)
    (hE : E * E = c • E) (a b : S) :
    aeval a (detPoly E) * aeval b (detPoly E) =
      aeval (a + b + a * b * algebraMap R S c) (detPoly E) := by
  rw [aeval_detPoly, aeval_detPoly, aeval_detPoly, ← det_mul]
  congr 1
  have h2 : E.map (algebraMap R S) * E.map (algebraMap R S) =
      algebraMap R S c • E.map (algebraMap R S) := by
    rw [← Matrix.map_mul, hE]
    ext i j; simp
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm, h2, smul_smul,
    add_smul, add_smul]
  abel

/-- The differential equation `m c f = (1 + c X) f'`. -/
lemma detPoly_ode (E : Matrix r r R) (c : R) (m : ℕ) (hE : E * E = c • E)
    (htr : E.trace = m * c) :
    detPoly E * C (m * c) = derivative (detPoly E) * (1 + C c * X) := by
  set f := detPoly E
  have h := detPoly_mul (S := DualNumber R[X]) E c hE (inl X) ε
  have h0 : aeval (ε : DualNumber R[X]) f = 1 + algebraMap R _ (m * c) * ε := by
    have := aeval_add_of_sq_eq_zero f (0 : DualNumber R[X]) ε eps_pow_two
    rw [zero_add] at this
    have hc0 : f.coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero, eval_det_add_X_smul, det_one, eval_one]
    have hc1 : (derivative f).coeff 0 = m * c := by
      rw [coeff_derivative, coeff_det_one_add_X_smul_one, htr]; simp
    rw [this, ← coeff_zero_eq_aeval_zero', ← coeff_zero_eq_aeval_zero', hc0, hc1, map_one]
  have hx : ∀ p : R[X], aeval (inl X : DualNumber R[X]) p = inl p := by
    intro p
    have : (inl X : DualNumber R[X]) = inlAlgHom R R[X] R[X] X := rfl
    rw [this, Polynomial.aeval_algHom_apply, aeval_X_left_apply]
    rfl
  rw [add_assoc, h0, aeval_add_of_sq_eq_zero, hx, hx] at h
  swap
  · have : (ε + inl X * ε * algebraMap R (DualNumber R[X]) c) =
        ε * (1 + inl X * algebraMap R (DualNumber R[X]) c) := by ring
    rw [this, mul_pow, eps_pow_two, zero_mul]
  have := congrArg snd h
  simp only [DualNumber.snd_mul, snd_add, fst_add, snd_one, fst_one, snd_inl, fst_inl, fst_eps,
    snd_eps, mul_zero, zero_add, add_zero, mul_one, algebraMap_eq_inl', TrivSqZeroExt.fst_mul,
    zero_mul, Polynomial.algebraMap_eq] at this
  linear_combination this

/-- The coefficient recursion `(k+1) c_{k+1} = c (m - k) c_k`. -/
lemma detPoly_coeff_succ (E : Matrix r r R) (c : R) (m : ℕ) (hE : E * E = c • E)
    (htr : E.trace = m * c) (k : ℕ) :
    ((k : R) + 1) * (detPoly E).coeff (k + 1) = c * ((m : R) - k) * (detPoly E).coeff k := by
  have h := congrArg (fun p => p.coeff k) (detPoly_ode E c m hE htr)
  simp only [coeff_mul_C, mul_add, mul_one] at h
  rcases k with _ | k
  · have h1 : (derivative (detPoly E) * (C c * X)).coeff 0 = 0 := by
      rw [← mul_assoc, coeff_mul_X_zero]
    rw [coeff_add, h1, coeff_derivative] at h
    simp only [Nat.cast_zero, zero_add, sub_zero] at h ⊢
    have h0 : (detPoly E).coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero, eval_det_add_X_smul, det_one, eval_one]
    rw [h0] at h ⊢
    linear_combination -h
  · have h2 : (derivative (detPoly E) * (C c * X)).coeff (k + 1) =
        (derivative (detPoly E)).coeff k * c := by
      rw [← mul_assoc, coeff_mul_X, coeff_mul_C]
    rw [coeff_add, h2, coeff_derivative, coeff_derivative] at h
    push_cast at h ⊢
    linear_combination -h

/-- `k! c_k = c^k · m (m-1) ⋯ (m-k+1)`. -/
lemma detPoly_coeff_eq (E : Matrix r r R) (c : R) (m : ℕ) (hE : E * E = c • E)
    (htr : E.trace = m * c) (k : ℕ) :
    (k.factorial : R) * (detPoly E).coeff k = c ^ k * (m.descFactorial k : R) := by
  induction k with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, Nat.descFactorial_zero]
    rw [coeff_zero_eq_eval_zero, eval_det_add_X_smul, det_one, eval_one]
  | succ k ih =>
    have hs := detPoly_coeff_succ E c m hE htr k
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.descFactorial_succ]
    rcases Nat.lt_or_ge m k with hk | hk
    · have h0 : m.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.2 hk
      rw [h0, Nat.cast_zero, mul_zero] at ih
      rw [h0, mul_zero, Nat.cast_zero, mul_zero]
      push_cast
      linear_combination (k.factorial : R) * hs + (c * ((m : R) - k)) * ih
    · rw [Nat.cast_mul, Nat.cast_sub hk]
      push_cast
      linear_combination (k.factorial : R) * hs + (c * ((m : R) - k)) * ih

/-- **Principal minors of a quasi-idempotent.** Over a `ℚ`-algebra, `E² = c E` and
`tr E = m c` give `Σ_{|S| = m} det E_SS = c^m`. -/
theorem sum_minors_of_sq [Algebra ℚ R] (E : Matrix r r R) (c : R) (m : ℕ) (hE : E * E = c • E)
    (htr : E.trace = m * c) :
    ∑ s ∈ Finset.univ.powersetCard m,
      (E.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det = c ^ m := by
  rw [← coeff_det_one_add_X_smul_eq_sum_minors]
  have h := detPoly_coeff_eq E c m hE htr m
  rw [Nat.descFactorial_self] at h
  have hu : IsUnit (m.factorial : R) := by
    have : IsUnit (m.factorial : ℚ) :=
      isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))
    simpa using this.map (algebraMap ℚ R)
  exact hu.mul_left_cancel (h.trans (mul_comm _ _))

/-- The same without division: `m! Σ_{|S| = m} det E_SS = m! c^m` over any commutative ring. -/
theorem factorial_mul_sum_minors_of_sq (E : Matrix r r R) (c : R) (m : ℕ)
    (hE : E * E = c • E) (htr : E.trace = m * c) :
    (m.factorial : R) * ∑ s ∈ Finset.univ.powersetCard m,
      (E.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det =
      (m.factorial : R) * c ^ m := by
  rw [← coeff_det_one_add_X_smul_eq_sum_minors, detPoly_coeff_eq E c m hE htr m,
    Nat.descFactorial_self, mul_comm]

end Minors

/-! ## Square systems from chart data -/

section Square

variable {Q : Type*} [CommRing Q] {m n r : ℕ}

/-- The rows `∂G_σ` followed by `∂x`. -/
def sqRows (DG : Matrix (Fin r) (Fin (m + n)) Q) (DX : Matrix (Fin n) (Fin (m + n)) Q)
    (σ : Fin m → Fin r) : Matrix (Fin (m + n)) (Fin (m + n)) Q :=
  Matrix.of fun i k => Fin.addCases (fun a => DG (σ a) k) (fun b => DX b k) i

/-- The columns `B_σ` followed by `V`. -/
def sqCols (B : Matrix (Fin (m + n)) (Fin r) Q) (V : Matrix (Fin (m + n)) (Fin n) Q)
    (σ : Fin m → Fin r) : Matrix (Fin (m + n)) (Fin (m + n)) Q :=
  Matrix.of fun k i => Fin.addCases (fun a => B k (σ a)) (fun b => V k b) i

variable (DG : Matrix (Fin r) (Fin (m + n)) Q) (DX : Matrix (Fin n) (Fin (m + n)) Q)
  (B : Matrix (Fin (m + n)) (Fin r) Q) (V : Matrix (Fin (m + n)) (Fin n) Q) (c : Q)
  (σ : Fin m → Fin r)

@[simp] lemma sqRows_castAdd (a : Fin m) (k : Fin (m + n)) :
    sqRows DG DX σ (Fin.castAdd n a) k = DG (σ a) k := by simp [sqRows]
@[simp] lemma sqRows_natAdd (b : Fin n) (k : Fin (m + n)) :
    sqRows DG DX σ (Fin.natAdd m b) k = DX b k := by simp [sqRows]
@[simp] lemma sqCols_castAdd (a : Fin m) (k : Fin (m + n)) :
    sqCols B V σ k (Fin.castAdd n a) = B k (σ a) := by simp [sqCols]
@[simp] lemma sqCols_natAdd (b : Fin n) (k : Fin (m + n)) :
    sqCols B V σ k (Fin.natAdd m b) = V k b := by simp [sqCols]

lemma sq_mul_castAdd_castAdd (a a' : Fin m) :
    (sqRows DG DX σ * sqCols B V σ) (Fin.castAdd n a) (Fin.castAdd n a') = (DG * B) (σ a) (σ a') := by
  simp [Matrix.mul_apply]
lemma sq_mul_castAdd_natAdd (a : Fin m) (b : Fin n) :
    (sqRows DG DX σ * sqCols B V σ) (Fin.castAdd n a) (Fin.natAdd m b) = (DG * V) (σ a) b := by
  simp [Matrix.mul_apply]
lemma sq_mul_natAdd_castAdd (b : Fin n) (a : Fin m) :
    (sqRows DG DX σ * sqCols B V σ) (Fin.natAdd m b) (Fin.castAdd n a) = (DX * B) b (σ a) := by
  simp [Matrix.mul_apply]
lemma sq_mul_natAdd_natAdd (b b' : Fin n) :
    (sqRows DG DX σ * sqCols B V σ) (Fin.natAdd m b) (Fin.natAdd m b') = (DX * V) b b' := by
  simp [Matrix.mul_apply]

/-- `E = ∂G · B` is quasi-idempotent. -/
lemma sq_E_sq (hL : B * DG + V * DX = c • 1) (hD : DG * V = 0) :
    (DG * B) * (DG * B) = c • (DG * B) := by
  have hBD : B * DG = c • 1 - V * DX := eq_sub_of_add_eq hL
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, hBD, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    show DG * (V * DX * B) = (DG * V) * (DX * B) by simp only [Matrix.mul_assoc], hD,
    Matrix.zero_mul, sub_zero]

/-- `tr E = m c`. -/
lemma sq_E_trace (hL : B * DG + V * DX = c • 1) (hX : DX * V = c • 1) :
    (DG * B).trace = (m : Q) * c := by
  have h := congrArg Matrix.trace hL
  rw [Matrix.trace_add, Matrix.trace_mul_comm V, hX, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, Matrix.trace_one, Fintype.card_fin, Fintype.card_fin,
    Matrix.trace_mul_comm] at h
  simp only [smul_eq_mul] at h
  push_cast at h
  linear_combination h

/-- **Certificate (i)**: `det [∂G_σ; ∂x] · det [B_σ | V] = det E_σσ · cⁿ`. -/
lemma det_sq (hD : DG * V = 0) (hX : DX * V = c • 1) :
    (sqRows DG DX σ).det * (sqCols B V σ).det = ((DG * B).submatrix σ σ).det * c ^ n := by
  rw [← Matrix.det_mul, ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  have : (sqRows DG DX σ * sqCols B V σ).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks ((DG * B).submatrix σ σ) 0 ((DX * B).submatrix id σ) (c • 1) := by
    ext (i | i) (j | j)
    · simp [sq_mul_castAdd_castAdd]
    · simp [sq_mul_castAdd_natAdd, hD]
    · simp [sq_mul_natAdd_castAdd]
    · rw [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_right,
        sq_mul_natAdd_natAdd, hX]
      rfl
  rw [this, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin]

/-- The coefficients `x = E_{l,σ} · adj E_σσ`. -/
def sepCoeff (l : Fin r) : Fin m → Q :=
  Matrix.vecMul (fun a => (DG * B) l (σ a)) ((DG * B).submatrix σ σ).adjugate

omit [CommRing Q] in
lemma vecMul_row {Q : Type*} [CommRing Q] {a b d : Type*} [Fintype b] (A : Matrix a b Q)
    (C : Matrix b d Q) (i : a) : Matrix.vecMul (A i) C = (A * C) i := by
  ext j; simp [Matrix.vecMul, dotProduct, Matrix.mul_apply]

omit [CommRing Q] in
lemma submatrix_id_mul {Q : Type*} [CommRing Q] {a a' b d : Type*} [Fintype b] (A : Matrix a b Q)
    (C : Matrix b d Q) (f : a' → a) : A.submatrix f id * C = (A * C).submatrix f id := by
  ext i j; simp [Matrix.mul_apply]

/-- **Rows outside `σ`**: `Δ cⁿ (Σ_a x_a ∇G_{σ a} - Δ ∇G_l) = 0`, `Δ = det E_σσ`. No inverses:
`v = x ∂G_σ - Δ ∇G_l` has `v W = 0` (`W = [B_σ | V]`), so `det W · v = 0`, and
`det M · det W = Δ cⁿ` (`det_sq`). -/
lemma sep_row (hD : DG * V = 0) (hX : DX * V = c • 1) (l : Fin r) :
    (((DG * B).submatrix σ σ).det * c ^ n) •
      (Matrix.vecMul (sepCoeff DG B σ l) (DG.submatrix σ id) -
        ((DG * B).submatrix σ σ).det • DG l) = 0 := by
  set Δ := ((DG * B).submatrix σ σ).det
  set x := sepCoeff DG B σ l
  set v := Matrix.vecMul x (DG.submatrix σ id) - Δ • DG l
  have hxE : Matrix.vecMul x ((DG * B).submatrix σ σ) = Δ • fun a => (DG * B) l (σ a) := by
    simp only [x, sepCoeff, Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul,
      Matrix.vecMul_one, Δ]
  have hvB : ∀ a', Matrix.vecMul v B (σ a') = 0 := by
    intro a'
    have := congrFun hxE a'
    simp only [v, Matrix.sub_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, submatrix_id_mul,
      vecMul_row, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]
    simp [Matrix.vecMul, dotProduct]
  have hvV : Matrix.vecMul v V = 0 := by
    simp only [v, Matrix.sub_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, submatrix_id_mul,
      vecMul_row, hD]
    ext j; simp
  have hvW : Matrix.vecMul v (sqCols B V σ) = 0 := by
    ext i
    refine Fin.addCases (fun a' => ?_) (fun b' => ?_) i
    · rw [Pi.zero_apply, ← hvB a']; simp [Matrix.vecMul, dotProduct]
    · have := congrFun hvV b'
      rw [Pi.zero_apply] at this ⊢; rw [← this]; simp [Matrix.vecMul, dotProduct]
  have hdet := det_sq DG DX B V c σ hD hX
  have hWv : (sqCols B V σ).det • v = 0 := by
    have := congrArg (fun u => Matrix.vecMul u (sqCols B V σ).adjugate) hvW
    simp only [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one,
      Matrix.zero_vecMul] at this
    exact this
  ext k
  have hk := congrFun hWv k
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk ⊢
  rw [← hdet]
  linear_combination (sqRows DG DX σ).det * hk

/-- `sep_row` multiplied by `B`: `Δ cⁿ (Σ_a x_a E_{σ a} - Δ E_l) = 0`. -/
lemma sep_rowE (hD : DG * V = 0) (hX : DX * V = c • 1) (l : Fin r) :
    (((DG * B).submatrix σ σ).det * c ^ n) •
      (Matrix.vecMul (sepCoeff DG B σ l) ((DG * B).submatrix σ id) -
        ((DG * B).submatrix σ σ).det • (DG * B) l) = 0 := by
  have h := congrArg (fun u => Matrix.vecMul u B) (sep_row DG DX B V c σ hD hX l)
  simpa only [Matrix.smul_vecMul, Matrix.sub_vecMul, Matrix.vecMul_vecMul, submatrix_id_mul,
    vecMul_row, Matrix.zero_vecMul] using h

end Square

end BezoutCounterexample.Constructive
