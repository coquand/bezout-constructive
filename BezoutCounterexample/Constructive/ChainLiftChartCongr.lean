import Mathlib
import BezoutCounterexample.Constructive.ChainLiftChartTransport

/-!
# Changing the coordinates of chart data modulo the ideal (Task B, Rees layer S4a)

`ChartData.exists_coordCongr`: if `β (x'ᵢ - xᵢ) ∈ (G)` for all `i`, then `x'` are again the
coordinates of chart data, with multiplier `β² c`: `V' = β² V`, `B' = β² B - β V λ` where
`β (x' - x) = λ G`. The check is in `ℤ[Y]/(G)`: there `β² ∂(x' - x) = β λ ∂G` and `∂G · V = 0`.
In the Rees layer this replaces a model coordinate `u'` by its global expression `P̃(Y, y)`.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial Matrix

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}

/-- **Chart data with coordinates changed modulo the ideal**, multiplier `β² c`. -/
theorem ChartData.exists_coordCongr (T : ChartData G) (x' : Fin n → MvPolynomial (Fin (m + n)) ℤ)
    (β : MvPolynomial (Fin (m + n)) ℤ) (h : ∀ i, β * (x' i - T.x i) ∈ lspan G) :
    ∃ T' : ChartData G, T'.x = x' ∧ T'.c = β ^ 2 * T.c := by
  obtain ⟨lam, hlam⟩ := fin_choice fun i : Fin n => exists_coeffs G (h i)
  have hπ0 : ∀ r, π G (G.get r) = 0 := fun r =>
    Ideal.Quotient.eq_zero_iff_mem.2 (get_mem_lspan G r)
  -- `β² ∂(x' - x) = β λ ∂G` in the quotient
  have hdx : ∀ i w, π G (β ^ 2 * pderiv w (x' i - T.x i)) =
      ∑ r, π G (β * lam i r) * π G (pderiv w (G.get r)) := by
    intro i w
    have hd := pi_pderiv_of_eq G (hlam i) w
    have hβ : π G (β * (x' i - T.x i)) = 0 := by
      rw [hlam i, map_sum]; exact Finset.sum_eq_zero fun r _ => by rw [map_mul, hπ0, mul_zero]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul] at hd
    rw [map_mul] at hβ
    have : π G (β ^ 2 * pderiv w (x' i - T.x i)) =
        π G β * (π G β * π G (pderiv w (x' i - T.x i)) +
          π G (x' i - T.x i) * π G (pderiv w β)) - π G (pderiv w β) * (π G β * π G (x' i - T.x i)) := by
      rw [map_mul, map_pow]; ring
    rw [this, hd, hβ, mul_zero, sub_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [map_mul]; ring
  set JG := (jacG G).map (π G) with hJG
  set JX := (jacX T.x).map (π G) with hJX
  set JX' := (jacX x').map (π G) with hJX'
  set Vq := T.V.map (π G) with hVq
  set Bq := T.B.map (π G) with hBq
  set Λ := (Matrix.of lam).map (π G) with hΛ
  set βq := π G β with hβq
  have FL : Bq * JG + Vq * JX = π G T.c • 1 := by
    have := T.hL.map_eq
    rwa [Matrix.map_add _ (map_add (π G)), Matrix.map_mul, Matrix.map_mul, map_smul_ringHom,
      Matrix.map_one _ (map_zero _) (map_one _)] at this
  have FD : JG * Vq = 0 := by
    have := T.hD.map_eq
    rwa [Matrix.map_mul, Matrix.map_zero _ (map_zero _)] at this
  have FX : JX * Vq = π G T.c • 1 := by
    have := T.hX.map_eq
    rwa [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _)] at this
  have FH : βq ^ 2 • JX' = βq ^ 2 • JX + βq • (Λ * JG) := by
    refine Matrix.ext fun i w => ?_
    have := hdx i w
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply,
      Matrix.of_apply, jacX, jacG, JX', JX, Λ, JG, βq] at this ⊢
    rw [map_sub, map_mul, map_pow, map_sub] at this
    rw [Finset.mul_sum]
    simp only [map_mul, mul_assoc] at this ⊢
    linear_combination this
  refine ⟨{ x := x'
            B := β ^ 2 • T.B - β • (T.V * Matrix.of lam)
            V := β ^ 2 • T.V
            c := β ^ 2 * T.c
            hL := matCong_of_map G ?_, hD := matCong_of_map G ?_, hX := matCong_of_map G ?_ },
    rfl, rfl⟩
  · rw [Matrix.map_add _ (map_add (π G)), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_sub _ (map_sub (π G)), map_smul_ringHom, map_smul_ringHom, map_smul_ringHom,
      Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [map_pow, map_mul, map_pow, ← hβq, ← hJG, ← hJX', ← hVq, ← hBq, ← hΛ]
    have e1 : βq ^ 2 • Vq * JX' = Vq * (βq ^ 2 • JX') := by
      rw [Matrix.smul_mul, Matrix.mul_smul]
    rw [e1, FH, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.smul_mul, ← Matrix.mul_assoc]
    calc βq ^ 2 • (Bq * JG) - βq • (Vq * Λ * JG) + (βq ^ 2 • (Vq * JX) + βq • (Vq * Λ * JG))
        = βq ^ 2 • (Bq * JG + Vq * JX) := by rw [smul_add]; abel
      _ = (βq ^ 2 * π G T.c) • 1 := by rw [FL, smul_smul]
  · rw [Matrix.map_mul, map_smul_ringHom, Matrix.map_zero _ (map_zero _)]
    rw [map_pow, ← hβq, ← hJG, ← hVq]
    rw [Matrix.mul_smul, FD, smul_zero]
  · rw [Matrix.map_mul, map_smul_ringHom, map_smul_ringHom,
      Matrix.map_one _ (map_zero _) (map_one _)]
    rw [map_pow, map_mul, map_pow, ← hβq, ← hJX', ← hVq]
    rw [Matrix.mul_smul, ← Matrix.smul_mul, FH, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      FX, Matrix.mul_assoc, FD, Matrix.mul_zero, smul_zero, add_zero, smul_smul]

end BezoutCounterexample.Constructive
