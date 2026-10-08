import BezoutCounterexample.Principalization.LocalN
import BezoutCounterexample.Constructive.SepPoly

/-!
# Recentring at an explicit point (Task D, R6; roadmap §1.0 step 2, §1.4)

`Chart.exists_centred_N` recentres by `minpoly ℚ (residue xᵢ)`, assuming
`[Algebra.IsIntegral ℚ (ResidueField R)]` (Zariski). Here the residue field is replaced by an
explicit point `ζ : R → L` with kernel `𝔪` (`κ(z) := L`), `L/ℚ` finite with a zero test (as
given by `HasPres.exists_point`), and the minimal polynomial by `exists_sep_poly` (Kronecker
factorisation and the zero test in `L`). The conclusion is that of `exists_centred_N`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing Polynomial BezoutCounterexample.Constructive

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ} [IsLocalRing R]

namespace Chart

/-- **Recentring at an explicit point**, without `minpoly` and without Zariski. -/
theorem exists_centred_pos [Algebra.FormallySmooth ℚ R]
    [Algebra.FormallySmooth ℚ (ResidueField R)] [Fact (PolyIndNoeth R)]
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    (hz : ∀ x : L, x = 0 ∨ x ≠ 0) (ζ : R →ₐ[ℚ] L) (hζ : ∀ x, ζ x = 0 ↔ x ∈ maximalIdeal R)
    (c : Chart R n) :
    ∃ c' : Chart R n, c'.IsCentred ∧ ∀ i, c.x i ∈ maximalIdeal R → c'.x i = c.x i := by
  obtain ⟨P, hP⟩ := fin_choice (P := fun i (P : ℚ[X]) => aeval (ζ (c.x i)) P = 0 ∧
    aeval (ζ (c.x i)) (derivative P) ≠ 0 ∧ (ζ (c.x i) = 0 → P = X))
    fun i => exists_sep_poly hz (ζ (c.x i))
  set y : Fin n → R := fun i => aeval (c.x i) (P i) with hy
  have hmap : ∀ (a : R) (p : ℚ[X]), ζ (aeval a p) = aeval (ζ a) p := fun a p =>
    (Polynomial.aeval_algHom_apply ζ a p).symm
  have hjac : c.jac y = Matrix.diagonal fun j => aeval (c.x j) (derivative (P j)) := by
    ext i j
    simp only [jac, Matrix.of_apply, hy, Derivation.map_aeval, c.d_x, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  have hdet : IsUnit (c.jac y).det := by
    rw [hjac, Matrix.det_diagonal, IsUnit.prod_univ_iff]
    intro j
    rw [← notMem_maximalIdeal, ← hζ, hmap]
    exact (hP j).2.1
  refine ⟨c.change y hdet, isCentred_of_mem_N fun i => ?_, fun i hi => ?_⟩
  · rw [change_x, ← hζ, hy]
    simp only
    rw [hmap]
    exact (hP i).1
  · rw [change_x, hy]
    simp only [(hP i).2.2 ((hζ _).2 hi), aeval_X]

end Chart

end BezoutCounterexample.Principalization
