import BezoutCounterexample.Principalization.Local
import BezoutCounterexample.Constructive.KrullBar

/-!
# Centred charts without finite generation of `𝔪` (leaf)

`Chart.isCentred_of_mem` and `Chart.exists_centred` (`Local.lean`) take `(maximalIdeal R).FG` for
Nakayama. Here the same statements assume `[Fact (PolyIndNoeth R)]` instead: the proof gives
`𝔪 ≤ (x) ⊔ 𝔪²`, and `PolyIndNoeth.le_of_le_sup_sq` (Krull intersection for an arbitrary ideal,
`Constructive/KrullBar.lean`, applied in `R ⧸ (x)`) turns this into `𝔪 ≤ (x)`. At HM's points
(`Localization.AtPrime` of a f.t. `ℚ`-algebra) the instance is `fact_polyIndNoeth_atPrime`
(polyBar), so no generators of `𝔪` are needed.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing TensorProduct Polynomial BezoutCounterexample.Constructive

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ} [IsLocalRing R]

namespace Chart

variable {c : Chart R n}

/-- The core of `isCentred_of_mem`: `𝔪 ≤ (x) ⊔ 𝔪²`. -/
theorem le_span_sup_sq [Algebra.FormallySmooth ℚ R]
    [Algebra.FormallySmooth ℚ (ResidueField R)] (hx : ∀ i, c.x i ∈ maximalIdeal R) :
    maximalIdeal R ≤ Ideal.span (Set.range c.x) ⊔ maximalIdeal R ^ 2 := by
  intro r hr
  set r' := r - ∑ i, c.d i r * c.x i with hr'
  have hr'm : r' ∈ maximalIdeal R :=
    sub_mem hr (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hx i))
  have hd : ∀ l, c.d l r' ∈ maximalIdeal R := by
    intro l
    have : ∀ i, c.d l (c.d i r * c.x i) =
        (if l = i then c.d i r else 0) + c.x i * c.d l (c.d i r) := by
      intro i
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, c.d_x, mul_ite, mul_one, mul_zero]
    rw [hr', map_sub, map_sum]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [sub_add_cancel_left]
    exact neg_mem (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hx i))
  have h2 : r' ∈ maximalIdeal R ^ 2 := by
    refine mem_sq_of_tmul_eq_zero hr'm ?_
    rw [c.kD_eq_sum r', tmul_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← TensorProduct.smul_tmul]
    rw [show (c.d l r' • (1 : ResidueField R)) = 0 from by
      rw [Algebra.smul_def, mul_one]; exact (residue_eq_zero_iff _).2 (hd l)]
    rw [zero_tmul]
  have : r = r' + ∑ i, c.d i r * c.x i := by rw [hr']; ring
  rw [this]
  exact add_mem (Submodule.mem_sup_right h2) (Submodule.mem_sup_left (Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)))

/-- A chart whose functions lie in `𝔪` is centred; `PolyIndNoeth` replaces `𝔪.FG`. -/
theorem isCentred_of_mem_N [Algebra.FormallySmooth ℚ R]
    [Algebra.FormallySmooth ℚ (ResidueField R)] [hN : Fact (PolyIndNoeth R)]
    (hx : ∀ i, c.x i ∈ maximalIdeal R) : c.IsCentred :=
  le_antisymm
    (hN.out.le_of_le_sup_sq (fun a ha => isUnit_one_sub_self_of_mem_nonunits a ha)
      (le_span_sup_sq hx))
    ((Ideal.span_le).2 (by rintro _ ⟨i, rfl⟩; exact hx i))

/-- **Recentring**, with `PolyIndNoeth` instead of `𝔪.FG`. -/
theorem exists_centred_N [Algebra.FormallySmooth ℚ R]
    [Algebra.FormallySmooth ℚ (ResidueField R)] [Algebra.IsIntegral ℚ (ResidueField R)]
    [Fact (PolyIndNoeth R)] (c : Chart R n) :
    ∃ c' : Chart R n, c'.IsCentred ∧ ∀ i, c.x i ∈ maximalIdeal R → c'.x i = c.x i := by
  classical
  set P : Fin n → ℚ[X] := fun i => minpoly ℚ (residue R (c.x i)) with hP
  set y : Fin n → R := fun i => aeval (c.x i) (P i) with hy
  have hsep : ∀ i, (P i).Separable := fun i =>
    Algebra.IsSeparable.isSeparable ℚ (residue R (c.x i))
  have hmap : ∀ (a : R) (p : ℚ[X]), residue R (aeval a p) = aeval (residue R a) p := fun a p =>
    (Polynomial.aeval_algebraMap_apply (B := ResidueField R) a p).symm
  have hres : ∀ i, residue R (aeval (c.x i) (derivative (P i))) ≠ 0 := by
    intro i
    rw [hmap]
    exact (hsep i).aeval_derivative_ne_zero (minpoly.aeval ℚ _)
  have hjac : c.jac y = Matrix.diagonal fun j => aeval (c.x j) (derivative (P j)) := by
    ext i j
    simp only [jac, Matrix.of_apply, hy, Derivation.map_aeval, c.d_x, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  have hdet : IsUnit (c.jac y).det := by
    rw [hjac, Matrix.det_diagonal, IsUnit.prod_univ_iff]
    intro j
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff]; exact hres j
  refine ⟨c.change y hdet, isCentred_of_mem_N fun i => ?_, fun i hi => ?_⟩
  · rw [change_x, ← residue_eq_zero_iff, hy]
    simp only
    rw [hmap]
    exact minpoly.aeval ℚ _
  · rw [change_x, hy]
    simp only [hP, (residue_eq_zero_iff _).2 hi, minpoly.zero, aeval_X]

end Chart

end BezoutCounterexample.Principalization
