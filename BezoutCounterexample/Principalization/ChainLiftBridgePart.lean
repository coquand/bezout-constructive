import Mathlib
import BezoutCounterexample.Principalization.ChainLiftBridgeChart
import BezoutCounterexample.Principalization.ChainLiftBridgeCover

/-!
# The Jacobian determinants of a chart cover its head locus (bridge (d), chart part)

In the setting of `ChainLiftBridgeChart` (`S` a localization of `A₀ = ℚ[Y] ⧸ (G₀)` with a chart
`c`), with numerators `c.x j · gˢ = p_j` and head scalings `D_q`, the coordinates
`y^τ = (D_q p_q)_{q < kc} ++ (Y_{τ t})_t` (one family per `(n - kc)`-subset `τ` of the variables)
satisfy `Σ_τ r_τ det J_τ = Π_q D_q · g^{s kc} + z` with `z ∈ (x_head)` (`partition_chart`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open scoped Matrix

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {N : ℕ} (G₀ : List (MvPolynomial (Fin N) ℚ))
  {S : Type*} [CommRing S] [Algebra ℚ S] [Algebra (Quo G₀) S] [IsScalarTower ℚ (Quo G₀) S]
  {n : ℕ} (c : Chart S n)

/-- The coordinates of the `τ`-chart: scaled head numerators, then the variables `Y_τ`. -/
def yTau {kc : ℕ} (hk : kc ≤ n) (p : Fin n → MvPolynomial (Fin N) ℚ) (Dh : Fin kc → ℚ)
    (τ : RowIdx N (n - kc)) (j : Fin n) : MvPolynomial (Fin N) ℚ :=
  if h : (j : ℕ) < kc then C (Dh ⟨j, h⟩) * p j else X (τ.enum ⟨j - kc, by omega⟩)

lemma yTau_head {kc : ℕ} (hk : kc ≤ n) (p : Fin n → MvPolynomial (Fin N) ℚ) (Dh : Fin kc → ℚ)
    (τ : RowIdx N (n - kc)) (q : Fin kc) :
    yTau hk p Dh τ (headIdx hk q) = C (Dh q) * p (headIdx hk q) := by
  simp [yTau, headIdx]

lemma yTau_tail {kc : ℕ} (hk : kc ≤ n) (p : Fin n → MvPolynomial (Fin N) ℚ) (Dh : Fin kc → ℚ)
    (τ : RowIdx N (n - kc)) (t : Fin (n - kc)) :
    yTau hk p Dh τ (tailIdx hk t) = X (τ.enum t) := by
  have : ¬ ((tailIdx hk t : Fin n) : ℕ) < kc := by simp [tailIdx]
  simp only [yTau, this, dite_false]
  congr 2
  ext; simp [tailIdx]

/-- **The `τ`-Jacobians cover the head locus.** -/
theorem partition_chart {kc : ℕ} (hk : kc ≤ n) (gp : MvPolynomial (Fin N) ℚ)
    (s : ℕ) (u : S) (hu : u * toS G₀ gp ^ s = 1) (p : Fin n → MvPolynomial (Fin N) ℚ)
    (hp : ∀ j, c.x j * toS G₀ gp ^ s = toS G₀ (p j)) (Dh : Fin kc → ℚ) :
    ∃ (r : RowIdx N (n - kc) → S) (z : S), z ∈ Ideal.span (Set.range fun q => c.x (headIdx hk q)) ∧
      ∑ τ, r τ * (Jm G₀ c (yTau hk p Dh τ)).det =
        (∏ q, algebraMap ℚ S (Dh q) * toS G₀ gp ^ s) + z := by
  -- the left inverse `U` of `V⁰`, by the chain rule
  set U : Matrix (Fin n) (Fin N) S := Matrix.of fun j k =>
    u * (toS G₀ (pderiv k (p j)) - c.x j * toS G₀ (pderiv k (gp ^ s)))
  have hgs : toS (S := S) G₀ (gp ^ s) = toS G₀ gp ^ s := by
    rw [← toSHom_apply, map_pow]; rfl
  have hUV : U * V0 G₀ c = 1 := by
    ext j l
    have h1 := derivation_toS G₀ (c.d l) (p j)
    have h2 := derivation_toS G₀ (c.d l) (gp ^ s)
    have h3 : c.d l (toS G₀ (p j)) = c.x j * c.d l (toS G₀ (gp ^ s)) +
        toS G₀ gp ^ s * c.d l (c.x j) := by
      rw [← hp j, Derivation.leibniz, hgs, smul_eq_mul, smul_eq_mul]
    simp only [U, V0, Matrix.mul_apply, Matrix.of_apply]
    have : ∑ k, u * (toS G₀ (pderiv k (p j)) - c.x j * toS G₀ (pderiv k (gp ^ s))) *
        c.d l (toS G₀ (X k)) = u * (c.d l (toS G₀ (p j)) - c.x j * c.d l (toS G₀ (gp ^ s))) := by
      rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, h3, c.d_x, Matrix.one_apply]
    have : u * (c.x j * c.d l (toS G₀ (gp ^ s)) + toS G₀ gp ^ s * (if l = j then 1 else 0) -
        c.x j * c.d l (toS G₀ (gp ^ s))) = (u * toS G₀ gp ^ s) * (if l = j then 1 else 0) := by
      ring
    rw [this, hu, one_mul]
    by_cases h : l = j
    · subst h; simp
    · simp [h, Ne.symm h]
  obtain ⟨r, hr⟩ := tail_minor_cover hk (V0 G₀ c) U hUV
  set x : Fin kc → S := fun q => c.x (headIdx hk q)
  set cd : Fin kc → S := fun q => algebraMap ℚ S (Dh q) * toS G₀ gp ^ s
  have hz : ∀ τ : RowIdx N (n - kc), (Jm G₀ c (yTau hk p Dh τ)).det -
      (∏ q, cd q) * ((V0 G₀ c).submatrix τ.enum (tailIdx hk)).det ∈ Ideal.span (Set.range x) := by
    intro τ
    refine det_mod_head hk _ x cd ((V0 G₀ c).submatrix τ.enum id) (fun l q => ?_) (fun l t => ?_)
    · simp only [Jm, Matrix.of_apply, yTau_head]
      rw [← toSHom_apply, map_mul, toSHom_apply, toSHom_apply]
      have hC : toS (S := S) G₀ (C (Dh q)) = algebraMap ℚ S (Dh q) := toS_C G₀ (Dh q)
      rw [hC, ← Algebra.smul_def, Derivation.map_smul, ← hp, Derivation.leibniz, c.d_x,
        smul_eq_mul, smul_eq_mul, Algebra.smul_def]
      have : algebraMap ℚ S (Dh q) * (c.x (headIdx hk q) * c.d l (toS G₀ gp ^ s) +
          toS G₀ gp ^ s * (if l = headIdx hk q then 1 else 0)) -
          (if l = headIdx hk q then cd q else 0) =
          (algebraMap ℚ S (Dh q) * c.d l (toS G₀ gp ^ s)) * x q := by
        by_cases h : l = headIdx hk q
        · simp [h, cd, x]; ring
        · simp [h, x]; ring
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)
    · simp only [Jm, Matrix.of_apply, yTau_tail, V0, Matrix.submatrix_apply, id]
  refine ⟨r, ∑ τ, r τ * ((Jm G₀ c (yTau hk p Dh τ)).det -
      (∏ q, cd q) * ((V0 G₀ c).submatrix τ.enum (tailIdx hk)).det),
    Ideal.sum_mem _ fun τ _ => Ideal.mul_mem_left _ _ (hz τ), ?_⟩
  have : ∑ τ, r τ * (Jm G₀ c (yTau hk p Dh τ)).det = (∏ q, cd q) *
      ∑ τ, r τ * ((V0 G₀ c).submatrix τ.enum (tailIdx hk)).det +
      ∑ τ, r τ * ((Jm G₀ c (yTau hk p Dh τ)).det -
        (∏ q, cd q) * ((V0 G₀ c).submatrix τ.enum (tailIdx hk)).det) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [this, hr, mul_one]

end BezoutCounterexample.Principalization
