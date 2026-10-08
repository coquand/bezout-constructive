import Mathlib
import BezoutCounterexample.Constructive.ChainLiftMinorPoly

/-!
# Conormal injectivity from retraction data

`ConormalRet G D a`: polynomials `a_k ∈ (G)` (lifts of the images of `dY_k` under a retraction of
`(G)/(G)² → Ω ⊗ ℤ[Y]/(G)`) with `D gⱼ ≡ Σ_k ∂_k gⱼ · a_k` modulo `(G)²` for every relation.
This is finite data, checkable by ideal membership. `conormalInj_of_ret`: it gives
`ConormalInj G D` (`D f ∈ (G)²` whenever `f` and all `∂_k f` lie in `(G)`): writing
`f = Σ bⱼ gⱼ`, `D f - Σ_k ∂_k f · a_k = Σ bⱼ (D gⱼ - Σ_k ∂_k gⱼ a_k) - Σ_{j,k} ∂_k bⱼ · gⱼ a_k`.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {N : ℕ}

/-- **Retraction data** for the conormal sequence of `G`, with integer constant `D`. -/
def ConormalRet (G : List (MvPolynomial (Fin N) ℤ)) (D : MvPolynomial (Fin N) ℤ)
    (a : Fin N → MvPolynomial (Fin N) ℤ) : Prop :=
  (∀ k, a k ∈ lspan G) ∧
    ∀ j : Fin G.length, D * G.get j - ∑ k, pderiv k (G.get j) * a k ∈ lspan G ^ 2

/-- **Conormal injectivity from retraction data.** -/
theorem conormalInj_of_ret {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}
    {D : MvPolynomial (Fin (m + n)) ℤ} {a : Fin (m + n) → MvPolynomial (Fin (m + n)) ℤ}
    (h : ConormalRet G D a) : ConormalInj G D := by
  intro f hf hdf
  obtain ⟨ha, hret⟩ := h
  rw [lspan_eq_span_range, Ideal.mem_span_range_iff_exists_fun] at hf
  obtain ⟨b, rfl⟩ := hf
  have hsq : ∀ x ∈ lspan G, ∀ y ∈ lspan G, x * y ∈ lspan G ^ 2 := fun x hx y hy => by
    rw [pow_two]; exact Ideal.mul_mem_mul hx hy
  -- `D f - Σ_k ∂_k f a_k ∈ (G)²`
  have key : D * ∑ j, b j * G.get j - ∑ k, pderiv k (∑ j, b j * G.get j) * a k =
      ∑ j, b j * (D * G.get j - ∑ k, pderiv k (G.get j) * a k) -
        ∑ k, ∑ j, pderiv k (b j) * (G.get j * a k) := by
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
      mul_sub, Finset.sum_sub_distrib, add_mul]
    rw [Finset.sum_comm (f := fun x i => b x * ((pderiv i) (G.get x) * a i))]
    simp only [Finset.sum_add_distrib]
    have e1 : ∑ i, D * (b i * G.get i) = ∑ x, b x * (D * G.get x) :=
      Finset.sum_congr rfl fun _ _ => by ring
    have e2 : ∑ x, ∑ x_1, b x_1 * pderiv x (G.get x_1) * a x =
        ∑ y, ∑ x, b x * (pderiv y (G.get x) * a y) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have e3 : ∑ x, ∑ x_1, G.get x_1 * pderiv x (b x_1) * a x =
        ∑ k, ∑ j, pderiv k (b j) * (G.get j * a k) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e1, e2, e3]
    ring
  have h1 : D * ∑ j, b j * G.get j - ∑ k, pderiv k (∑ j, b j * G.get j) * a k ∈ lspan G ^ 2 := by
    rw [key]
    refine Ideal.sub_mem _ (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hret j)) ?_
    exact Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun j _ =>
      Ideal.mul_mem_left _ _ (hsq _ (get_mem_lspan G j) _ (ha k))
  have h2 : ∑ k, pderiv k (∑ j, b j * G.get j) * a k ∈ lspan G ^ 2 :=
    Ideal.sum_mem _ fun k _ => hsq _ (hdf k) _ (ha k)
  have := Ideal.add_mem _ h1 h2
  rwa [sub_add_cancel] at this

end BezoutCounterexample.Constructive
