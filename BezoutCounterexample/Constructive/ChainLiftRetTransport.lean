import Mathlib
import BezoutCounterexample.Constructive.ChainLiftConormal

/-!
# Transport of conormal retraction data along a local isomorphism (Task B, Rees layer S2)

A *target* presentation `G` (variables `Z`, `N` of them) and a *model* presentation `H` (variables
`W`, `M` of them), related by polynomial substitutions (in the Rees layer the model has the target
variables plus graph variables `u' = P̃(Z)`, so both maps are polynomial):

* `φ : Z → ℤ[W]` with `d_W · (g ∘ φ) ∈ (H)` for `g ∈ G` (the target relations hold in the model on
  `D(d_W)`: the local kernel equality);
* `ψ : W → ℤ[Z]` with `ψ(H) ⊆ (G)` (the model relations hold in the target);
* the round trip `Z_v - ψ(φ_v) ∈ (G)`.

Retraction data `ConormalRet H D' a'` of the model give retraction data of the target with
multiplier `ψ(D' d_W²)` (`conormalRet_transport`), by the formula
`a_v = ψ(D' d_W²) (Z_v - ψ φ_v) + Σ_u ψ(∂_u φ_v) ψ(d_W² a'_u)`. The check is a first-order Taylor
expansion (`taylor0`, `taylor1`) and the chain rule (`pderiv_aeval`), modulo `(G)²`.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

section Taylor

variable {σ : Type*} [Fintype σ] {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (x x' : σ → S)

/-- The ideal of the differences `x_v - x'_v`. -/
def diffIdeal : Ideal S := Ideal.span (Set.range fun v => x v - x' v)

lemma sub_mem_diffIdeal (v : σ) : x v - x' v ∈ diffIdeal x x' := Ideal.subset_span ⟨v, rfl⟩

/-- **Taylor, order 0**: `p(x) - p(x') ∈ (x - x')`. -/
lemma taylor0 (p : MvPolynomial σ R) : aeval x p - aeval x' p ∈ diffIdeal x x' := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]; exact Ideal.add_mem _ hp hq
  | mul_X p v hp =>
    have : aeval x (p * X v) - aeval x' (p * X v) =
        (aeval x p - aeval x' p) * x v + aeval x' p * (x v - x' v) := by
      simp only [map_mul, aeval_X]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp)
      (Ideal.mul_mem_left _ _ (sub_mem_diffIdeal x x' v))

/-- **Taylor, order 1**: `p(x) - p(x') - Σ_v ∂_v p(x') (x_v - x'_v) ∈ (x - x')²`. -/
lemma taylor1 [DecidableEq σ] (p : MvPolynomial σ R) :
    aeval x p - aeval x' p - ∑ v, aeval x' (pderiv v p) * (x v - x' v) ∈ diffIdeal x x' ^ 2 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have : aeval x (p + q) - aeval x' (p + q) - ∑ v, aeval x' (pderiv v (p + q)) * (x v - x' v) =
        (aeval x p - aeval x' p - ∑ v, aeval x' (pderiv v p) * (x v - x' v)) +
          (aeval x q - aeval x' q - ∑ v, aeval x' (pderiv v q) * (x v - x' v)) := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]; ring
    rw [this]; exact Ideal.add_mem _ hp hq
  | mul_X p w hp =>
    have hd : ∀ v, pderiv v (p * X w) = pderiv v p * X w + p * pderiv v (X w) := fun v => by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    have hsum : ∑ v, aeval x' (pderiv v (p * X w)) * (x v - x' v) =
        x' w * ∑ v, aeval x' (pderiv v p) * (x v - x' v) + aeval x' p * (x w - x' w) := by
      simp only [hd, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun v _ => by ring
      · rw [Finset.sum_eq_single w]
        · simp
        · intro v _ hv; simp [pderiv_X, Pi.single_apply, hv]
        · intro h; exact absurd (Finset.mem_univ w) h
    have : aeval x (p * X w) - aeval x' (p * X w) - ∑ v, aeval x' (pderiv v (p * X w)) * (x v - x' v) =
        (aeval x p - aeval x' p) * (x w - x' w) +
          x' w * (aeval x p - aeval x' p - ∑ v, aeval x' (pderiv v p) * (x v - x' v)) := by
      rw [hsum]; simp only [map_mul, aeval_X]; ring
    rw [this, pow_two]
    exact Ideal.add_mem _ (Ideal.mul_mem_mul (taylor0 x x' p) (sub_mem_diffIdeal x x' w))
      (Ideal.mul_mem_left _ _ (by rw [← pow_two]; exact hp))

end Taylor

section Chain

variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq τ]

/-- **The chain rule** for `aeval` between polynomial rings. -/
lemma pderiv_aeval (φ : σ → MvPolynomial τ ℤ) (u : τ) (g : MvPolynomial σ ℤ) :
    pderiv u (aeval φ g) = ∑ v, aeval φ (pderiv v g) * pderiv u (φ v) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p w hp =>
    have hd : ∀ v, pderiv v (p * X w) = pderiv v p * X w + p * pderiv v (X w) := fun v => by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hp, hd, map_add, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun v _ => by ring
    · rw [Finset.sum_eq_single w]
      · simp
      · intro v _ hv; simp [pderiv_X, Pi.single_apply, hv]
      · intro h; exact absurd (Finset.mem_univ w) h

end Chain

/-- Retraction data extend from the generators to the whole ideal. -/
lemma ConormalRet.mem {N : ℕ} {H : List (MvPolynomial (Fin N) ℤ)} {D : MvPolynomial (Fin N) ℤ}
    {a : Fin N → MvPolynomial (Fin N) ℤ} (h : ConormalRet H D a) {F : MvPolynomial (Fin N) ℤ}
    (hF : F ∈ lspan H) : D * F - ∑ k, pderiv k F * a k ∈ lspan H ^ 2 := by
  have hsq : ∀ x ∈ lspan H, ∀ z ∈ lspan H, x * z ∈ lspan H ^ 2 := fun x hx z hz => by
    rw [pow_two]; exact Ideal.mul_mem_mul hx hz
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := List.get_of_mem hx
    exact h.2 j
  | zero => simp
  | add x z _ _ hx hz =>
    have : D * (x + z) - ∑ k, pderiv k (x + z) * a k =
        (D * x - ∑ k, pderiv k x * a k) + (D * z - ∑ k, pderiv k z * a k) := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]; ring
    rw [this]; exact Ideal.add_mem _ hx hz
  | smul c x hxI hx =>
    have hd : ∀ k, pderiv k (c * x) * a k = c * (pderiv k x * a k) + x * (pderiv k c * a k) :=
      fun k => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    have : D * (c • x) - ∑ k, pderiv k (c • x) * a k =
        c * (D * x - ∑ k, pderiv k x * a k) - ∑ k, x * (pderiv k c * a k) := by
      rw [smul_eq_mul, Finset.sum_congr rfl (fun k _ => hd k), Finset.sum_add_distrib,
        ← Finset.mul_sum, mul_sub]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hx)
      (Ideal.sum_mem _ fun k _ => hsq _ hxI _ (Ideal.mul_mem_left _ _ (h.1 k)))

section Transport

variable {N M : ℕ} (G : List (MvPolynomial (Fin N) ℤ)) (H : List (MvPolynomial (Fin M) ℤ))
  (φ : Fin N → MvPolynomial (Fin M) ℤ) (ψ : Fin M → MvPolynomial (Fin N) ℤ)
  (dW : MvPolynomial (Fin M) ℤ)

lemma aeval_X_self (p : MvPolynomial (Fin N) ℤ) : aeval (fun v => (X v : MvPolynomial (Fin N) ℤ)) p = p := by
  simp

/-- **Transport of conormal retraction data** along polynomial substitutions. -/
theorem conormalRet_transport
    (hφ : ∀ g ∈ G, dW * aeval φ g ∈ lspan H)
    (hψ : ∀ h ∈ H, aeval ψ h ∈ lspan G)
    (hround : ∀ v, X v - aeval ψ (φ v) ∈ lspan G)
    {D' : MvPolynomial (Fin M) ℤ} {a' : Fin M → MvPolynomial (Fin M) ℤ}
    (hret : ConormalRet H D' a') :
    ConormalRet G (aeval ψ (D' * dW ^ 2)) (fun v => aeval ψ (D' * dW ^ 2) * (X v - aeval ψ (φ v)) +
      ∑ u, aeval ψ (pderiv u (φ v)) * aeval ψ (dW ^ 2 * a' u)) := by
  set I := lspan G
  set x : Fin N → MvPolynomial (Fin N) ℤ := fun v => X v
  set x' : Fin N → MvPolynomial (Fin N) ℤ := fun v => aeval ψ (φ v)
  have hJ : diffIdeal x x' ≤ I := by
    rw [diffIdeal, Ideal.span_le]; rintro _ ⟨v, rfl⟩; exact hround v
  have hJ2 : diffIdeal x x' ^ 2 ≤ I ^ 2 := Ideal.pow_right_mono hJ 2
  have hψI : ∀ F ∈ lspan H, aeval ψ F ∈ I := by
    intro F hF
    have : (lspan H).map (aeval ψ : MvPolynomial (Fin M) ℤ →ₐ[ℤ] _).toRingHom ≤ I := by
      rw [Ideal.map_le_iff_le_comap, lspan, Ideal.span_le]
      intro h hh; exact hψ h hh
    exact this (Ideal.mem_map_of_mem _ hF)
  have hψI2 : ∀ F ∈ lspan H ^ 2, aeval ψ F ∈ I ^ 2 := by
    intro F hF
    have : (lspan H ^ 2).map (aeval ψ : MvPolynomial (Fin M) ℤ →ₐ[ℤ] _).toRingHom ≤ I ^ 2 := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (by
        rw [Ideal.map_le_iff_le_comap, lspan, Ideal.span_le]
        intro h hh; exact hψ h hh) 2
    exact this (Ideal.mem_map_of_mem _ hF)
  have hsq : ∀ y ∈ I, ∀ z ∈ I, y * z ∈ I ^ 2 := fun y hy z hz => by
    rw [pow_two]; exact Ideal.mul_mem_mul hy hz
  have hsqH : ∀ y ∈ lspan H, ∀ z ∈ lspan H, y * z ∈ lspan H ^ 2 := fun y hy z hz => by
    rw [pow_two]; exact Ideal.mul_mem_mul hy hz
  have hcomp : ∀ p : MvPolynomial (Fin N) ℤ, aeval ψ (aeval φ p) = aeval x' p := fun p => by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hx : ∀ p : MvPolynomial (Fin N) ℤ, aeval x p = p := aeval_X_self
  refine ⟨fun v => Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hround v))
    (Ideal.sum_mem _ fun u _ => Ideal.mul_mem_left _ _
      (hψI _ (Ideal.mul_mem_left _ _ (hret.1 u)))), fun j => ?_⟩
  set g := G.get j
  set δ := aeval ψ (D' * dW ^ 2)
  -- (T1) the first sum
  have hT1' : g - aeval ψ (aeval φ g) - ∑ v, pderiv v g * (x v - x' v) ∈ I ^ 2 := by
    have hT1 := taylor1 x x' g
    rw [hx, ← hcomp] at hT1
    have hdiff : ∑ v, aeval x' (pderiv v g) * (x v - x' v) - ∑ v, pderiv v g * (x v - x' v) ∈
        I ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun v _ => ?_
      rw [← sub_mul]
      have := (Ideal.neg_mem_iff _).2 (taylor0 x x' (pderiv v g))
      rw [neg_sub, hx] at this
      exact hJ2 (by rw [pow_two]; exact Ideal.mul_mem_mul this (sub_mem_diffIdeal x x' v))
    have := Ideal.add_mem _ (hJ2 hT1) hdiff
    convert this using 1; ring
  -- (T2) the second sum, through the chain rule
  have hT2 : ∑ v, pderiv v g * ∑ u, aeval ψ (pderiv u (φ v)) * aeval ψ (dW ^ 2 * a' u) -
      aeval ψ (∑ u, dW ^ 2 * pderiv u (aeval φ g) * a' u) ∈ I ^ 2 := by
    have hch : aeval ψ (∑ u, dW ^ 2 * pderiv u (aeval φ g) * a' u) =
        ∑ v, aeval x' (pderiv v g) * ∑ u, aeval ψ (pderiv u (φ v)) * aeval ψ (dW ^ 2 * a' u) := by
      simp only [pderiv_aeval, map_sum, map_mul, hcomp, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by ring
    rw [hch, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun v _ => ?_
    rw [← sub_mul]
    refine hsq _ ?_ _ (Ideal.sum_mem _ fun u _ => Ideal.mul_mem_left _ _
      (hψI _ (Ideal.mul_mem_left _ _ (hret.1 u))))
    have := taylor0 x x' (pderiv v g)
    rw [hx] at this
    exact hJ this
  -- (T3) the model retraction on `d_W · (g ∘ φ)`
  have hT3 : δ * aeval ψ (aeval φ g) - aeval ψ (∑ u, dW ^ 2 * pderiv u (aeval φ g) * a' u) ∈
      I ^ 2 := by
    have hF := hφ g (List.get_mem G j)
    have h1 := Ideal.mul_mem_left _ dW (hret.mem hF)
    have h2 : ∑ u, dW * aeval φ g * (pderiv u dW * a' u) ∈ lspan H ^ 2 :=
      Ideal.sum_mem _ fun u _ => hsqH _ hF _ (Ideal.mul_mem_left _ _ (hret.1 u))
    have h3 := Ideal.add_mem _ h1 h2
    have e : dW * (D' * (dW * aeval φ g) - ∑ k, pderiv k (dW * aeval φ g) * a' k) +
        ∑ u, dW * aeval φ g * (pderiv u dW * a' u) =
        D' * dW ^ 2 * aeval φ g - ∑ u, dW ^ 2 * pderiv u (aeval φ g) * a' u := by
      have hk : ∀ k, pderiv k (dW * aeval φ g) * a' k =
          dW * (pderiv k (aeval φ g) * a' k) + aeval φ g * (pderiv k dW * a' k) := fun k => by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
      have s1 : ∑ u, dW ^ 2 * pderiv u (aeval φ g) * a' u =
          dW ^ 2 * ∑ u, pderiv u (aeval φ g) * a' u := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
      have s2 : ∑ u, dW * aeval φ g * (pderiv u dW * a' u) =
          dW * aeval φ g * ∑ u, pderiv u dW * a' u := by rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, s1, s2]
      ring
    rw [e] at h3
    have := hψI2 _ h3
    simpa only [map_sub, map_mul, δ] using this
  have hfinal := Ideal.add_mem _ (Ideal.mul_mem_left _ δ hT1')
    (Ideal.add_mem _ hT3 ((Ideal.neg_mem_iff _).2 hT2))
  convert hfinal using 1
  simp only [x, x', mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_sub,
    Finset.sum_sub_distrib, mul_assoc]
  ring

end Transport

end BezoutCounterexample.Constructive
