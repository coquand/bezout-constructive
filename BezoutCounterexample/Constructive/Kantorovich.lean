import Mathlib
import BezoutCounterexample.Constructive.Attr

/-!
# Quantitative inverse function theorem, chord form (`bezout-positive.tex`, Prop. 2.1)

Chain lifting needs exact real points of a smooth variety with prescribed chart coordinates near
a given approximate point. With a fixed approximate inverse `M` of the Jacobian, the chord map
`Φ x = x - M (F x - y)` is a contraction of a closed ball when

* (contraction) `2 ‖Φ x - Φ x'‖ ≤ ‖x - x'‖` on the ball, and
* (small residual) `2 ‖M (F x₀ - y)‖ ≤ r`.

Then `Φ` has a fixed point in the ball, i.e. `M (F x - y) = 0`, and `F x = y` if `M` is
injective (`exists_solution_chord`). All constants are explicit; no division or order decision
on `ℝ` is used in the statements. The fixed point theorem itself is the one trusted primitive
(`@[cprim] exists_fixedPoint_half`): Banach's theorem with rate `1/2` is constructive (the
iterates form an explicit Cauchy sequence, `‖xₙ - x‖ ≤ 2⁻ⁿ r`), while Mathlib's proof is not.
-/

namespace BezoutCounterexample.Constructive

open Metric

/-- **Banach's fixed point theorem with rate `1/2`** on a closed ball of a complete normed space
(trusted primitive: constructively valid statement, classical Mathlib proof). -/
@[cprim]
theorem exists_fixedPoint_half {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (Φ : E → E) (x₀ : E) (r : ℝ) (hr : 0 ≤ r)
    (hmaps : ∀ x ∈ closedBall x₀ r, Φ x ∈ closedBall x₀ r)
    (hcon : ∀ x ∈ closedBall x₀ r, ∀ x' ∈ closedBall x₀ r, 2 * ‖Φ x - Φ x'‖ ≤ ‖x - x'‖) :
    ∃ x ∈ closedBall x₀ r, Φ x = x := by
  classical
  let B := closedBall x₀ r
  have hcl : IsClosed B := isClosed_closedBall
  have : CompleteSpace B := hcl.completeSpace_coe
  have : Nonempty B := ⟨⟨x₀, mem_closedBall_self hr⟩⟩
  let f : B → B := fun x => ⟨Φ x, hmaps x x.2⟩
  have hK : (2⁻¹ : NNReal) < 1 := by norm_num
  have hlip : LipschitzWith 2⁻¹ f := by
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    have h := hcon x x.2 x' x'.2
    simp only [Subtype.dist_eq, dist_eq_norm, f, NNReal.coe_inv, NNReal.coe_ofNat]
    linarith
  obtain ⟨x, hx⟩ : ∃ x, f x = x := ⟨_, (ContractingWith.fixedPoint_isFixedPt ⟨hK, hlip⟩)⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

/-- **Solutions by the chord method.** -/
theorem exists_solution_chord {E F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (F : E → F') (M : F' →L[ℝ] E) (x₀ : E) (y : F') (r : ℝ) (hr : 0 ≤ r)
    (hcon : ∀ x ∈ closedBall x₀ r, ∀ x' ∈ closedBall x₀ r,
      2 * ‖(x - M (F x - y)) - (x' - M (F x' - y))‖ ≤ ‖x - x'‖)
    (hres : 2 * ‖M (F x₀ - y)‖ ≤ r) :
    ∃ x ∈ closedBall x₀ r, M (F x - y) = 0 := by
  set Φ : E → E := fun x => x - M (F x - y)
  have hmaps : ∀ x ∈ closedBall x₀ r, Φ x ∈ closedBall x₀ r := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    have h1 := hcon x (by rwa [mem_closedBall, dist_eq_norm]) x₀ (mem_closedBall_self hr)
    have h2 : ‖Φ x - x₀‖ ≤ ‖Φ x - Φ x₀‖ + ‖Φ x₀ - x₀‖ := by
      calc ‖Φ x - x₀‖ = ‖(Φ x - Φ x₀) + (Φ x₀ - x₀)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h3 : Φ x₀ - x₀ = -M (F x₀ - y) := by simp [Φ]
    rw [h3, norm_neg] at h2
    linarith
  obtain ⟨x, hx, hfix⟩ := exists_fixedPoint_half Φ x₀ r hr hmaps hcon
  refine ⟨x, hx, ?_⟩
  have : x - M (F x - y) = x := hfix
  simpa using this

/-- With an injective approximate inverse, the fixed point solves `F x = y`. -/
theorem exists_solution_chord_inj {E F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (F : E → F') (M : F' →L[ℝ] E) (hM : Function.Injective M) (x₀ : E) (y : F') (r : ℝ)
    (hr : 0 ≤ r)
    (hcon : ∀ x ∈ closedBall x₀ r, ∀ x' ∈ closedBall x₀ r,
      2 * ‖(x - M (F x - y)) - (x' - M (F x' - y))‖ ≤ ‖x - x'‖)
    (hres : 2 * ‖M (F x₀ - y)‖ ≤ r) :
    ∃ x ∈ closedBall x₀ r, F x = y := by
  obtain ⟨x, hx, h0⟩ := exists_solution_chord F M x₀ y r hr hcon hres
  exact ⟨x, hx, sub_eq_zero.1 (hM (by rw [h0, map_zero]))⟩

/-- **The contraction condition from a derivative bound** (mean value inequality on the convex
ball): if `‖id - M ∘ DF x‖ ≤ c` with `2 c ≤ 1`, the chord map contracts with rate `1/2`. -/
theorem chord_contraction {E F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (F : E → F') (DF : E → E →L[ℝ] F') (M : F' →L[ℝ] E) (x₀ : E) (y : F') (r c : ℝ)
    (hF : ∀ x ∈ closedBall x₀ r, HasFDerivAt F (DF x) x)
    (hd : ∀ x ∈ closedBall x₀ r, ‖ContinuousLinearMap.id ℝ E - M.comp (DF x)‖ ≤ c)
    (hc : 2 * c ≤ 1) :
    ∀ x ∈ closedBall x₀ r, ∀ x' ∈ closedBall x₀ r,
      2 * ‖(x - M (F x - y)) - (x' - M (F x' - y))‖ ≤ ‖x - x'‖ := by
  intro x hx x' hx'
  set Φ : E → E := fun z => z - M (F z - y)
  have hΦ : ∀ z ∈ closedBall x₀ r,
      HasFDerivWithinAt Φ (ContinuousLinearMap.id ℝ E - M.comp (DF z)) (closedBall x₀ r) z := by
    intro z hz
    have h1 : HasFDerivAt (fun z => F z - y) (DF z) z := (hF z hz).sub_const y
    have h2 := (M.hasFDerivAt.comp z h1)
    exact ((hasFDerivAt_id z).sub h2).hasFDerivWithinAt
  have hmv := (convex_closedBall x₀ r).norm_image_sub_le_of_norm_hasFDerivWithin_le hΦ hd hx' hx
  have hn : 0 ≤ ‖x - x'‖ := norm_nonneg _
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hd x hx)
  calc 2 * ‖Φ x - Φ x'‖ ≤ 2 * (c * ‖x - x'‖) := by
        exact mul_le_mul_of_nonneg_left hmv (by norm_num)
    _ = (2 * c) * ‖x - x'‖ := by ring
    _ ≤ 1 * ‖x - x'‖ := mul_le_mul_of_nonneg_right hc hn
    _ = ‖x - x'‖ := one_mul _

/-- **Quantitative inverse function theorem** (chord form): derivative bound plus small
residual give an exact solution in the ball. -/
theorem exists_solution_of_deriv {E F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (F : E → F') (DF : E → E →L[ℝ] F') (M : F' →L[ℝ] E) (hM : Function.Injective M)
    (x₀ : E) (y : F') (r c : ℝ) (hr : 0 ≤ r)
    (hF : ∀ x ∈ closedBall x₀ r, HasFDerivAt F (DF x) x)
    (hd : ∀ x ∈ closedBall x₀ r, ‖ContinuousLinearMap.id ℝ E - M.comp (DF x)‖ ≤ c)
    (hc : 2 * c ≤ 1) (hres : 2 * ‖M (F x₀ - y)‖ ≤ r) :
    ∃ x ∈ closedBall x₀ r, F x = y :=
  exists_solution_chord_inj F M hM x₀ y r hr (chord_contraction F DF M x₀ y r c hF hd hc) hres

end BezoutCounterexample.Constructive
