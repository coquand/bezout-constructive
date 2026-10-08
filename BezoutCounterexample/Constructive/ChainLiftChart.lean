import Mathlib
import BezoutCounterexample.Constructive.Kantorovich
import BezoutCounterexample.Constructive.ChainLiftPush

/-!
# Sources for the fields of `PushData` (`~/COLL/bezout-positive.tex`, §2.2–2.3)

* `chord_lip`, `chord_section`: from the chord contraction of `Kantorovich.lean`, exact
  solutions (`sect`) *and* the Lipschitz inverse (`inj`): two solutions in the ball satisfy
  `‖x - x'‖ ≤ 2 ‖M (F x - F x')‖`. `close_of_norm_le`, `norm_le_of_close`: the sup norm on
  `Fin N → ℝ` against coordinatewise closeness.
* `nu_lo_of_identity` (Lemma 2.3 from `NuBound`): a pure-power identity
  `x_m^{a} = Σ_γ c_γ g^γ` gives `ν ≥ κ^E r^{D}` as soon as `|x_m| ≥ r^{w}`.
* `nu_hi_of_identity`: `gᵢ = Σ_α bᵢα x^α` with `w·α ≥ dᵢ` (`F_t` weighted monomial) gives
  `ν ≤ c' r^{D}` when all `|x_m| ≤ r^{w_m}`, `r ≤ 1`.
* `cover_of_identity`: a partition of unity `1 = b ν + Σⱼ aⱼ hⱼ` with bounded coefficients gives
  the decision `θ ≤ ν ∨ ∃ j, κ ≤ |hⱼ|` (finitely many comparisons with margins).
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

open Metric

/-! ## Kantorovich: section and Lipschitz inverse -/

/-- **Lipschitz inverse from the chord contraction.** -/
theorem chord_lip {E F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] (F : E → F') (M : F' →L[ℝ] E) (x₀ : E) (y : F')
    (r : ℝ) (hcon : ∀ x ∈ closedBall x₀ r, ∀ x' ∈ closedBall x₀ r,
      2 * ‖(x - M (F x - y)) - (x' - M (F x' - y))‖ ≤ ‖x - x'‖)
    {x x' : E} (hx : x ∈ closedBall x₀ r) (hx' : x' ∈ closedBall x₀ r) :
    ‖x - x'‖ ≤ 2 * ‖M (F x - F x')‖ := by
  have e : x - x' = ((x - M (F x - y)) - (x' - M (F x' - y))) + M (F x - F x') := by
    rw [map_sub, map_sub, map_sub]; abel
  have h1 : ‖x - x'‖ ≤ ‖(x - M (F x - y)) - (x' - M (F x' - y))‖ + ‖M (F x - F x')‖ := by
    calc ‖x - x'‖ = ‖((x - M (F x - y)) - (x' - M (F x' - y))) + M (F x - F x')‖ := by rw [← e]
      _ ≤ _ := norm_add_le _ _
  have h2 := hcon x hx x' hx'
  linarith

/-- **Section and Lipschitz inverse** (the fields `sect` and `inj` of `PushData` at one base
point, in a normed space). -/
theorem chord_section {E F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] (F : E → F') (M : F' →L[ℝ] E)
    (hM : Function.Injective M) (x₀ : E) (r : ℝ) (hr : 0 ≤ r)
    (hcon : ∀ x ∈ closedBall x₀ r, ∀ x' ∈ closedBall x₀ r,
      2 * ‖(x - M (F x)) - (x' - M (F x'))‖ ≤ ‖x - x'‖) :
    (∀ y, 2 * ‖M (F x₀ - y)‖ ≤ r → ∃ x ∈ closedBall x₀ r, F x = y) ∧
    (∀ x ∈ closedBall x₀ r, ∀ x' ∈ closedBall x₀ r, ‖x - x'‖ ≤ 2 * ‖M (F x - F x')‖) := by
  -- the contraction does not depend on the target `y`
  have hcon' : ∀ y, ∀ x ∈ closedBall x₀ r, ∀ x' ∈ closedBall x₀ r,
      2 * ‖(x - M (F x - y)) - (x' - M (F x' - y))‖ ≤ ‖x - x'‖ := by
    intro y x hx x' hx'
    have e : (x - M (F x - y)) - (x' - M (F x' - y)) = (x - M (F x)) - (x' - M (F x')) := by
      rw [map_sub, map_sub]; abel
    rw [e]; exact hcon x hx x' hx'
  exact ⟨fun y hy => exists_solution_chord_inj F M hM x₀ y r hr (hcon' y) hy,
    fun x hx x' hx' => chord_lip F M x₀ 0 r (hcon' 0) hx hx'⟩

/-- Coordinatewise closeness gives the sup norm bound. -/
theorem norm_le_of_close {N : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {w w' : Fin N → ℝ} (h : Close δ w w') :
    ‖w - w'‖ ≤ δ :=
  (pi_norm_le_iff_of_nonneg hδ).2 fun k => by
    rw [Pi.sub_apply, Real.norm_eq_abs]; exact h k

/-- The sup norm bound gives coordinatewise closeness. -/
theorem close_of_norm_le {N : ℕ} {δ : ℝ} {w w' : Fin N → ℝ} (h : ‖w - w'‖ ≤ δ) :
    Close δ w w' := fun k => by
  have := (norm_le_pi_norm (w - w') k).trans h
  rwa [Pi.sub_apply, Real.norm_eq_abs] at this

/-! ## The two comparisons of `ν` with the head -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`nu_lo` from a pure-power identity** (Lemma 2.3). -/
theorem nu_lo_of_identity (g : ι → ℝ) (d E : ι → ℕ) (Dν Eb a w : ℕ) (hE : ∀ j, Even (E j))
    (hEd : ∀ j, E j * d j = Dν) (hEb : ∀ j, E j ≤ Eb) (Γ : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (K κ : ℝ) (hκ : 0 < κ) (hκ1 : 2 * κ ≤ 1) (hK : 4 * K * Γ.card * κ ≤ 1)
    (hc : ∀ γ ∈ Γ, |c γ| ≤ K) (hhom : ∀ γ ∈ Γ, ∑ j, γ j * d j = a * w)
    (hne : ∀ γ ∈ Γ, ∑ j, γ j ≠ 0) (x : ℝ) (hid : x ^ a = ∑ γ ∈ Γ, c γ * ∏ j, g j ^ γ j)
    (r : ℝ) (hr : 0 < r) (hx : r ^ w ≤ |x|) : κ ^ Eb * r ^ Dν ≤ ∑ j, g j ^ E j := by
  have hX : r ^ (a * w) ≤ |x ^ a| := by
    rw [abs_pow, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hr.le _) hx _
  obtain ⟨j, hj⟩ := exists_large g d r hr (a * w) Γ c K κ hκ hκ1 hK hc hhom hne _ hid hX
  exact nu_lower g d E r hr Dν Eb hE hEd hEb κ hκ (by linarith) hj

/-- `|x^α| ≤ r^{w·α}` when `|x_m| ≤ r^{w_m}`. -/
lemma abs_monomial_le {k : ℕ} (x : Fin k → ℝ) (w α : Fin k → ℕ) {r : ℝ} (_hr : 0 ≤ r)
    (hx : ∀ m, |x m| ≤ r ^ w m) : |∏ m, x m ^ α m| ≤ r ^ (∑ m, w m * α m) := by
  rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun m _ => abs_nonneg _) fun m _ => ?_
  rw [abs_pow, pow_mul]
  exact pow_le_pow_left₀ (abs_nonneg _) (hx m) _

/-- **`nu_hi` from `F_t` weighted monomial**: `gᵢ = Σ_α bᵢα x^α` over head monomials of weighted
degree `≥ dᵢ`. -/
theorem nu_hi_of_identity {k : ℕ} (g : ι → ℝ) (d E : ι → ℕ) (Dν : ℕ) (hE : ∀ j, Even (E j))
    (hEd : ∀ j, E j * d j = Dν) (x : Fin k → ℝ) (w : Fin k → ℕ) (Γ : ι → Finset (Fin k → ℕ))
    (bc : ι → (Fin k → ℕ) → ℝ) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ i, ∀ α ∈ Γ i, |bc i α| ≤ K)
    (hdeg : ∀ i, ∀ α ∈ Γ i, d i ≤ ∑ m, w m * α m)
    (hid : ∀ i, g i = ∑ α ∈ Γ i, bc i α * ∏ m, x m ^ α m) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : ∀ m, |x m| ≤ r ^ w m) :
    ∑ j, g j ^ E j ≤ (∑ j, (K * (Γ j).card) ^ E j) * r ^ Dν := by
  have hg : ∀ i, |g i| ≤ K * (Γ i).card * r ^ d i := by
    intro i
    rw [hid i]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ α ∈ Γ i, |bc i α * ∏ m, x m ^ α m| ≤ K * r ^ d i := fun α hα => by
      rw [abs_mul]
      refine mul_le_mul (hb i α hα) ((abs_monomial_le x w α hr hx).trans ?_) (abs_nonneg _) hK
      exact pow_le_pow_of_le_one hr hr1 (hdeg i α hα)
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← (hE i).pow_abs]
  calc |g i| ^ E i ≤ (K * (Γ i).card * r ^ d i) ^ E i :=
        pow_le_pow_left₀ (abs_nonneg _) (hg i) _
    _ = (K * (Γ i).card) ^ E i * r ^ Dν := by
        rw [mul_pow, ← pow_mul, mul_comm (d i), hEd i]

/-! ## The cover from a partition of unity -/

/-- **Choosing `ν ≥ θ` or a chart**, from `1 = b ν + Σⱼ aⱼ hⱼ` with `|b|, |aⱼ| ≤ A` and `ν ≥ 0`:
with `8 A θ ≤ 1` and `8 A q κ ≤ 1` (`q` charts), either `θ ≤ ν` or some `κ ≤ |hⱼ|`. -/
theorem cover_of_identity {J : Type*} [Fintype J] [DecidableEq J] (νv b : ℝ) (a h : J → ℝ)
    (A θ κ : ℝ) (hθ : 0 < θ) (hκ : 0 < κ) (hν : 0 ≤ νv) (hb : |b| ≤ A) (ha : ∀ j, |a j| ≤ A)
    (hAθ : 8 * A * θ ≤ 1) (hAκ : 8 * A * Fintype.card J * κ ≤ 1)
    (hid : 1 = b * νv + ∑ j, a j * h j) : θ ≤ νv ∨ ∃ j, κ ≤ |h j| := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hb
  have hsplit : ∀ j, κ < |h j| ∨ |h j| < 2 * κ := fun j => cotrans (lt_two_mul' hκ) _
  rcases cotrans (lt_two_mul' hθ) νv with h1 | h1
  · exact Or.inl h1.le
  rcases exists_or_forall_finset hsplit Finset.univ with ⟨j, -, hj⟩ | hall
  · exact Or.inr ⟨j, hj.le⟩
  exfalso
  have e1 : |b * νv| ≤ A * (2 * θ) := by
    rw [abs_mul, abs_of_nonneg hν]
    exact mul_le_mul hb h1.le hν hA
  have e2 : |∑ j, a j * h j| ≤ Fintype.card J * (A * (2 * κ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ j ∈ (Finset.univ : Finset J), |a j * h j| ≤ A * (2 * κ) := fun j _ => by
      rw [abs_mul]; exact mul_le_mul (ha j) (hall j (Finset.mem_univ j)).le (abs_nonneg _) hA
    refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have e3 : (1 : ℝ) ≤ A * (2 * θ) + Fintype.card J * (A * (2 * κ)) := by
    calc (1 : ℝ) = |b * νv + ∑ j, a j * h j| := by rw [← hid, abs_one]
      _ ≤ |b * νv| + |∑ j, a j * h j| := abs_add_le _ _
      _ ≤ _ := add_le_add e1 e2
  linarith

end BezoutCounterexample.Constructive
