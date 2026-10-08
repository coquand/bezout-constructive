import Mathlib
import BezoutCounterexample.Constructive.ChainLiftChart

/-!
# `nu_lo` from a pure-power identity of weighted degree `≥ a w`

The Rees algebra gives `x^a T^{a w} = Σ_γ c_γ (g T^d)^γ T^{-(γ·d - a w)}`, i.e. an identity
`x^a = Σ_γ c_γ g^γ` with `γ·d ≥ a w` (not `=`). For `r ≤ 1` the extra degree only helps:
`r^{γ·d} ≤ r^{a w}`. Variants of `exists_large` and `nu_lo_of_identity` with `≤`.
-/

namespace BezoutCounterexample.Constructive

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `exists_large` with `D ≤ γ·d` and `r ≤ 1`. -/
theorem exists_large_ge (u : ι → ℝ) (d : ι → ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (D : ℕ)
    (Γ : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ) (K κ : ℝ) (hκ : 0 < κ) (hκ1 : 2 * κ ≤ 1)
    (hK : 4 * K * Γ.card * κ ≤ 1)
    (hc : ∀ γ ∈ Γ, |c γ| ≤ K) (hhom : ∀ γ ∈ Γ, D ≤ ∑ j, γ j * d j)
    (hne : ∀ γ ∈ Γ, ∑ j, γ j ≠ 0) (X : ℝ) (hid : X = ∑ γ ∈ Γ, c γ * ∏ j, u j ^ γ j)
    (hX : r ^ D ≤ |X|) : ∃ j, κ * r ^ d j ≤ |u j| := by
  have hsplit : ∀ j, κ * r ^ d j < |u j| ∨ |u j| < 2 * κ * r ^ d j := fun j => by
    have hx : 0 < κ * r ^ d j := mul_pos hκ (pow_pos hr _)
    have hlt : κ * r ^ d j < 2 * κ * r ^ d j :=
      calc κ * r ^ d j < κ * r ^ d j + κ * r ^ d j := lt_add_of_pos_right _ hx
        _ = 2 * κ * r ^ d j := by ring
    exact cotrans hlt _
  rcases exists_or_forall_finset hsplit Finset.univ with ⟨j, -, hj⟩ | hall
  · exact ⟨j, hj.le⟩
  exfalso
  have hrD : 0 < r ^ D := pow_pos hr D
  have hb : 0 ≤ 2 * κ := by linarith
  have hterm : ∀ γ ∈ Γ, |c γ * ∏ j, u j ^ γ j| ≤ K * (2 * κ) * r ^ D := by
    intro γ hγ
    rw [abs_mul]
    have h1 := abs_prod_le (γ := γ) hb hr.le fun j => (hall j (Finset.mem_univ j)).le
    have h1' : |∏ j, u j ^ γ j| ≤ (2 * κ) ^ (∑ j, γ j) * r ^ D :=
      h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr.le hr1 (hhom γ hγ))
        (pow_nonneg hb _))
    have h2 : (2 * κ) ^ (∑ j, γ j) ≤ 2 * κ := pow_le_of_le_one hb hκ1 (hne γ hγ)
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hc γ hγ)
    calc |c γ| * |∏ j, u j ^ γ j| ≤ K * ((2 * κ) ^ (∑ j, γ j) * r ^ D) :=
          mul_le_mul (hc γ hγ) h1' (abs_nonneg _) hK0
      _ ≤ K * ((2 * κ) * r ^ D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hrD.le) hK0
      _ = K * (2 * κ) * r ^ D := by ring
  have hsum : |X| ≤ Γ.card * (K * (2 * κ) * r ^ D) := by
    rw [hid]
    calc |∑ γ ∈ Γ, c γ * ∏ j, u j ^ γ j| ≤ ∑ γ ∈ Γ, |c γ * ∏ j, u j ^ γ j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ γ ∈ Γ, K * (2 * κ) * r ^ D := Finset.sum_le_sum hterm
      _ = Γ.card * (K * (2 * κ) * r ^ D) := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : 2 * ((Γ.card : ℝ) * (K * (2 * κ) * r ^ D)) ≤ r ^ D := by
    have : 2 * ((Γ.card : ℝ) * (K * (2 * κ) * r ^ D)) = (4 * K * Γ.card * κ) * r ^ D := by ring
    rw [this]
    calc (4 * K * Γ.card * κ) * r ^ D ≤ 1 * r ^ D := mul_le_mul_of_nonneg_right hK hrD.le
      _ = r ^ D := one_mul _
  have h3 : 2 * r ^ D ≤ r ^ D := by linarith
  linarith

/-- `nu_lo_of_identity` with weighted degree `≥ a w` and `r ≤ 1`. -/
theorem nu_lo_of_identity_ge (g : ι → ℝ) (d E : ι → ℕ) (Dν Eb a w : ℕ) (hE : ∀ j, Even (E j))
    (hEd : ∀ j, E j * d j = Dν) (hEb : ∀ j, E j ≤ Eb) (Γ : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ)
    (K κ : ℝ) (hκ : 0 < κ) (hκ1 : 2 * κ ≤ 1) (hK : 4 * K * Γ.card * κ ≤ 1)
    (hc : ∀ γ ∈ Γ, |c γ| ≤ K) (hhom : ∀ γ ∈ Γ, a * w ≤ ∑ j, γ j * d j)
    (hne : ∀ γ ∈ Γ, ∑ j, γ j ≠ 0) (x : ℝ) (hid : x ^ a = ∑ γ ∈ Γ, c γ * ∏ j, g j ^ γ j)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hx : r ^ w ≤ |x|) : κ ^ Eb * r ^ Dν ≤ ∑ j, g j ^ E j := by
  have hX : r ^ (a * w) ≤ |x ^ a| := by
    rw [abs_pow, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hr.le _) hx _
  obtain ⟨j, hj⟩ := exists_large_ge g d r hr hr1 (a * w) Γ c K κ hκ hκ1 hK hc hhom hne _ hid hX
  exact nu_lower g d E r hr Dν Eb hE hEd hEb κ hκ (by linarith) hj

end BezoutCounterexample.Constructive
