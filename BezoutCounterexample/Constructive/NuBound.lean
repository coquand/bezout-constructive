import Mathlib
import BezoutCounterexample.Constructive.Attr

/-!
# `ν` stays positive on the pushed-off chain (`~/COLL/bezout-positive.tex`, Lemma 2.3)

On a chart where `F_t` is weighted monomial, every head coordinate has a pure power in the Rees
algebra: an exact identity `xₘ^{aₘ} = Σ_γ c_γ g^γ` with `Σⱼ γⱼ dⱼ = aₘ wₘ` and `γ ≠ 0`. At a pushed
point `xₘ = r^{wₘ} ηₘ` with `|ηₘ| = 1`, so `|xₘ^{aₘ}| = r^{aₘ wₘ}`. Evaluating the identity there
gives some `gⱼ` of size at least `κ r^{dⱼ}` (`exists_large`), and hence
`ν = Σⱼ gⱼ^{Eⱼ} ≥ κ^E r^{2 d!}` (`nu_lower`). No compactness and no error terms are needed: the
identity is exact.

Constructive reals: the large `gⱼ` is found by finitely many comparisons with a margin
(`cotrans`, cotransitivity of `<`, the one trusted primitive). Divisions do not occur.
-/

namespace BezoutCounterexample.Constructive

/-- **Cotransitivity of `<` on `ℝ`** (trusted primitive: an axiom of Bishop's reals, proved
classically in Mathlib). -/
@[cprim]
theorem cotrans {x y : ℝ} (h : x < y) (z : ℝ) : x < z ∨ z < y := by
  rcases lt_or_ge x z with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (lt_of_le_of_lt h1 h)

/-- A finite search: either some `P j`, or `Q j` for all `j`. -/
lemma exists_or_forall_finset {ι : Type*} [DecidableEq ι] {P Q : ι → Prop}
    (h : ∀ j, P j ∨ Q j) : ∀ s : Finset ι, (∃ j ∈ s, P j) ∨ ∀ j ∈ s, Q j := by
  intro s
  induction s using Finset.induction_on with
  | empty => exact Or.inr fun _ h => absurd h (Finset.notMem_empty _)
  | insert a s _ ih =>
    rcases h a with ha | ha
    · exact Or.inl ⟨a, Finset.mem_insert_self a s, ha⟩
    · rcases ih with ⟨j, hj, hPj⟩ | hall
      · exact Or.inl ⟨j, Finset.mem_insert_of_mem hj, hPj⟩
      · refine Or.inr fun j hj => ?_
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact ha
        · exact hall j hj

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- `|Π uⱼ^{γⱼ}| ≤ b^{Σγⱼ} r^{Σγⱼdⱼ}` when `|uⱼ| ≤ b r^{dⱼ}`. -/
lemma abs_prod_le {u : ι → ℝ} {d γ : ι → ℕ} {b r : ℝ} (_hb : 0 ≤ b) (_hr : 0 ≤ r)
    (hu : ∀ j, |u j| ≤ b * r ^ d j) :
    |∏ j, u j ^ γ j| ≤ b ^ (∑ j, γ j) * r ^ (∑ j, γ j * d j) := by
  rw [Finset.abs_prod]
  calc ∏ j, |u j ^ γ j| = ∏ j, |u j| ^ γ j := by simp [abs_pow]
    _ ≤ ∏ j, (b * r ^ d j) ^ γ j :=
        Finset.prod_le_prod₀ (fun j _ => pow_nonneg (abs_nonneg _) _)
          (fun j _ => pow_le_pow_left₀ (abs_nonneg _) (hu j) _)
    _ = b ^ (∑ j, γ j) * r ^ (∑ j, γ j * d j) := by
        simp only [mul_pow, ← pow_mul, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        congr 2
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **Some generator is large.** From the exact identity `X = Σ_γ c_γ u^γ` (homogeneous of
weighted degree `D`, all `γ ≠ 0`, `|c_γ| ≤ K`) and `r^D ≤ |X|`: some `κ r^{dⱼ} ≤ |uⱼ|`, for any
`κ > 0` with `4 K #Γ κ ≤ 1` and `2κ ≤ 1`. -/
theorem exists_large (u : ι → ℝ) (d : ι → ℕ) (r : ℝ) (hr : 0 < r) (D : ℕ)
    (Γ : Finset (ι → ℕ)) (c : (ι → ℕ) → ℝ) (K κ : ℝ) (hκ : 0 < κ) (hκ1 : 2 * κ ≤ 1)
    (hK : 4 * K * Γ.card * κ ≤ 1)
    (hc : ∀ γ ∈ Γ, |c γ| ≤ K) (hhom : ∀ γ ∈ Γ, ∑ j, γ j * d j = D)
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
    rw [hhom γ hγ] at h1
    have h2 : (2 * κ) ^ (∑ j, γ j) ≤ 2 * κ := pow_le_of_le_one hb hκ1 (hne γ hγ)
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hc γ hγ)
    calc |c γ| * |∏ j, u j ^ γ j| ≤ K * ((2 * κ) ^ (∑ j, γ j) * r ^ D) :=
          mul_le_mul (hc γ hγ) h1 (abs_nonneg _) hK0
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

omit [DecidableEq ι] in
/-- **`ν` is bounded below on the pushed-off chain**: with even exponents `Eⱼ`, `Eⱼ dⱼ = Dν`, and
`Eⱼ ≤ E`, `ν = Σⱼ uⱼ^{Eⱼ} ≥ κ^E r^{Dν}` (for `κ ≤ 1`). -/
theorem nu_lower (u : ι → ℝ) (d E : ι → ℕ) (r : ℝ) (hr : 0 < r) (Dν Eb : ℕ)
    (hE : ∀ j, Even (E j)) (hEd : ∀ j, E j * d j = Dν) (hEb : ∀ j, E j ≤ Eb)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) {j : ι} (hj : κ * r ^ d j ≤ |u j|) :
    κ ^ Eb * r ^ Dν ≤ ∑ i, u i ^ E i := by
  have hterm : u j ^ E j ≤ ∑ i, u i ^ E i :=
    Finset.single_le_sum (f := fun i => u i ^ E i) (fun i _ => (hE i).pow_nonneg _)
      (Finset.mem_univ j)
  have h1 : (κ * r ^ d j) ^ E j ≤ u j ^ E j := by
    calc (κ * r ^ d j) ^ E j ≤ |u j| ^ E j := pow_le_pow_left₀ (by positivity) hj _
      _ = u j ^ E j := (hE j).pow_abs (u j)
  have h2 : κ ^ Eb ≤ κ ^ E j := pow_le_pow_of_le_one hκ.le hκ1 (hEb j)
  calc κ ^ Eb * r ^ Dν ≤ κ ^ E j * r ^ Dν :=
        mul_le_mul_of_nonneg_right h2 (pow_pos hr _).le
    _ = (κ * r ^ d j) ^ E j := by rw [mul_pow, ← pow_mul, mul_comm (d j), hEd j]
    _ ≤ u j ^ E j := h1
    _ ≤ ∑ i, u i ^ E i := hterm

end BezoutCounterexample.Constructive
