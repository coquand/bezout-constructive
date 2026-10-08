import Mathlib
import BezoutCounterexample.Constructive.Attr

/-!
# The discrete Möbius lemma

A finite, constructive replacement for the topological obstruction of Section 2 of
Hägg–Mörtberg (non-orientability of the Möbius bundle, Lemmas 2.1 and 2.2).

Data along a closed chain `i = 0, …, m`: a radius `r i`, a unit vector `(a i, b i)` (the
half-angle of the point `ζ i = r i · (a² - b², 2ab)` of the plane), and values `u, v, p, q, μ`
of five ring elements at the `i`-th real point, satisfying `μ · (p, q) M(ζ) (u, v)ᵀ = 1` with
`M(x, y) = [[1 + x, y], [y, 1 - x]]`. The chain closes with the half-angle reversed
(`(a m, b m) = -(a 0, b 0)`: the chain winds an odd number of times). If the radii stay close to
`1` and consecutive data are close, this is contradictory (`discrete_moebius`).

The proof is a finite sign search: `λ i = (1 + r i)(u a + v b)` is bounded away from `0` by the
relation, its sign is decided with a margin (`sign_split`), it changes sign between `0` and `m`,
and at a sign change consecutive values are far apart.

Order goals on `ℝ` are never proved by contradiction; the only classical facts used are the
`@[cprim]` lemmas below, whose statements are constructively valid.
-/

namespace BezoutCounterexample.Constructive

/-- Approximating `x` to precision `1 / 2c` decides its sign when `c |x| ≥ 1`, `c > 0`. -/
@[cprim] theorem sign_split {x c : ℝ} (hc : 0 < c) (hx : 1 ≤ c * |x|) : 0 < x ∨ x < 0 := by
  rcases lt_trichotomy x 0 with h | h | h
  · exact Or.inr h
  · subst h; simp at hx; linarith
  · exact Or.inl h

/-- In constructive analysis `a ≤ b` is defined as `¬ b < a`. -/
@[cprim] theorem le_of_not_lt' {a b : ℝ} (h : ¬ b < a) : a ≤ b := le_of_not_gt h

/-- Product estimate. -/
theorem abs_mul_sub_mul_le (x y x' y' : ℝ) :
    |x' * y' - x * y| ≤ |x' - x| * |y'| + |x| * |y' - y| := by
  have h : x' * y' - x * y = (x' - x) * y' + x * (y' - y) := by ring
  rw [h, ← abs_mul, ← abs_mul]
  exact abs_add_le _ _

theorem abs_le_one_of_sq_add {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) : |a| ≤ 1 := by
  have h1 : a ^ 2 ≤ 1 := by
    apply le_of_not_lt'
    intro hlt
    nlinarith [sq_nonneg b]
  exact (sq_le_one_iff_abs_le_one a).1 h1

/-- The relation in coordinates adapted to the half-angle frame `e = (a, b)`, `f = (-b, a)`. -/
theorem frame_identity (r a b u v p q : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    p * ((1 + r * (a ^ 2 - b ^ 2)) * u + r * (2 * a * b) * v) +
      q * (r * (2 * a * b) * u + (1 - r * (a ^ 2 - b ^ 2)) * v) =
    (1 + r) * (u * a + v * b) * (p * a + q * b) +
      (1 - r) * (-(u * b) + v * a) * (-(p * b) + q * a) := by
  linear_combination (-(u * p + v * q)) * hab

/-- A finite sign-change search. -/
theorem exists_sign_change (l : ℕ → ℝ) :
    ∀ m : ℕ, (∀ i ≤ m, 0 < l i ∨ l i < 0) → 0 < l 0 → l m < 0 →
      ∃ i < m, 0 < l i ∧ l (i + 1) < 0 := by
  intro m
  induction m with
  | zero => intro _ h0 hm; exact absurd (lt_trans hm h0) (lt_irrefl _)
  | succ k ih =>
    intro hs h0 hm
    rcases hs k (Nat.le_succ k) with hk | hk
    · exact ⟨k, Nat.lt_succ_self k, hk, hm⟩
    · obtain ⟨i, hi, h1, h2⟩ := ih (fun i hi => hs i (Nat.le_succ_of_le hi)) h0 hk
      exact ⟨i, Nat.lt_succ_of_lt hi, h1, h2⟩

/-- **The discrete Möbius lemma.** -/
theorem discrete_moebius (C η δ : ℝ) (m : ℕ) (r a b u v p q μ : ℕ → ℝ)
    (hC : 1 ≤ C) (hη : 0 ≤ η) (hηC : 8 * C ^ 3 * η ≤ 1) (hδ : 0 ≤ δ) (hδC : 28 * C ^ 3 * δ < 1)
    (hab : ∀ i, a i ^ 2 + b i ^ 2 = 1)
    (hrel : ∀ i, μ i * (p i * ((1 + r i * (a i ^ 2 - b i ^ 2)) * u i + r i * (2 * a i * b i) * v i)
      + q i * (r i * (2 * a i * b i) * u i + (1 - r i * (a i ^ 2 - b i ^ 2)) * v i)) = 1)
    (hp : ∀ i, |p i| ≤ C) (hq : ∀ i, |q i| ≤ C) (hμ : ∀ i, |μ i| ≤ C)
    (hu : ∀ i, |u i| ≤ C) (hv : ∀ i, |v i| ≤ C) (hr : ∀ i, |r i - 1| ≤ η)
    (dr : ∀ i < m, |r (i + 1) - r i| ≤ δ) (da : ∀ i < m, |a (i + 1) - a i| ≤ δ)
    (db : ∀ i < m, |b (i + 1) - b i| ≤ δ) (du : ∀ i < m, |u (i + 1) - u i| ≤ δ)
    (dv : ∀ i < m, |v (i + 1) - v i| ≤ δ)
    (cr : r m = r 0) (cu : u m = u 0) (cv : v m = v 0) (ca : a m = -a 0) (cb : b m = -b 0) :
    False := by
  set l : ℕ → ℝ := fun i => (1 + r i) * (u i * a i + v i * b i) with hl
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hC3 : 1 ≤ C ^ 3 := one_le_pow₀ hC
  -- elementary bounds
  have ha1 : ∀ i, |a i| ≤ 1 := fun i => abs_le_one_of_sq_add (hab i)
  have hb1 : ∀ i, |b i| ≤ 1 := fun i => abs_le_one_of_sq_add (a := b i) (b := a i) (by linarith [hab i])
  have hη1 : 8 * η ≤ 1 := by
    apply le_of_not_lt'; intro h; nlinarith [mul_le_mul_of_nonneg_right hC3 hη]
  have hrpos : ∀ i, |1 + r i| ≤ 3 := by
    intro i
    have h := abs_le.1 (hr i)
    exact abs_le.2 ⟨by linarith [h.1], by linarith [h.2]⟩
  have hlin : ∀ (s t x y : ℝ), |s| ≤ C → |t| ≤ C → |x| ≤ 1 → |y| ≤ 1 → |s * x + t * y| ≤ 2 * C := by
    intro s t x y hs ht hx hy
    calc |s * x + t * y| ≤ |s * x| + |t * y| := abs_add_le _ _
      _ = |s| * |x| + |t| * |y| := by rw [abs_mul, abs_mul]
      _ ≤ C * 1 + C * 1 := by
          gcongr
      _ = 2 * C := by ring
  -- lower bound for `|l i|`
  have hlow : ∀ i, 1 ≤ 4 * C ^ 2 * |l i| := by
    intro i
    have hid := frame_identity (r i) (a i) (b i) (u i) (v i) (p i) (q i) (hab i)
    have h1 := hrel i
    rw [hid] at h1
    set A := p i * a i + q i * b i
    set B := -(p i * b i) + q i * a i
    set φ := (1 - r i) * (-(u i * b i) + v i * a i)
    have hA : |A| ≤ 2 * C := hlin _ _ _ _ (hp i) (hq i) (ha1 i) (hb1 i)
    have hB : |B| ≤ 2 * C := by
      have := hlin (-(p i)) (q i) (b i) (a i) (by rw [abs_neg]; exact hp i) (hq i) (hb1 i) (ha1 i)
      simpa [B, neg_mul] using this
    have hφ : |φ| ≤ η * (2 * C) := by
      have h2 : |(-(u i * b i) + v i * a i)| ≤ 2 * C := by
        have := hlin (-(u i)) (v i) (b i) (a i) (by rw [abs_neg]; exact hu i) (hv i) (hb1 i) (ha1 i)
        simpa [neg_mul] using this
      have h3 : |1 - r i| ≤ η := by rw [abs_sub_comm]; exact hr i
      calc |φ| = |1 - r i| * |(-(u i * b i) + v i * a i)| := abs_mul _ _
        _ ≤ η * (2 * C) := mul_le_mul h3 h2 (abs_nonneg _) hη
    have h4 : 1 ≤ C * (|l i| * (2 * C) + η * (2 * C) * (2 * C)) := by
      have e1 : (1 : ℝ) = |μ i * (l i * A + φ * B)| := by rw [h1, abs_one]
      calc (1 : ℝ) = |μ i| * |l i * A + φ * B| := by rw [e1, abs_mul]
        _ ≤ C * (|l i * A| + |φ * B|) := by
            gcongr
            · exact hμ i
            · exact abs_add_le _ _
        _ = C * (|l i| * |A| + |φ| * |B|) := by rw [abs_mul (l i) A, abs_mul φ B]
        _ ≤ C * (|l i| * (2 * C) + η * (2 * C) * (2 * C)) := by
            gcongr
    apply le_of_not_lt'
    intro hlt
    nlinarith [abs_nonneg (l i), mul_le_mul_of_nonneg_left hηC (le_of_lt hC0)]
  -- consecutive values are close
  have hstep : ∀ i < m, |l (i + 1) - l i| ≤ δ * (8 * C + 6) := by
    intro i hi
    have hw : ∀ j, |u j * a j + v j * b j| ≤ 2 * C :=
      fun j => hlin _ _ _ _ (hu j) (hv j) (ha1 j) (hb1 j)
    have hdw : |(u (i + 1) * a (i + 1) + v (i + 1) * b (i + 1)) - (u i * a i + v i * b i)| ≤
        δ * (2 + 2 * C) := by
      have e : (u (i + 1) * a (i + 1) + v (i + 1) * b (i + 1)) - (u i * a i + v i * b i) =
          (u (i + 1) * a (i + 1) - u i * a i) + (v (i + 1) * b (i + 1) - v i * b i) := by ring
      rw [e]
      have h1 := abs_mul_sub_mul_le (u i) (a i) (u (i + 1)) (a (i + 1))
      have h2 := abs_mul_sub_mul_le (v i) (b i) (v (i + 1)) (b (i + 1))
      calc _ ≤ |u (i + 1) * a (i + 1) - u i * a i| + |v (i + 1) * b (i + 1) - v i * b i| :=
            abs_add_le _ _
        _ ≤ (|u (i + 1) - u i| * |a (i + 1)| + |u i| * |a (i + 1) - a i|) +
            (|v (i + 1) - v i| * |b (i + 1)| + |v i| * |b (i + 1) - b i|) := add_le_add h1 h2
        _ ≤ (δ * 1 + C * δ) + (δ * 1 + C * δ) := by
            gcongr
            · exact du i hi
            · exact ha1 _
            · exact hu i
            · exact da i hi
            · exact dv i hi
            · exact hb1 _
            · exact hv i
            · exact db i hi
        _ = δ * (2 + 2 * C) := by ring
    have h := abs_mul_sub_mul_le (1 + r i) (u i * a i + v i * b i) (1 + r (i + 1))
      (u (i + 1) * a (i + 1) + v (i + 1) * b (i + 1))
    have e : (1 + r (i + 1)) - (1 + r i) = r (i + 1) - r i := by ring
    rw [e] at h
    calc |l (i + 1) - l i| ≤ |r (i + 1) - r i| * |u (i + 1) * a (i + 1) + v (i + 1) * b (i + 1)| +
          |1 + r i| * |(u (i + 1) * a (i + 1) + v (i + 1) * b (i + 1)) - (u i * a i + v i * b i)| := h
      _ ≤ δ * (2 * C) + 3 * (δ * (2 + 2 * C)) := by
          gcongr
          · exact dr i hi
          · exact hw _
          · exact hrpos i
      _ = δ * (8 * C + 6) := by ring
  -- the sign reverses along the chain
  have hend : l m = -l 0 := by
    simp only [hl, cr, cu, cv, ca, cb]; ring
  have hsign : ∀ i, 0 < l i ∨ l i < 0 := fun i => sign_split (by positivity) (hlow i)
  -- the step bound is smaller than the gap at a sign change
  have hsmall : δ * (8 * C + 6) * (4 * C ^ 2) < 2 := by
    have h1 : δ * (8 * C + 6) * (4 * C ^ 2) ≤ 2 * (28 * C ^ 3 * δ) := by
      have e1 : 8 * C + 6 ≤ 14 * C := by linarith
      have e2 : 0 ≤ δ * (4 * C ^ 2) := by positivity
      have e3 := mul_le_mul_of_nonneg_right e1 e2
      apply le_of_not_lt'; intro h; nlinarith
    calc δ * (8 * C + 6) * (4 * C ^ 2) ≤ 2 * (28 * C ^ 3 * δ) := h1
      _ < 2 * 1 := mul_lt_mul_of_pos_left hδC two_pos
      _ = 2 := mul_one 2
  have hfar : ∀ i < m, (0 < l i ∧ l (i + 1) < 0) ∨ (l i < 0 ∧ 0 < l (i + 1)) → False := by
    intro i hi hc
    have hs := hstep i hi
    have hl1 := hlow i
    have hl2 := hlow (i + 1)
    have hd1 := le_abs_self (l (i + 1) - l i)
    have hd2 := neg_le_abs (l (i + 1) - l i)
    have h4 : 0 ≤ 4 * C ^ 2 := by positivity
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_pos h1] at hl1
      rw [abs_of_neg h2] at hl2
      nlinarith [mul_le_mul_of_nonneg_left (le_trans hd2 hs) h4]
    · rw [abs_of_neg h1] at hl1
      rw [abs_of_pos h2] at hl2
      nlinarith [mul_le_mul_of_nonneg_left (le_trans hd1 hs) h4]
  rcases hsign 0 with h0 | h0
  · have hm : l m < 0 := by rw [hend]; exact neg_neg_of_pos h0
    obtain ⟨i, hi, h1, h2⟩ := exists_sign_change l m (fun i _ => hsign i) h0 hm
    exact hfar i hi (Or.inl ⟨h1, h2⟩)
  · have hm : (fun i => -l i) m < 0 := by
      show -l m < 0
      rw [hend, neg_neg]; exact h0
    obtain ⟨i, hi, h1, h2⟩ := exists_sign_change (fun i => -l i) m
      (fun i _ => (hsign i).elim (fun h => Or.inr (neg_neg_of_pos h)) (fun h => Or.inl (neg_pos.2 h)))
      (neg_pos.2 h0) hm
    exact hfar i hi (Or.inr ⟨neg_pos.1 h1, neg_lt_zero.1 h2⟩)

end BezoutCounterexample.Constructive
