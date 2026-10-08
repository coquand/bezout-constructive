import Mathlib
import BezoutCounterexample.Constructive.ChainLift

/-!
# Gluing chain lifting into the discrete Möbius lemma (`~/COLL/bezout-direct.tex`, §2)

`moebius_approx` is the discrete Möbius lemma in the form needed after lifting: the half-angle
`(a, b)` (exactly a unit vector) is attached to the *original* chain point, and the projection
`(x, y)` of the lifted point is only `η`-close to `(a² - b², 2ab)`. This removes the radii of
`Moebius.discrete_moebius` and makes the bookkeeping of the winding trivial: the lifted chain
reuses the half-angles of the original chain through the index map, and the reversal
`(a, b)(ι m') = -(a, b)(ι 0)` is inherited from the original chain.

`circle_chain`: the starting chain in `ℝ²` with exact half-angles
`(a, b) = ((1 - t²)/(1 + t²), 2t/(1 + t²))`, `t = -1, -1 + 2h, …, 1` (`m h = 1`), going from
`(0, -1)` to `(0, 1)`: the half-angle reverses, the chain closes.

`no_moebius_lift`: a chain lift from the plane to the real points of `B` (composite of the
steps of the tower, `ChainLift.comp`) is incompatible with a relation
`μ · (p, q) M(x, y) (u, v)ᵀ = 1` on `B` whose terms are bounded and Lipschitz on boxes.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

/-- The relation in the half-angle frame, with the errors `ξ = x - (a² - b²)`, `χ = y - 2ab`. -/
theorem frame_identity' (a b x y u v p q : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    p * ((1 + x) * u + y * v) + q * (y * u + (1 - x) * v) =
      2 * (u * a + v * b) * (p * a + q * b) +
      (p * ((x - (a ^ 2 - b ^ 2)) * u + (y - 2 * a * b) * v) +
        q * ((y - 2 * a * b) * u - (x - (a ^ 2 - b ^ 2)) * v)) := by
  linear_combination (-(p * u + q * v)) * hab

/-- **The discrete Möbius lemma, approximate form.** -/
theorem moebius_approx (C η δ : ℝ) (m : ℕ) (a b u v p q μ x y : ℕ → ℝ)
    (hC : 1 ≤ C) (hη : 0 ≤ η) (hηC : 8 * C ^ 3 * η ≤ 1) (hδ : 0 ≤ δ)
    (hδC : 16 * C ^ 3 * δ < 1)
    (hab : ∀ i ≤ m, a i ^ 2 + b i ^ 2 = 1)
    (hrel : ∀ i ≤ m, μ i * (p i * ((1 + x i) * u i + y i * v i) +
      q i * (y i * u i + (1 - x i) * v i)) = 1)
    (hp : ∀ i ≤ m, |p i| ≤ C) (hq : ∀ i ≤ m, |q i| ≤ C) (hμ : ∀ i ≤ m, |μ i| ≤ C)
    (hu : ∀ i ≤ m, |u i| ≤ C) (hv : ∀ i ≤ m, |v i| ≤ C)
    (hx : ∀ i ≤ m, |x i - (a i ^ 2 - b i ^ 2)| ≤ η)
    (hy : ∀ i ≤ m, |y i - 2 * a i * b i| ≤ η)
    (da : ∀ i < m, |a (i + 1) - a i| ≤ δ) (db : ∀ i < m, |b (i + 1) - b i| ≤ δ)
    (du : ∀ i < m, |u (i + 1) - u i| ≤ δ) (dv : ∀ i < m, |v (i + 1) - v i| ≤ δ)
    (cu : u m = u 0) (cv : v m = v 0) (ca : a m = -a 0) (cb : b m = -b 0) : False := by
  set l : ℕ → ℝ := fun i => u i * a i + v i * b i with hl
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have ha1 : ∀ i ≤ m, |a i| ≤ 1 := fun i hi => abs_le_one_of_sq_add (hab i hi)
  have hb1 : ∀ i ≤ m, |b i| ≤ 1 := fun i hi =>
    abs_le_one_of_sq_add (a := b i) (b := a i) (by linarith [hab i hi])
  have hlin : ∀ (s t x y : ℝ), |s| ≤ C → |t| ≤ C → |x| ≤ 1 → |y| ≤ 1 →
      |s * x + t * y| ≤ 2 * C := by
    intro s t x y hs ht hx hy
    calc |s * x + t * y| ≤ |s * x| + |t * y| := abs_add_le _ _
      _ = |s| * |x| + |t| * |y| := by rw [abs_mul, abs_mul]
      _ ≤ C * 1 + C * 1 := by gcongr
      _ = 2 * C := by ring
  -- lower bound `1 ≤ 8 C² |l i|`
  have hlow : ∀ i ≤ m, 1 ≤ 8 * C ^ 2 * |l i| := by
    intro i hi
    have h1 := hrel i hi
    rw [frame_identity' (a i) (b i) (x i) (y i) (u i) (v i) (p i) (q i) (hab i hi)] at h1
    set ξ := x i - (a i ^ 2 - b i ^ 2)
    set χ := y i - 2 * a i * b i
    have hA : |p i * a i + q i * b i| ≤ 2 * C := hlin _ _ _ _ (hp i hi) (hq i hi) (ha1 i hi) (hb1 i hi)
    have hpr : ∀ s t r, |s| ≤ C → |r| ≤ C → |t| ≤ η → |s * (t * r)| ≤ C * (η * C) :=
      fun s t r hs hr ht => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul hs (mul_le_mul ht hr (abs_nonneg _) hη) (by positivity) hC0.le
    have herr : |p i * (ξ * u i + χ * v i) + q i * (χ * u i - ξ * v i)| ≤ 4 * (C * (η * C)) := by
      have e : p i * (ξ * u i + χ * v i) + q i * (χ * u i - ξ * v i) =
          p i * (ξ * u i) + p i * (χ * v i) + q i * (χ * u i) + (-(q i) * (ξ * v i)) := by ring
      rw [e]
      have h1 := hpr (p i) ξ (u i) (hp i hi) (hu i hi) (hx i hi)
      have h2 := hpr (p i) χ (v i) (hp i hi) (hv i hi) (hy i hi)
      have h3 := hpr (q i) χ (u i) (hq i hi) (hu i hi) (hy i hi)
      have h4 := hpr (-(q i)) ξ (v i) (by rw [abs_neg]; exact hq i hi) (hv i hi) (hx i hi)
      calc _ ≤ |p i * (ξ * u i)| + |p i * (χ * v i)| + |q i * (χ * u i)| +
            |-(q i) * (ξ * v i)| := by
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
            exact abs_add_le _ _
        _ ≤ 4 * (C * (η * C)) := by linarith
    have h4 : 1 ≤ C * (|l i| * 2 * (2 * C) + 4 * (C * (η * C))) := by
      have e1 : (1 : ℝ) = |μ i| * |2 * l i * (p i * a i + q i * b i) +
          (p i * (ξ * u i + χ * v i) + q i * (χ * u i - ξ * v i))| := by
        rw [← abs_mul, h1, abs_one]
      rw [e1]
      gcongr
      · exact hμ i hi
      · refine (abs_add_le _ _).trans (add_le_add ?_ herr)
        rw [abs_mul, abs_mul, abs_two]
        have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 * |l i|)
        linarith
    have e2 : C * (|l i| * 2 * (2 * C) + 4 * (C * (η * C))) =
        4 * C ^ 2 * |l i| + 4 * (C ^ 3 * η) := by ring
    rw [e2] at h4
    linarith
  -- steps
  have hstep : ∀ i < m, |l (i + 1) - l i| ≤ δ * (2 + 2 * C) := by
    intro i hi
    have e : l (i + 1) - l i = (u (i + 1) * a (i + 1) - u i * a i) +
        (v (i + 1) * b (i + 1) - v i * b i) := by simp only [hl]; ring
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
          · exact ha1 _ hi
          · exact hu i hi.le
          · exact da i hi
          · exact dv i hi
          · exact hb1 _ hi
          · exact hv i hi.le
          · exact db i hi
      _ = δ * (2 + 2 * C) := by ring
  have hend : l m = -l 0 := by simp only [hl, cu, cv, ca, cb]; ring
  have hsign : ∀ i ≤ m, 0 < l i ∨ l i < 0 := fun i hi => sign_split (by positivity) (hlow i hi)
  have hsmall : δ * (2 + 2 * C) * (8 * C ^ 2) < 2 := by
    have h1 : δ * (2 + 2 * C) * (8 * C ^ 2) ≤ 2 * (16 * C ^ 3 * δ) := by
      have e1 : 2 + 2 * C ≤ 4 * C := by linarith
      have e2 : 0 ≤ δ * (8 * C ^ 2) := by positivity
      have e3 := mul_le_mul_of_nonneg_right e1 e2
      have e4 : δ * (2 + 2 * C) * (8 * C ^ 2) = (2 + 2 * C) * (δ * (8 * C ^ 2)) := by ring
      have e5 : 2 * (16 * C ^ 3 * δ) = 4 * C * (δ * (8 * C ^ 2)) := by ring
      rw [e4, e5]; exact e3
    calc δ * (2 + 2 * C) * (8 * C ^ 2) ≤ 2 * (16 * C ^ 3 * δ) := h1
      _ < 2 * 1 := mul_lt_mul_of_pos_left hδC two_pos
      _ = 2 := mul_one 2
  have hfar : ∀ i < m, (0 < l i ∧ l (i + 1) < 0) ∨ (l i < 0 ∧ 0 < l (i + 1)) → False := by
    intro i hi hc
    have hs := hstep i hi
    have hl1 := hlow i hi.le
    have hl2 := hlow (i + 1) hi
    have hd1 := le_abs_self (l (i + 1) - l i)
    have hd2 := neg_le_abs (l (i + 1) - l i)
    have h4 : 0 ≤ 8 * C ^ 2 := by positivity
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_pos h1] at hl1
      rw [abs_of_neg h2] at hl2
      nlinarith [mul_le_mul_of_nonneg_left (le_trans hd2 hs) h4]
    · rw [abs_of_neg h1] at hl1
      rw [abs_of_pos h2] at hl2
      nlinarith [mul_le_mul_of_nonneg_left (le_trans hd1 hs) h4]
  rcases hsign 0 (Nat.zero_le _) with h0 | h0
  · have hm : l m < 0 := by rw [hend]; exact neg_neg_of_pos h0
    obtain ⟨i, hi, h1, h2⟩ := exists_sign_change l m (fun i hi => hsign i hi) h0 hm
    exact hfar i hi (Or.inl ⟨h1, h2⟩)
  · have hm : (fun i => -l i) m < 0 := by
      show -l m < 0
      rw [hend, neg_neg]; exact h0
    obtain ⟨i, hi, h1, h2⟩ := exists_sign_change (fun i => -l i) m
      (fun i hi => (hsign i hi).elim (fun h => Or.inr (neg_neg_of_pos h))
        (fun h => Or.inl (neg_pos.2 h)))
      (neg_pos.2 h0) hm
    exact hfar i hi (Or.inr ⟨neg_pos.1 h1, neg_lt_zero.1 h2⟩)

/-! ## The starting chain: the circle, with exact rational half-angles -/

/-- The half-angle `((1 - t²) s, 2 t s)` with `(1 + t²) s = 1` moves by at most `4 |t' - t|`. -/
theorem half_angle_step {t t' s s' : ℝ} (hs : (1 + t ^ 2) * s = 1) (hs' : (1 + t' ^ 2) * s' = 1)
    (hs0 : 0 < s) (hs0' : 0 < s') (ht : |t| ≤ 1) (ht' : |t'| ≤ 1) :
    |(1 - t' ^ 2) * s' - (1 - t ^ 2) * s| ≤ 4 * |t' - t| ∧ |2 * t' * s' - 2 * t * s| ≤ 4 * |t' - t| := by
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg t]
  have hs1' : s' ≤ 1 := by nlinarith [sq_nonneg t']
  have e1 : (1 - t' ^ 2) * s' - (1 - t ^ 2) * s = 2 * s * s' * (t - t') * (t + t') := by
    linear_combination (-((1 - t' ^ 2) * s')) * hs + ((1 - t ^ 2) * s) * hs'
  have e2 : 2 * t' * s' - 2 * t * s = 2 * s * s' * (t' - t) * (1 - t * t') := by
    linear_combination (-(2 * t' * s')) * hs + (2 * t * s) * hs'
  have hss : |2 * s * s'| ≤ 2 := by
    rw [abs_of_pos (by positivity)]; nlinarith
  have hsum : |t + t'| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  have hprod : |1 - t * t'| ≤ 2 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_one, abs_mul]
    nlinarith [abs_nonneg t, abs_nonneg t']
  constructor
  · rw [e1, abs_mul, abs_mul, abs_sub_comm t t']
    calc |2 * s * s'| * |t' - t| * |t + t'| ≤ 2 * |t' - t| * 2 := by
          gcongr
    _ = 4 * |t' - t| := by ring
  · rw [e2, abs_mul, abs_mul]
    calc |2 * s * s'| * |t' - t| * |1 - t * t'| ≤ 2 * |t' - t| * 2 := by gcongr
    _ = 4 * |t' - t| := by ring

/-- **The circle chain.** For every `κ > 0` there are `m` and half-angles `(a i, b i)` (exact unit
vectors) with steps `≤ κ`, running from `(0, -1)` to `(0, 1) = -(0, -1)`. -/
theorem circle_chain (κ : ℝ) (hκ : 0 < κ) : ∃ m : ℕ, ∃ a b : ℕ → ℝ,
    (∀ i ≤ m, a i ^ 2 + b i ^ 2 = 1) ∧
    (∀ i < m, |a (i + 1) - a i| ≤ κ ∧ |b (i + 1) - b i| ≤ κ) ∧ a m = -a 0 ∧ b m = -b 0 := by
  -- step `h ≤ κ/8` with `m h = 1`
  obtain ⟨η, hη, hηκ⟩ := exists_pos_mul_le hκ 8
  obtain ⟨tη, -, htη⟩ := exists_inv_pos hη
  obtain ⟨n, hn⟩ := exists_nat_gt tη
  set m := n + 1
  have hm : (0 : ℝ) < m := by positivity
  obtain ⟨h, hh, hmh⟩ := exists_inv_pos hm
  have hhη : h ≤ η := by
    -- `h = h (η tη) < h m η = η`
    have : tη ≤ m := by simp only [m]; push_cast; linarith
    calc h = h * (η * tη) := by rw [htη, mul_one]
      _ ≤ h * (η * m) := by gcongr
      _ = η * (m * h) := by ring
      _ = η := by rw [hmh, mul_one]
  set t : ℕ → ℝ := fun i => -1 + 2 * i * h
  have ht : ∀ i ≤ m, |t i| ≤ 1 := fun i hi => by
    have h1 : (i : ℝ) * h ≤ 1 := by
      rw [← hmh]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh.le
    have h0 : 0 ≤ (i : ℝ) * h := by positivity
    exact abs_le.2 ⟨by simp only [t]; linarith, by simp only [t]; linarith⟩
  have hex : ∀ i ≤ m, ∃ s : ℝ, 0 < s ∧ (1 + t i ^ 2) * s = 1 := fun i _ => by
    obtain ⟨s, hs, e⟩ := exists_inv_pos (show (0 : ℝ) < 1 + t i ^ 2 by positivity)
    exact ⟨s, hs, e⟩
  obtain ⟨s, hs⟩ := nat_choice m hex
  refine ⟨m, fun i => (1 - t i ^ 2) * s i, fun i => 2 * t i * s i, fun i hi => ?_,
    fun i hi => ?_, ?_, ?_⟩
  · have e := (hs i hi).2
    linear_combination ((1 + t i ^ 2) * s i + 1) * e
  · have hst := half_angle_step (hs i hi.le).2 (hs (i + 1) hi).2 (hs i hi.le).1 (hs (i + 1) hi).1
      (ht i hi.le) (ht (i + 1) hi)
    have hdt : |t (i + 1) - t i| = 2 * h := by
      simp only [t]; push_cast
      rw [show -1 + 2 * ((i : ℝ) + 1) * h - (-1 + 2 * i * h) = 2 * h by ring,
        abs_of_pos (by positivity)]
    rw [hdt] at hst
    exact ⟨hst.1.trans (by linarith), hst.2.trans (by linarith)⟩
  · have h0 : t 0 = -1 := by simp [t]
    have hm' : t m = 1 := by
      simp only [t]; rw [mul_assoc, hmh]; ring
    simp only [h0, hm']; ring
  · have h0 : t 0 = -1 := by simp [t]
    have hm' : t m = 1 := by
      simp only [t]; rw [mul_assoc, hmh]; ring
    have e0 := (hs 0 (Nat.zero_le _)).2
    have em := (hs m le_rfl).2
    rw [h0] at e0
    rw [hm'] at em
    simp only [h0, hm']
    linarith

/-- The point `e²` of the plane for a half-angle `e = (a, b)`. -/
def sqPt (a b : ℝ) : Fin 2 → ℝ := ![a ^ 2 - b ^ 2, 2 * a * b]

lemma sqPt_bdd {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) : Bdd 1 (sqPt a b) := by
  intro k
  fin_cases k
  · show |a ^ 2 - b ^ 2| ≤ 1
    exact abs_le.2 ⟨by nlinarith [sq_nonneg a], by nlinarith [sq_nonneg b]⟩
  · show |2 * a * b| ≤ 1
    exact abs_le.2 ⟨by nlinarith [sq_nonneg (a + b)], by nlinarith [sq_nonneg (a - b)]⟩

lemma sqPt_close {a b a' b' κ : ℝ} (h : a ^ 2 + b ^ 2 = 1) (h' : a' ^ 2 + b' ^ 2 = 1)
    (ha : |a' - a| ≤ κ) (hb : |b' - b| ≤ κ) : Close (4 * κ) (sqPt a b) (sqPt a' b') := by
  have ha1 := abs_le_one_of_sq_add h
  have hb1 := abs_le_one_of_sq_add (a := b) (b := a) (by linarith)
  have ha1' := abs_le_one_of_sq_add h'
  have hb1' := abs_le_one_of_sq_add (a := b') (b := a') (by linarith)
  intro k
  fin_cases k
  · show |(a ^ 2 - b ^ 2) - (a' ^ 2 - b' ^ 2)| ≤ 4 * κ
    have e : (a ^ 2 - b ^ 2) - (a' ^ 2 - b' ^ 2) = (a - a') * (a + a') - (b - b') * (b + b') := by
      ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_sub_comm a, abs_sub_comm b]
    have h1 : |a + a'| ≤ 2 := (abs_add_le _ _).trans (by linarith)
    have h2 : |b + b'| ≤ 2 := (abs_add_le _ _).trans (by linarith)
    have := mul_le_mul ha h1 (abs_nonneg _) ((abs_nonneg _).trans ha)
    have := mul_le_mul hb h2 (abs_nonneg _) ((abs_nonneg _).trans hb)
    linarith
  · show |2 * a * b - 2 * a' * b'| ≤ 4 * κ
    have e : 2 * a * b - 2 * a' * b' = 2 * ((a - a') * b + a' * (b - b')) := by ring
    rw [e, abs_mul, abs_two]
    have h3 : |(a - a') * b + a' * (b - b')| ≤ 2 * κ := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_sub_comm a, abs_sub_comm b]
      have := mul_le_mul ha hb1 (abs_nonneg _) ((abs_nonneg _).trans ha)
      have := mul_le_mul ha1' hb (abs_nonneg _) zero_le_one
      linarith
    linarith

/-! ## The gluing -/

/-- **No Möbius relation survives chain lifting.** If the real points of `B` (with projection
`Pr` to the plane) have the chain lifting property from the plane, and
`μ · (p, q) M(x, y) (u, v)ᵀ = 1` holds at every real point of `B` (`(x, y) = Pr w`), with
`p, q, u, v, μ` bounded and `u, v` Lipschitz on boxes, then `False`. -/
theorem no_moebius_lift {N : ℕ} (Pt : (Fin N → ℝ) → Prop) (Pr : (Fin N → ℝ) → (Fin 2 → ℝ))
    (hL : ChainLift (fun _ : Fin 2 → ℝ => True) Pt Pr) (p q u v μ : (Fin N → ℝ) → ℝ)
    (hrel : ∀ w, Pt w → μ w * (p w * ((1 + Pr w 0) * u w + Pr w 1 * v w) +
      q w * (Pr w 1 * u w + (1 - Pr w 0) * v w)) = 1)
    (hbd : ∀ C, ∃ B, ∀ w, Pt w → Bdd C w →
      |p w| ≤ B ∧ |q w| ≤ B ∧ |μ w| ≤ B ∧ |u w| ≤ B ∧ |v w| ≤ B)
    (hlip : ∀ C, ∃ L, 0 ≤ L ∧ LipR C L u ∧ LipR C L v) : False := by
  obtain ⟨C', hC'⟩ := hL 1
  obtain ⟨B, hB⟩ := hbd C'
  set Cm := |B| + 1
  have hCm : 1 ≤ Cm := by simp only [Cm]; linarith [abs_nonneg B]
  have hBC : B ≤ Cm := by simp only [Cm]; linarith [le_abs_self B]
  obtain ⟨L, hL0, hLu, hLv⟩ := hlip C'
  obtain ⟨δM, hδM, hδM1⟩ := exists_pos_mul_le one_pos (32 * Cm ^ 3)
  have hδMC : 16 * Cm ^ 3 * δM < 1 :=
    lt_of_two_mul_le (by linarith) one_pos
  obtain ⟨ε, hε, hε1, hεL⟩ := exists_pos_mul_le₂ one_pos hδM (8 * Cm ^ 3) L
  obtain ⟨δ, hδ, hlift⟩ := hC' ε hε
  obtain ⟨κ, hκ, hκδ, hκM⟩ := exists_pos_mul_le₂ hδ hδM 4 1
  rw [one_mul] at hκM
  obtain ⟨m, a, b, hab, hstep, ha, hb⟩ := circle_chain κ hκ
  -- the base chain in the plane
  have hz : IsChain (fun _ : Fin 2 → ℝ => True) 1 δ m (fun i => sqPt (a i) (b i)) :=
    ⟨by simp only [sqPt, ha, hb]; congr 1 <;> ring_nf, fun _ _ => trivial,
      fun i hi => sqPt_bdd (hab i hi),
      fun i hi => (sqPt_close (hab i hi.le) (hab (i + 1) hi) (hstep i hi).1 (hstep i hi).2).mono
        hκδ⟩
  obtain ⟨m', w, ι, hw, hι, hcl⟩ := hlift m _ hz
  have hιm := hι.le
  have hbw : ∀ j ≤ m', ∀ f ∈ [p, q, μ, u, v], |f (w j)| ≤ Cm := by
    intro j hj f hf
    obtain ⟨h1, h2, h3, h4, h5⟩ := hB (w j) (hw.mem j hj) (hw.bdd j hj)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> linarith
  refine moebius_approx Cm ε δM m' (fun j => a (ι j)) (fun j => b (ι j)) (fun j => u (w j))
    (fun j => v (w j)) (fun j => p (w j)) (fun j => q (w j)) (fun j => μ (w j))
    (fun j => Pr (w j) 0) (fun j => Pr (w j) 1) hCm hε.le hε1 hδM.le hδMC
    (fun j hj => hab _ (hιm j hj)) (fun j hj => hrel _ (hw.mem j hj))
    (fun j hj => hbw j hj p (by simp)) (fun j hj => hbw j hj q (by simp))
    (fun j hj => hbw j hj μ (by simp)) (fun j hj => hbw j hj u (by simp))
    (fun j hj => hbw j hj v (by simp)) (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
    (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) ?_ ?_ ?_ ?_
  · exact hcl j hj 0
  · exact hcl j hj 1
  · rcases hι.step j hj with e | e
    · simp only [e, sub_self, abs_zero]; exact hδM.le
    · simp only [e]
      exact (hstep _ (by have := hιm (j + 1) hj; omega)).1.trans hκM
  · rcases hι.step j hj with e | e
    · simp only [e, sub_self, abs_zero]; exact hδM.le
    · simp only [e]
      exact (hstep _ (by have := hιm (j + 1) hj; omega)).2.trans hκM
  · exact (hLu _ _ _ (hw.bdd _ hj) (hw.bdd j hj.le) (hw.step j hj).symm).trans hεL
  · exact (hLv _ _ _ (hw.bdd _ hj) (hw.bdd j hj.le) (hw.step j hj).symm).trans hεL
  · simp only [hw.closed]
  · simp only [hw.closed]
  · simp only [hι.last, hι.zero, ha]
  · simp only [hι.last, hι.zero, hb]

end BezoutCounterexample.Constructive
