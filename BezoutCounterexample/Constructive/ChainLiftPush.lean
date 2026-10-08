import Mathlib
import BezoutCounterexample.Constructive.ChainLiftBasic

/-!
# The push-off along the weighted sphere (`~/COLL/bezout-positive.tex`, §2.3)

A closed chain of real points of `B` may pass near the centre `V(𝔭)`, where `ν = 0`. We replace
it by a chain on which `ν ≥ ρ > 0`, staying close to the original and keeping it closed.

Charts: near a valid base point, chart coordinates `φ` (head coordinates `x_{hd m}`, weights
`w m ≥ 1`, at least two of them: codimension `k ≥ 2`) give exact real points with prescribed
coordinates (`sect`, from Newton–Kantorovich), are locally injective with a Lipschitz inverse
(`inj`), and compare `ν` with the weighted size of the head (`nu_lo`: some `|x_m| ≥ r^{w_m}`
gives `ν ≥ c r^D`, Lemma 2.3 = `NuBound`; `nu_hi`: all `|x_m| ≤ r^{w_m}` gives `ν ≤ c' r^D`).

Construction:
1. Each chain point gets a representative `p_i`: itself if `ν ≥ θ` (cover), otherwise, in a chart
   valid at `z_i`, the point with head coordinate `x_{hd 0}` replaced by `3 r^{w₀}` unless it is
   already `≥ r^{w₀}` in size (`exists_rep`). So `ν(p_i) ≥ c r^D`.
2. Consecutive representatives are joined, in a chart valid at one of the two base points, by a
   *relay path* (`relay`): three linear segments in chart coordinates along each of which one head
   coordinate keeps its sign and stays `≥ ε^{w}` in size. When the two endpoints are good only in
   the same coordinate with opposite signs, a second head coordinate takes over: this is the one
   place where `k ≥ 2` (connectedness of the weighted sphere `S^{k-1}`) is used. The segments are
   discretised (`segPt`) and realised by exact points (`sect`, `inj`).
3. Everything has the same number `M = 3K` of steps per original step, so the new chain is
   `cat M σ`, reindexed by `j ↦ j / M`.

All comparisons are made with a margin (`cotrans`); no excluded middle on `ℝ`.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

/-! ## Sign decisions with a margin -/

theorem sign_of_two_le_abs {x e : ℝ} (he : 0 < e) (h : 2 * e ≤ |x|) :
    2 * e ≤ x ∨ x ≤ -(2 * e) := by
  rcases cotrans (neg_lt_self he) x with hx | hx
  · left
    apply le_of_not_lt'
    intro hlt
    have : |x| < 2 * e := abs_lt.2 ⟨lt_trans (neg_lt_neg (lt_two_mul' he)) hx, hlt⟩
    linarith
  · right
    apply le_of_not_lt'
    intro hlt
    have : |x| < 2 * e := abs_lt.2 ⟨hlt, hx.trans (lt_two_mul' he)⟩
    linarith

theorem three_way {x e : ℝ} (he : 0 < e) : e ≤ x ∨ x ≤ -e ∨ |x| ≤ 2 * e := by
  rcases cotrans (lt_two_mul' he) x with hx | hx
  · exact Or.inl hx.le
  · rcases cotrans (neg_lt_neg (lt_two_mul' he)) x with hx' | hx'
    · exact Or.inr (Or.inr (abs_le.2 ⟨hx'.le, hx.le⟩))
    · exact Or.inr (Or.inl hx'.le)

/-! ## Relay paths in chart coordinates -/

section Relay
variable {n k : ℕ} (hd : Fin k → Fin n)

/-- A segment `[a, b]` along which the head coordinate `hd m` keeps its sign and size `≥ e m`. -/
def GoodSeg (e : Fin k → ℝ) (a b : Fin n → ℝ) : Prop :=
  ∃ m, (e m ≤ a (hd m) ∧ e m ≤ b (hd m)) ∨ (a (hd m) ≤ -e m ∧ b (hd m) ≤ -e m)

/-- Another head index (codimension `k ≥ 2`). -/
def other (hk : 2 ≤ k) (m : Fin k) : Fin k :=
  if m.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

lemma other_ne (hk : 2 ≤ k) (m : Fin k) : other hk m ≠ m := by
  unfold other
  split_ifs with h
  · intro e; rw [← e] at h; simp at h
  · intro e; apply h; rw [← e]

lemma close_update {c : Fin n → ℝ} {i : Fin n} {v Δ : ℝ} (hΔ : 0 ≤ Δ) (h : |v - c i| ≤ Δ) :
    Close Δ (Function.update c i v) c := by
  intro x
  by_cases hx : x = i
  · subst hx; simpa using h
  · rw [Function.update_of_ne hx]; simpa using hΔ

/-- **Relay path.** Two chart points that are good (some head coordinate of size `≥ 2e`) are
joined by three good segments, with corners near the first point. -/
theorem relay (hk : 2 ≤ k) (hinj : Function.Injective hd) (e : Fin k → ℝ) (he : ∀ m, 0 < e m)
    (E₀ : ℝ) (hE₀ : ∀ m, e m ≤ E₀) (c c' : Fin n → ℝ) (Δ : ℝ) (hΔ : Close Δ c c')
    (hc : ∃ m, 2 * e m ≤ |c (hd m)|) (hc' : ∃ m, 2 * e m ≤ |c' (hd m)|) :
    ∃ q₁ q₂, GoodSeg hd e c q₁ ∧ GoodSeg hd e q₁ q₂ ∧ GoodSeg hd e q₂ c' ∧
      Close (Δ + 5 * E₀) q₁ c ∧ Close (Δ + 5 * E₀) q₂ c := by
  obtain ⟨m, hm⟩ := hc
  obtain ⟨m', hm'⟩ := hc'
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans (hΔ (hd m))
  have hE0 : 0 ≤ E₀ := (he m).le.trans (hE₀ m)
  have hΔ5 : Δ ≤ Δ + 5 * E₀ := by linarith
  have hcc' : Close (Δ + 5 * E₀) c' c := (hΔ.symm).mono hΔ5
  have hcc : Close (Δ + 5 * E₀) c c := close_refl (by linarith) c
  have sm := sign_of_two_le_abs (he m) hm
  have sm' := sign_of_two_le_abs (he m') hm'
  have hem := (he m).le
  have hem' := (he m').le
  by_cases hmm : m = m'
  · subst hmm
    -- same coordinate: same sign → one segment; opposite signs → relay through `other m`
    have same : ∀ (s : Prop), (GoodSeg hd e c c') → ∃ q₁ q₂, GoodSeg hd e c q₁ ∧
        GoodSeg hd e q₁ q₂ ∧ GoodSeg hd e q₂ c' ∧ Close (Δ + 5 * E₀) q₁ c ∧
        Close (Δ + 5 * E₀) q₂ c := fun _ h => by
      refine ⟨c, c, ⟨m, ?_⟩, ⟨m, ?_⟩, h, hcc, hcc⟩
      · rcases sm with h1 | h1
        · exact Or.inl ⟨by linarith, by linarith⟩
        · exact Or.inr ⟨by linarith, by linarith⟩
      · rcases sm with h1 | h1
        · exact Or.inl ⟨by linarith, by linarith⟩
        · exact Or.inr ⟨by linarith, by linarith⟩
    -- the relay through `l`
    have opp : ∃ q₁ q₂, GoodSeg hd e c q₁ ∧ GoodSeg hd e q₁ q₂ ∧ GoodSeg hd e q₂ c' ∧
        Close (Δ + 5 * E₀) q₁ c ∧ Close (Δ + 5 * E₀) q₂ c := by
      set l := other hk m
      have hl : hd l ≠ hd m := fun h => other_ne hk m (hinj h)
      have hel := (he l).le
      -- the value of `c'` at `hd m` is good with its sign
      have gm' : ∀ v : ℝ, (2 * e m ≤ v ∨ v ≤ -(2 * e m)) → v = c' (hd m) →
          (e m ≤ v ∧ e m ≤ c' (hd m)) ∨ (v ≤ -e m ∧ c' (hd m) ≤ -e m) := by
        intro v hv hvc
        rcases hv with h | h
        · exact Or.inl ⟨by linarith, by rw [← hvc]; linarith⟩
        · exact Or.inr ⟨by linarith, by rw [← hvc]; linarith⟩
      rcases three_way (x := c (hd l)) (he l) with hcl | hcl | hcl
      · -- `l` is already good at `c`
        refine ⟨Function.update c (hd m) (c' (hd m)), Function.update c (hd m) (c' (hd m)),
          ⟨l, Or.inl ⟨hcl, ?_⟩⟩, ⟨m, ?_⟩, ⟨m, ?_⟩, ?_, ?_⟩
        · rw [Function.update_of_ne hl]; exact hcl
        · simp only [Function.update_self]
          rcases sm' with h | h
          · exact Or.inl ⟨by linarith, by linarith⟩
          · exact Or.inr ⟨by linarith, by linarith⟩
        · simp only [Function.update_self]; exact gm' _ sm' rfl
        · exact close_update (by linarith) (by rw [abs_sub_comm]; exact (hΔ (hd m)).trans hΔ5)
        · exact close_update (by linarith) (by rw [abs_sub_comm]; exact (hΔ (hd m)).trans hΔ5)
      · refine ⟨Function.update c (hd m) (c' (hd m)), Function.update c (hd m) (c' (hd m)),
          ⟨l, Or.inr ⟨hcl, ?_⟩⟩, ⟨m, ?_⟩, ⟨m, ?_⟩, ?_, ?_⟩
        · rw [Function.update_of_ne hl]; exact hcl
        · simp only [Function.update_self]
          rcases sm' with h | h
          · exact Or.inl ⟨by linarith, by linarith⟩
          · exact Or.inr ⟨by linarith, by linarith⟩
        · simp only [Function.update_self]; exact gm' _ sm' rfl
        · exact close_update (by linarith) (by rw [abs_sub_comm]; exact (hΔ (hd m)).trans hΔ5)
        · exact close_update (by linarith) (by rw [abs_sub_comm]; exact (hΔ (hd m)).trans hΔ5)
      · -- `c_l` is small: set it to `3 e_l` first
        have h5 : |3 * e l - c (hd l)| ≤ Δ + 5 * E₀ := by
          have := abs_le.1 hcl
          have h1 : |3 * e l - c (hd l)| ≤ 5 * e l := abs_le.2 ⟨by linarith, by linarith⟩
          linarith [hE₀ l]
        refine ⟨Function.update c (hd l) (3 * e l), Function.update c' (hd l) (3 * e l),
          ⟨m, ?_⟩, ⟨l, Or.inl ⟨?_, ?_⟩⟩, ⟨m, ?_⟩, close_update (by linarith) h5, ?_⟩
        · rw [Function.update_of_ne hl.symm]
          rcases sm with h | h
          · exact Or.inl ⟨by linarith, by linarith⟩
          · exact Or.inr ⟨by linarith, by linarith⟩
        · simp only [Function.update_self]; linarith
        · simp only [Function.update_self]; linarith
        · rw [Function.update_of_ne hl.symm]; exact gm' _ sm' rfl
        · intro x
          by_cases hx : x = hd l
          · subst hx; simpa using h5
          · rw [Function.update_of_ne hx]; exact hcc' x
    rcases sm with h1 | h1 <;> rcases sm' with h2 | h2
    · exact same True ⟨m, Or.inl ⟨by linarith, by linarith⟩⟩
    · exact opp
    · exact opp
    · exact same True ⟨m, Or.inr ⟨by linarith, by linarith⟩⟩
  · -- different coordinates: move `hd m'` first, keeping `hd m`
    have hne : hd m ≠ hd m' := fun h => hmm (hinj h)
    refine ⟨Function.update c (hd m') (c' (hd m')), Function.update c (hd m') (c' (hd m')),
      ⟨m, ?_⟩, ⟨m', ?_⟩, ⟨m', ?_⟩, ?_, ?_⟩
    · rw [Function.update_of_ne hne]
      rcases sm with h | h
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
    · simp only [Function.update_self]
      rcases sm' with h | h
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
    · simp only [Function.update_self]
      rcases sm' with h | h
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
    · exact close_update (by linarith) (by rw [abs_sub_comm]; exact (hΔ (hd m')).trans hΔ5)
    · exact close_update (by linarith) (by rw [abs_sub_comm]; exact (hΔ (hd m')).trans hΔ5)

/-! ## Discretised segments -/

/-- Point `t` of the discretisation of `[a, b]` with step `τ` (`K τ = 1`). -/
def segPt (τ : ℝ) (a b : Fin n → ℝ) (t : ℕ) : Fin n → ℝ := fun x => a x + (t * τ) * (b x - a x)

lemma segPt_zero (τ : ℝ) (a b : Fin n → ℝ) : segPt τ a b 0 = a := by
  funext x; simp [segPt]

lemma segPt_last {τ : ℝ} {K : ℕ} (hK : (K : ℝ) * τ = 1) (a b : Fin n → ℝ) :
    segPt τ a b K = b := by
  funext x; simp only [segPt, hK]; ring

lemma segPt_step {τ Λ : ℝ} (hτ : 0 ≤ τ) {a b : Fin n → ℝ} (h : Close Λ a b) (t : ℕ) :
    Close (τ * Λ) (segPt τ a b t) (segPt τ a b (t + 1)) := by
  intro x
  have e : segPt τ a b t x - segPt τ a b (t + 1) x = τ * (a x - b x) := by
    simp only [segPt]; push_cast; ring
  rw [e, abs_mul, abs_of_nonneg hτ]
  exact mul_le_mul_of_nonneg_left (h x) hτ

lemma segPt_unit {τ : ℝ} {K : ℕ} (hτ : 0 ≤ τ) (hK : (K : ℝ) * τ = 1) {t : ℕ} (ht : t ≤ K) :
    0 ≤ (t : ℝ) * τ ∧ (t : ℝ) * τ ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  rw [← hK]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht) hτ

lemma segPt_close {τ ρ : ℝ} {K : ℕ} (hτ : 0 ≤ τ) (hK : (K : ℝ) * τ = 1) {a b c : Fin n → ℝ}
    (ha : Close ρ a c) (hb : Close ρ b c) {t : ℕ} (ht : t ≤ K) : Close ρ (segPt τ a b t) c := by
  obtain ⟨h0, h1⟩ := segPt_unit hτ hK ht
  set lam := (t : ℝ) * τ
  intro x
  have e : segPt τ a b t x - c x = (1 - lam) * (a x - c x) + lam * (b x - c x) := by
    simp only [segPt, lam]; ring
  rw [e]
  calc |(1 - lam) * (a x - c x) + lam * (b x - c x)|
      ≤ |(1 - lam) * (a x - c x)| + |lam * (b x - c x)| := abs_add_le _ _
    _ = (1 - lam) * |a x - c x| + lam * |b x - c x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg h0]
    _ ≤ (1 - lam) * ρ + lam * ρ :=
        add_le_add (mul_le_mul_of_nonneg_left (ha x) (by linarith))
          (mul_le_mul_of_nonneg_left (hb x) h0)
    _ = ρ := by ring

lemma segPt_good {τ : ℝ} {K : ℕ} (hτ : 0 ≤ τ) (hK : (K : ℝ) * τ = 1) {e : Fin k → ℝ}
    {a b : Fin n → ℝ} (h : GoodSeg hd e a b) {t : ℕ} (ht : t ≤ K) :
    ∃ m, e m ≤ |segPt τ a b t (hd m)| := by
  obtain ⟨h0, h1⟩ := segPt_unit hτ hK ht
  set lam := (t : ℝ) * τ
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have e1 : segPt τ a b t (hd m) = (1 - lam) * a (hd m) + lam * b (hd m) := by
    simp only [segPt, lam]; ring
  rw [e1]
  have h2 : 0 ≤ 1 - lam := by linarith
  rcases hm with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have : e m ≤ (1 - lam) * a (hd m) + lam * b (hd m) := by
      have := mul_le_mul_of_nonneg_left ha h2
      have := mul_le_mul_of_nonneg_left hb h0
      nlinarith
    exact this.trans (le_abs_self _)
  · have : (1 - lam) * a (hd m) + lam * b (hd m) ≤ -e m := by
      have := mul_le_mul_of_nonneg_left ha h2
      have := mul_le_mul_of_nonneg_left hb h0
      nlinarith
    exact (by linarith : e m ≤ -((1 - lam) * a (hd m) + lam * b (hd m))).trans (neg_le_abs _)

end Relay

/-! ## Charts and push-off data -/

/-- A chart: chart coordinates `φ`, head indices `hd` (at least two: codimension `k ≥ 2`), weights
`w ≥ 1`, and the validity predicate of base points (`|h| ≥ θ` on a cover element). -/
structure Chart (N : ℕ) where
  n : ℕ
  k : ℕ
  hk : 2 ≤ k
  hd : Fin k → Fin n
  hd_inj : Function.Injective hd
  w : Fin k → ℕ
  hw : ∀ m, w m ≠ 0
  φ : (Fin N → ℝ) → (Fin n → ℝ)
  valid : (Fin N → ℝ) → Prop

/-- **Push-off data on the box `C`.** A cover (`ν ≥ θ`, or some chart is valid), and uniform
constants for the charts near valid base points: exact points with prescribed chart
coordinates (`sect`) and a Lipschitz inverse (`inj`), both from Newton–Kantorovich
(`Kantorovich.lean`, `chord_lip` below); Lipschitz chart coordinates (`lipφ`); and the two
comparisons of `ν` with the head (`nu_lo` from the pure-power identities, `NuBound`; `nu_hi`
from `F_t` being weighted monomial). -/
structure PushData (N : ℕ) (Pt : (Fin N → ℝ) → Prop) (ν : (Fin N → ℝ) → ℝ) (C : ℝ) where
  J : Type
  ch : J → Chart N
  θ : ℝ
  hθ : 0 < θ
  cover : ∀ z, Pt z → Bdd C z → θ ≤ ν z ∨ ∃ j, (ch j).valid z
  D : ℕ
  hD : D ≠ 0
  R : ℝ
  K : ℝ
  S : ℝ
  Lφ : ℝ
  clo : ℝ
  chi : ℝ
  hR : 0 < R
  hK : 0 ≤ K
  hS : 0 < S
  hL : 0 ≤ Lφ
  hclo : 0 < clo
  hchi : 0 ≤ chi
  sect : ∀ j z, Pt z → Bdd C z → (ch j).valid z → ∀ c e, e ≤ R → Close e c ((ch j).φ z) →
    ∃ z', Pt z' ∧ (ch j).φ z' = c ∧ Close (K * e) z' z
  inj : ∀ j z, Pt z → Bdd C z → (ch j).valid z → ∀ z' z'', Pt z' → Pt z'' → Close S z' z →
    Close S z'' z → ∀ e, Close e ((ch j).φ z') ((ch j).φ z'') → Close (K * e) z' z''
  lipφ : ∀ j z, Pt z → Bdd C z → (ch j).valid z → ∀ z' z'' e, Close S z' z → Close S z'' z →
    Close e z' z'' → Close (Lφ * e) ((ch j).φ z') ((ch j).φ z'')
  nu_lo : ∀ j z, Pt z → Bdd C z → (ch j).valid z → ∀ z', Pt z' → Close S z' z → ∀ r, 0 < r →
    r ≤ 1 → ∀ m, r ^ (ch j).w m ≤ |(ch j).φ z' ((ch j).hd m)| → clo * r ^ D ≤ ν z'
  nu_hi : ∀ j z, Pt z → Bdd C z → (ch j).valid z → ∀ z', Pt z' → Close S z' z → ∀ r, 0 < r →
    r ≤ 1 → (∀ m, |(ch j).φ z' ((ch j).hd m)| ≤ r ^ (ch j).w m) → ν z' ≤ chi * r ^ D

lemma eq_of_close_zero {N : ℕ} {w w' : Fin N → ℝ} (h : Close 0 w w') : w = w' :=
  funext fun k => sub_eq_zero.1 (abs_nonpos_iff.1 (h k))

/-- The four corners of a relay path. -/
def corner4 {α : Type*} (c q₁ q₂ c' : α) : ℕ → α
  | 0 => c
  | 1 => q₁
  | 2 => q₂
  | _ => c'

namespace PushData

variable {N : ℕ} {Pt : (Fin N → ℝ) → Prop} {ν : (Fin N → ℝ) → ℝ} {C : ℝ}
  (P : PushData N Pt ν C)

/-- **Representatives** (step 1): every chain point has a nearby point with `ν ≥ c r^D`; it is
the point itself when the cover says `ν ≥ θ` (`none`), and otherwise a chart valid there is
recorded. -/
theorem exists_rep (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (h5 : 5 * r ≤ P.R) (hS5 : 5 * P.K * r ≤ P.S)
    (hθr : P.clo * r ^ P.D ≤ P.θ) (z : Fin N → ℝ) (hz : Pt z) (hzC : Bdd C z) :
    ∃ x : (Fin N → ℝ) × Option P.J, Pt x.1 ∧ Close (5 * P.K * r) x.1 z ∧
      P.clo * r ^ P.D ≤ ν x.1 ∧ (x.2 = none → x.1 = z) ∧
      (∀ j, x.2 = some j → (P.ch j).valid z) := by
  have h0 : 0 ≤ 5 * P.K * r := by have := P.hK; positivity
  rcases P.cover z hz hzC with hν | ⟨j, hj⟩
  · exact ⟨(z, none), hz, close_refl h0 z, hθr.trans hν, fun _ => rfl, fun j h => by simp at h⟩
  set ch := P.ch j
  have hzS : Close P.S z z := close_refl P.hS.le z
  set m₀ : Fin ch.k := ⟨0, by have := ch.hk; omega⟩
  set a := r ^ ch.w m₀
  have ha : 0 < a := pow_pos hr _
  have har : a ≤ r := pow_le_of_le_one hr.le hr1 (ch.hw m₀)
  have keep : a ≤ |ch.φ z (ch.hd m₀)| → ∃ x : (Fin N → ℝ) × Option P.J, Pt x.1 ∧
      Close (5 * P.K * r) x.1 z ∧ P.clo * r ^ P.D ≤ ν x.1 ∧ (x.2 = none → x.1 = z) ∧
      (∀ j', x.2 = some j' → (P.ch j').valid z) := fun h =>
    ⟨(z, some j), hz, close_refl h0 z, P.nu_lo j z hz hzC hj z hz hzS r hr hr1 m₀ h,
      fun h' => by simp at h', fun j' h' => by simp only [Option.some.injEq] at h'; subst h'; exact hj⟩
  rcases three_way (x := ch.φ z (ch.hd m₀)) ha with hx | hx | hx
  · exact keep (hx.trans (le_abs_self _))
  · exact keep ((le_neg.1 hx).trans (neg_le_abs _))
  · -- move the head coordinate `hd m₀` to `3a`
    have hdev : |3 * a - ch.φ z (ch.hd m₀)| ≤ 5 * r := by
      have := abs_le.1 hx
      exact abs_le.2 ⟨by linarith, by linarith⟩
    obtain ⟨z', hz', hφ, hcl⟩ := P.sect j z hz hzC hj
      (Function.update (ch.φ z) (ch.hd m₀) (3 * a)) (5 * r) h5
      (close_update (by linarith) hdev)
    have hcl' : Close (5 * P.K * r) z' z := hcl.mono (le_of_eq (by ring))
    have hgood : a ≤ |ch.φ z' (ch.hd m₀)| := by
      rw [hφ, Function.update_self, abs_of_pos (by positivity)]; linarith
    exact ⟨(z', some j), hz', hcl', P.nu_lo j z hz hzC hj z' hz' (hcl'.mono hS5) r hr hr1 m₀ hgood,
      fun h' => by simp at h', fun j' h' => by simp only [Option.some.injEq] at h'; subst h'; exact hj⟩

/-- A point with `ν` above the `nu_hi` bound at scale `3ε` is good at scale `ε` in every chart
valid nearby (finite search with margins). -/
theorem coord_good (j : P.J) (b : Fin N → ℝ) (hb : Pt b) (hbC : Bdd C b)
    (hbv : (P.ch j).valid b) (p : Fin N → ℝ) (hp : Pt p) (hpb : Close P.S p b) (ε : ℝ)
    (hε : 0 < ε) (h3 : 3 * ε ≤ 1) (hν : P.chi * (3 * ε) ^ P.D < ν p) :
    ∃ m, 2 * ε ^ (P.ch j).w m ≤ |(P.ch j).φ p ((P.ch j).hd m)| := by
  set ch := P.ch j
  have h23 : (2 : ℝ) < 3 := by
    have h := lt_add_of_pos_right (2 : ℝ) one_pos
    rwa [show (2 : ℝ) + 1 = 3 by norm_num] at h
  have hsplit : ∀ m, 2 * ε ^ ch.w m < |ch.φ p (ch.hd m)| ∨
      |ch.φ p (ch.hd m)| < 3 * ε ^ ch.w m := fun m =>
    cotrans (mul_lt_mul_of_pos_right h23 (pow_pos hε (ch.w m))) _
  rcases exists_or_forall_finset hsplit Finset.univ with ⟨m, -, hm⟩ | hall
  · exact ⟨m, hm.le⟩
  exfalso
  have hle : ∀ m, |ch.φ p (ch.hd m)| ≤ (3 * ε) ^ ch.w m := fun m => by
    have h1 : (3 : ℝ) ≤ 3 ^ ch.w m := le_self_pow₀ (by norm_num) (ch.hw m)
    have h2 : 3 * ε ^ ch.w m ≤ (3 * ε) ^ ch.w m := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hε.le _)
    exact ((hall m (Finset.mem_univ m)).le).trans h2
  have := P.nu_hi j b hb hbC hbv p hp hpb (3 * ε) (by positivity) h3 hle
  exact lt_irrefl _ (lt_of_le_of_lt this hν)

/-- **One realised relay segment** (step 2): two good points near a valid base point are joined
by `3K + 1` exact points with `ν ≥ c ε^D`, consecutive ones `δ₁`-close. -/
theorem relay_segment (j : P.J) (b : Fin N → ℝ) (hb : Pt b) (hbC : Bdd C b)
    (hbv : (P.ch j).valid b) (p p' : Fin N → ℝ) (hp : Pt p) (hp' : Pt p') (u : ℝ) (hu : 0 ≤ u)
    (hpb : Close u p b) (hp'b : Close u p' b) (huS : u ≤ P.S) (ε : ℝ) (hε : 0 < ε)
    (h3 : 3 * ε ≤ 1) (hνp : P.chi * (3 * ε) ^ P.D < ν p) (hνp' : P.chi * (3 * ε) ^ P.D < ν p')
    (Kseg : ℕ) (hKseg : 0 < Kseg) (τ : ℝ) (hτ : 0 ≤ τ) (hKτ : (Kseg : ℝ) * τ = 1) (δ₁ : ℝ)
    (hdev : P.Lφ * u + (P.Lφ * u + P.Lφ * u + 5 * ε) ≤ P.R)
    (hKdev : P.K * (P.Lφ * u + (P.Lφ * u + P.Lφ * u + 5 * ε)) ≤ P.S)
    (hmesh : P.K * (τ * ((P.Lφ * u + P.Lφ * u + 5 * ε) + (P.Lφ * u + P.Lφ * u + 5 * ε))) ≤ δ₁) :
    ∃ σ : ℕ → Fin N → ℝ, σ 0 = p ∧ σ (3 * Kseg) = p' ∧
      (∀ t < 3 * Kseg, Close δ₁ (σ t) (σ (t + 1))) ∧
      ∀ t ≤ 3 * Kseg, Pt (σ t) ∧
        Close (P.K * (P.Lφ * u + (P.Lφ * u + P.Lφ * u + 5 * ε))) (σ t) b ∧
        P.clo * ε ^ P.D ≤ ν (σ t) := by
  set ch := P.ch j
  have hbS : Close P.S b b := close_refl P.hS.le b
  have hpS : Close P.S p b := hpb.mono huS
  have hp'S : Close P.S p' b := hp'b.mono huS
  set c := ch.φ p
  set c' := ch.φ p'
  have hcb : Close (P.Lφ * u) c (ch.φ b) := P.lipφ j b hb hbC hbv p b u hpS hbS hpb
  have hc'b : Close (P.Lφ * u) c' (ch.φ b) := P.lipφ j b hb hbC hbv p' b u hp'S hbS hp'b
  have hcc' : Close (P.Lφ * u + P.Lφ * u) c c' := hcb.trans hc'b.symm
  set e : Fin ch.k → ℝ := fun m => ε ^ ch.w m
  have he : ∀ m, 0 < e m := fun m => pow_pos hε _
  have hε1 : ε ≤ 1 := by linarith
  have heE : ∀ m, e m ≤ ε := fun m => pow_le_of_le_one hε.le hε1 (ch.hw m)
  obtain ⟨q₁, q₂, g₁, g₂, g₃, hq₁, hq₂⟩ := relay ch.hd ch.hk ch.hd_inj e he ε heE c c' _ hcc'
    (P.coord_good j b hb hbC hbv p hp hpS ε hε h3 hνp)
    (P.coord_good j b hb hbC hbv p' hp' hp'S ε hε h3 hνp')
  set B := P.Lφ * u + P.Lφ * u + 5 * ε
  have hB0 : 0 ≤ B := by
    have := P.hL; positivity
  set Q := corner4 c q₁ q₂ c'
  have hQc : ∀ i, Close B (Q i) c := by
    intro i
    match i with
    | 0 => exact close_refl hB0 c
    | 1 => exact hq₁
    | 2 => exact hq₂
    | i + 3 => exact hcc'.symm.mono (by have := hε.le; simp only [B]; linarith)
  have hgood : ∀ i < 3, GoodSeg ch.hd e (Q i) (Q (i + 1)) := by
    intro i hi
    match i, hi with
    | 0, _ => exact g₁
    | 1, _ => exact g₂
    | 2, _ => exact g₃
  set σs : ℕ → ℕ → Fin ch.n → ℝ := fun i t => segPt τ (Q i) (Q (i + 1)) t
  set path := cat Kseg σs
  have hjoin : ∀ i < 3, σs i Kseg = σs (i + 1) 0 := fun i _ => by
    simp only [σs, segPt_last hKτ, segPt_zero]
  have hpath_close : ∀ t ≤ 3 * Kseg, Close B (path t) c := by
    have := cat_prop hKseg σs (fun _ x => Close B x c) (m := 3)
      (fun i _ t ht => segPt_close hτ hKτ (hQc i) (hQc (i + 1)) ht.le)
      (by simp only [σs, segPt_zero]; exact hQc 3)
    exact this
  have hpath_good : ∀ t ≤ 3 * Kseg, ∃ m, e m ≤ |path t (ch.hd m)| := by
    have := cat_prop hKseg σs (fun _ x => ∃ m, e m ≤ |x (ch.hd m)|) (m := 3)
      (fun i hi t ht => segPt_good ch.hd hτ hKτ (hgood i hi) ht.le)
      (by
        simp only [σs, segPt_zero]
        obtain ⟨m, hm⟩ := P.coord_good j b hb hbC hbv p' hp' hp'S ε hε h3 hνp'
        exact ⟨m, by have := he m; show e m ≤ |c' (ch.hd m)|; linarith⟩)
    exact this
  have hpath_step : ∀ t < 3 * Kseg, Close (τ * (B + B)) (path t) (path (t + 1)) :=
    cat_step hKseg σs _ hjoin fun i _ t _ => segPt_step hτ ((hQc i).trans (hQc (i + 1)).symm) t
  have hpath0 : path 0 = c := by
    simp only [path, cat, Nat.zero_div, Nat.zero_mod, σs, segPt_zero]; rfl
  have hpathL : path (3 * Kseg) = c' := by
    have := cat_mul_add hKseg σs 3 0 hKseg
    simp only [add_zero] at this
    simp only [path, this, σs, segPt_zero]; rfl
  set dev := P.Lφ * u + B
  have hdev' : ∀ t ≤ 3 * Kseg, Close dev (path t) (ch.φ b) := fun t ht =>
    ((hpath_close t ht).trans hcb).mono (le_of_eq (by simp only [dev]; ring))
  have hex : ∀ t ≤ 3 * Kseg, ∃ z', Pt z' ∧ ch.φ z' = path t ∧ Close (P.K * dev) z' b :=
    fun t ht => P.sect j b hb hbC hbv (path t) dev hdev (hdev' t ht)
  obtain ⟨σ, hσ⟩ := nat_choice (3 * Kseg) hex
  have hσS : ∀ t ≤ 3 * Kseg, Close P.S (σ t) b := fun t ht => (hσ t ht).2.2.mono hKdev
  have hend : ∀ t ≤ 3 * Kseg, ∀ q, Pt q → Close P.S q b → ch.φ q = path t → σ t = q := by
    intro t ht q hq hqb hφq
    have h := P.inj j b hb hbC hbv (σ t) q (hσ t ht).1 hq (hσS t ht) hqb 0
      (by rw [(hσ t ht).2.1, hφq]; exact close_refl le_rfl _)
    rw [mul_zero] at h
    exact eq_of_close_zero h
  refine ⟨σ, hend 0 (Nat.zero_le _) p hp hpS hpath0.symm,
    hend _ le_rfl p' hp' hp'S hpathL.symm, fun t ht => ?_, fun t ht => ⟨(hσ t ht).1,
      (hσ t ht).2.2, ?_⟩⟩
  · have h := P.inj j b hb hbC hbv (σ t) (σ (t + 1)) (hσ t ht.le).1 (hσ _ ht).1
      (hσS t ht.le) (hσS _ ht) _ (by rw [(hσ t ht.le).2.1, (hσ _ ht).2.1]; exact hpath_step t ht)
    exact h.mono hmesh
  · obtain ⟨m, hm⟩ := hpath_good t ht
    exact P.nu_lo j b hb hbC hbv (σ t) (hσ t ht).1 (hσS t ht) ε hε hε1 m
      (by rw [(hσ t ht).2.1]; exact hm)

end PushData

/-- `i % m` indexes the same chain point as `i`, for `i ≤ m` (closed chains). -/
lemma IsChain.mod_eq {N : ℕ} {Pt : (Fin N → ℝ) → Prop} {C δ : ℝ} {m : ℕ} {z : ℕ → Fin N → ℝ}
    (hz : IsChain Pt C δ m z) : ∀ i ≤ m, i % m ≤ m ∧ z (i % m) = z i := by
  intro i hi
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.mod_zero]; exact ⟨hi, trivial⟩
  rcases Nat.lt_or_ge i m with h | h
  · exact ⟨(Nat.mod_lt _ hm).le, by rw [Nat.mod_eq_of_lt h]⟩
  · have : i = m := le_antisymm hi h
    subst this
    exact ⟨by simp, by rw [Nat.mod_self, hz.closed]⟩

namespace PushData

variable {N : ℕ} {Pt : (Fin N → ℝ) → Prop} {ν : (Fin N → ℝ) → ℝ} {C : ℝ}
  (P : PushData N Pt ν C)

lemma mesh_aux {X t δ τ n : ℝ} (hδt : δ * t = 1) (hn : X * t ≤ n) (hnτ : n * τ = 1)
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) : X * τ ≤ δ := by
  have e : X * τ = (X * t) * (δ * τ) := by
    calc X * τ = X * (δ * t) * τ := by rw [hδt, mul_one]
      _ = (X * t) * (δ * τ) := by ring
  rw [e]
  calc (X * t) * (δ * τ) ≤ n * (δ * τ) := mul_le_mul_of_nonneg_right hn (mul_nonneg hδ hτ)
    _ = δ * (n * τ) := by ring
    _ = δ := by rw [hnτ, mul_one]

include P in
/-- **The push-off (§2.3).** For every `ε > 0` there is `ρ > 0` such that, for every `δ₁ > 0`,
closed `δ`-chains in the box `C` (`δ` explicit) are replaced by closed `δ₁`-chains in the box
`C + 1` on which `ν ≥ ρ`, each new point `ε`-close to the original point it is indexed by. -/
theorem push_off : ∀ ε, 0 < ε → ∃ ρ, 0 < ρ ∧ ∀ δ₁, 0 < δ₁ → ∃ δ, 0 < δ ∧
    ∀ m z, IsChain Pt C δ m z → ∃ m' w ι, IsChain Pt (C + 1) δ₁ m' w ∧
      (∀ j ≤ m', ρ ≤ ν (w j)) ∧ IsReindex m m' ι ∧ ∀ j ≤ m', Close ε (w j) (z (ι j)) := by
  intro ε hε
  have hK := P.hK
  have hL := P.hL
  have hclo := P.hclo
  have hchi := P.hchi
  -- `κ`: the ratio between the two scales
  obtain ⟨κ, hκ, hκ1, hκ2⟩ := exists_pos_mul_le₂ hclo one_pos (2 * (P.chi * 3 ^ P.D)) 1
  rw [one_mul] at hκ2
  set A := 3 * P.Lφ * (5 * P.K + 1) + 5
  have hA : 0 ≤ A := by positivity
  have hA5 : 5 ≤ A := by
    have : 0 ≤ 3 * P.Lφ * (5 * P.K + 1) := by positivity
    simp only [A]; linarith
  obtain ⟨r, hr, hrl⟩ := exists_pos_mul_le_list
    [(3, 1), (5, P.R), (5 * P.K + 1, P.S), (A, P.R), (P.K * A, P.S), (P.K * A + 1, ε),
      (P.K * A + 1, 1), (P.clo, P.θ)]
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by positivity, by first | exact P.hR | exact P.hS | exact hε | exact P.hθ | norm_num⟩)
  have c1 : 3 * r ≤ 1 := hrl (3, 1) (by simp)
  have c2 : 5 * r ≤ P.R := hrl (5, P.R) (by simp)
  have c3 : (5 * P.K + 1) * r ≤ P.S := hrl (5 * P.K + 1, P.S) (by simp)
  have c4 : A * r ≤ P.R := hrl (A, P.R) (by simp)
  have c5 : P.K * A * r ≤ P.S := hrl (P.K * A, P.S) (by simp)
  have c6 : (P.K * A + 1) * r ≤ ε := hrl (P.K * A + 1, ε) (by simp)
  have c7 : (P.K * A + 1) * r ≤ 1 := hrl (P.K * A + 1, 1) (by simp)
  have c8 : P.clo * r ≤ P.θ := hrl (P.clo, P.θ) (by simp)
  have hr1 : r ≤ 1 := by linarith
  have hrD : r ^ P.D ≤ r := pow_le_of_le_one hr.le hr1 P.hD
  have hrD0 : 0 < r ^ P.D := pow_pos hr _
  set ε' := κ * r
  have hε' : 0 < ε' := mul_pos hκ hr
  have hε'r : ε' ≤ r := by simp only [ε']; nlinarith
  have h3ε' : 3 * ε' ≤ 1 := by linarith
  set ρ := P.clo * ε' ^ P.D
  have hρ : 0 < ρ := mul_pos hclo (pow_pos hε' _)
  have hρr : ρ ≤ P.clo * r ^ P.D :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε'.le hε'r _) hclo.le
  -- representatives are above the `nu_hi` bound at scale `3ε'`
  have hgap : P.chi * (3 * ε') ^ P.D < P.clo * r ^ P.D := by
    have hκD : κ ^ P.D ≤ κ := pow_le_of_le_one hκ.le hκ2 P.hD
    have e : P.chi * (3 * ε') ^ P.D = (P.chi * 3 ^ P.D * κ ^ P.D) * r ^ P.D := by
      simp only [ε']; ring
    rw [e]
    have h1 : 2 * (P.chi * 3 ^ P.D * κ ^ P.D) ≤ P.clo := by
      have := mul_le_mul_of_nonneg_left hκD (by positivity : (0 : ℝ) ≤ 2 * (P.chi * 3 ^ P.D))
      linarith
    have h2 : 2 * ((P.chi * 3 ^ P.D * κ ^ P.D) * r ^ P.D) ≤ P.clo * r ^ P.D := by
      have := mul_le_mul_of_nonneg_right h1 hrD0.le
      linarith
    exact lt_of_two_mul_le h2 (mul_pos hclo hrD0)
  refine ⟨ρ, hρ, fun δ₁ hδ₁ => ?_⟩
  -- the number of discretisation steps
  obtain ⟨t₁, -, ht₁⟩ := exists_inv_pos hδ₁
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (P.K * (2 * A * r) * t₁)
  set Kseg := n₀ + 1
  have hKseg : 0 < Kseg := Nat.succ_pos _
  obtain ⟨τ, hτ, hKτ⟩ := exists_inv_pos (show (0 : ℝ) < Kseg by exact_mod_cast hKseg)
  set M := 3 * Kseg
  have hM : 0 < M := by simp only [M]; omega
  obtain ⟨δ, hδ, hδr2, hδδ₁⟩ := exists_pos_mul_le₂ hr hδ₁ 2 1
  rw [one_mul] at hδδ₁
  have hδr : δ ≤ r := by linarith
  refine ⟨δ, hδ, fun m z hz => ?_⟩
  -- the common slack `u` and the deviation bounds
  set u := 5 * P.K * r + 2 * δ
  have hu : 0 ≤ u := by positivity
  have hu' : u ≤ (5 * P.K + 1) * r := by simp only [u]; linarith
  have hBdev : P.Lφ * u + P.Lφ * u + 5 * ε' ≤ A * r := by
    have : P.Lφ * u ≤ P.Lφ * ((5 * P.K + 1) * r) := mul_le_mul_of_nonneg_left hu' hL
    simp only [A]; nlinarith
  have hdev : P.Lφ * u + (P.Lφ * u + P.Lφ * u + 5 * ε') ≤ A * r := by
    have : P.Lφ * u ≤ P.Lφ * ((5 * P.K + 1) * r) := mul_le_mul_of_nonneg_left hu' hL
    simp only [A]; nlinarith
  have hKdev : P.K * (P.Lφ * u + (P.Lφ * u + P.Lφ * u + 5 * ε')) ≤ P.K * A * r := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hdev hK
  have hmesh : P.K * (τ * ((P.Lφ * u + P.Lφ * u + 5 * ε') + (P.Lφ * u + P.Lφ * u + 5 * ε')))
      ≤ δ₁ := by
    have h1 : P.K * (τ * ((P.Lφ * u + P.Lφ * u + 5 * ε') + (P.Lφ * u + P.Lφ * u + 5 * ε')))
        ≤ (P.K * (2 * A * r)) * τ := by
      have := mul_le_mul_of_nonneg_left (add_le_add hBdev hBdev) (mul_nonneg hK hτ.le)
      nlinarith
    have h2 : (P.K * (2 * A * r)) * τ ≤ δ₁ :=
      mesh_aux ht₁ (by simp only [Kseg]; push_cast; linarith) hKτ hδ₁.le hτ.le
    exact h1.trans h2
  have hεc : P.K * (P.Lφ * u + (P.Lφ * u + P.Lφ * u + 5 * ε')) + δ ≤ ε := by
    linarith [hKdev, hδr, c6]
  have hbd : P.K * (P.Lφ * u + (P.Lφ * u + P.Lφ * u + 5 * ε')) + δ ≤ 1 := by
    linarith [hKdev, hδr, c7]
  have h5K : 5 * P.K * r + δ ≤ (P.K * A + 1) * r := by
    have : 5 * P.K * r ≤ P.K * A * r :=
      mul_le_mul_of_nonneg_right (by linarith [mul_le_mul_of_nonneg_left hA5 hK]) hr.le
    linarith
  -- step 1: representatives, indexed modulo `m` so that `p m = p 0`
  have h5S : 5 * P.K * r ≤ P.S := by linarith [mul_nonneg hr.le (show (0:ℝ) ≤ 1 by norm_num)]
  have hθr : P.clo * r ^ P.D ≤ P.θ := (mul_le_mul_of_nonneg_left hrD hclo.le).trans c8
  obtain ⟨f, hf⟩ := nat_choice m fun i hi => P.exists_rep r hr hr1 c2 h5S hθr
    (z i) (hz.mem i hi) (hz.bdd i hi)
  set p : ℕ → Fin N → ℝ := fun i => (f (i % m)).1
  set o : ℕ → Option P.J := fun i => (f (i % m)).2
  have hp : ∀ i ≤ m, Pt (p i) ∧ Close (5 * P.K * r) (p i) (z i) ∧
      P.clo * r ^ P.D ≤ ν (p i) ∧ (o i = none → p i = z i) ∧
      (∀ j, o i = some j → (P.ch j).valid (z i)) := fun i hi => by
    have := hf (i % m) (hz.mod_eq i hi).1
    rw [(hz.mod_eq i hi).2] at this
    exact this
  have hpm : p m = p 0 := by simp only [p, Nat.mod_self, Nat.zero_mod]
  have hpu : ∀ i ≤ m, Close u (p i) (z i) := fun i hi =>
    (hp i hi).2.1.mono (by simp only [u]; linarith)
  -- step 2: segments
  have hseg : ∀ i ≤ m, ∃ σ : ℕ → Fin N → ℝ, σ 0 = p i ∧ (i < m → σ M = p (i + 1) ∧
      (∀ t < M, Close δ₁ (σ t) (σ (t + 1))) ∧
      ∀ t ≤ M, Pt (σ t) ∧ Bdd (C + 1) (σ t) ∧ ρ ≤ ν (σ t) ∧ Close ε (σ t) (z i)) := by
    intro i hi
    rcases Nat.lt_or_ge i m with him | him
    swap
    · exact ⟨fun _ => p i, rfl, fun h => absurd h (by omega)⟩
    have hi1 : i + 1 ≤ m := him
    obtain ⟨hPi, hci, hνi, hni, hvi⟩ := hp i hi
    obtain ⟨hPi', hci', hνi', hni', hvi'⟩ := hp (i + 1) hi1
    have hzi := hz.mem i hi
    have hzi' := hz.mem _ hi1
    have hzC := hz.bdd i hi
    have hzC' := hz.bdd _ hi1
    have hst := hz.step i him
    -- the relay case, with base `b ∈ {z i, z (i+1)}` and `Close δ b (z i)`
    have relay_case : ∀ j b, Pt b → Bdd C b → (P.ch j).valid b → Close δ b (z i) →
        Close u (p i) b → Close u (p (i + 1)) b → ∃ σ : ℕ → Fin N → ℝ, σ 0 = p i ∧
          (i < m → σ M = p (i + 1) ∧ (∀ t < M, Close δ₁ (σ t) (σ (t + 1))) ∧
          ∀ t ≤ M, Pt (σ t) ∧ Bdd (C + 1) (σ t) ∧ ρ ≤ ν (σ t) ∧ Close ε (σ t) (z i)) := by
      intro j b hb hbC hbv hbz h1 h2
      obtain ⟨σ, h0, hL', hstep, hprop⟩ := P.relay_segment j b hb hbC hbv (p i) (p (i + 1))
        hPi hPi' u hu h1 h2 (hu'.trans c3) ε' hε' h3ε' (lt_of_lt_of_le hgap hνi)
        (lt_of_lt_of_le hgap hνi') Kseg hKseg τ hτ.le hKτ δ₁ (hdev.trans c4)
        (hKdev.trans c5) hmesh
      refine ⟨σ, h0, fun _ => ⟨hL', hstep, fun t ht => ?_⟩⟩
      obtain ⟨hPt, hcl, hν⟩ := hprop t ht
      have hcz := hcl.trans hbz
      refine ⟨hPt, ?_, ?_, hcz.mono hεc⟩
      · exact (hzC.of_close hcz).mono (by linarith)
      · exact hν
    cases hoi : o i with
    | some j =>
      exact relay_case j (z i) hzi hzC (hvi j hoi) (close_refl hδ.le _) (hpu i hi)
        (((hp _ hi1).2.1.trans hst.symm).mono (by simp only [u]; linarith))
    | none =>
      cases hoi' : o (i + 1) with
      | some j =>
        have hpz : p i = z i := hni hoi
        exact relay_case j (z (i + 1)) hzi' hzC' (hvi' j hoi') hst.symm
          (by rw [hpz]; exact hst.mono (by simp only [u]; linarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 5 by norm_num) hK) hr.le])) (hpu _ hi1)
      | none =>
        have hpz : p i = z i := hni hoi
        have hpz' : p (i + 1) = z (i + 1) := hni' hoi'
        refine ⟨fun t => if t < M then p i else p (i + 1), by simp [hM], fun _ => ⟨by simp,
          fun t ht => ?_, fun t ht => ?_⟩⟩
        · by_cases h' : t + 1 < M
          · simp only [show t < M by omega, h', ite_true]; exact close_refl hδ₁.le _
          · simp only [ht, h', ite_true, ite_false]
            rw [hpz, hpz']; exact hst.mono hδδ₁
        · by_cases h' : t < M
          · simp only [h', ite_true]
            refine ⟨hPi, (hzC.of_close hci).mono (by linarith), hρr.trans hνi,
              hci.mono (by linarith)⟩
          · simp only [h', ite_false]
            have hcz : Close (5 * P.K * r + δ) (p (i + 1)) (z i) := hci'.trans hst.symm
            refine ⟨hPi', (hzC.of_close hcz).mono (by linarith), hρr.trans hνi',
              hcz.mono (by linarith)⟩
  obtain ⟨g, hg⟩ := nat_choice m hseg
  -- step 3: assemble
  have hprops : ∀ j ≤ m * M, Pt (cat M g j) ∧ Bdd (C + 1) (cat M g j) ∧ ρ ≤ ν (cat M g j) ∧
      Close ε (cat M g j) (z (j / M)) := by
    refine cat_prop hM g (fun i x => Pt x ∧ Bdd (C + 1) x ∧ ρ ≤ ν x ∧ Close ε x (z i))
      (fun i hi t ht => ((hg i hi.le).2 hi).2.2 t ht.le) ?_
    rw [(hg m le_rfl).1]
    obtain ⟨hPm, hcm, hνm, -, -⟩ := hp m le_rfl
    exact ⟨hPm, ((hz.bdd m le_rfl).of_close hcm).mono (by linarith), hρr.trans hνm,
      hcm.mono (by linarith)⟩
  refine ⟨m * M, cat M g, (· / M), ⟨?_, ?_, ?_, ?_⟩, ?_, isReindex_div hM m, ?_⟩
  · have h1 := cat_mul_add hM g m 0 hM
    have h2 := cat_mul_add hM g 0 0 hM
    simp only [add_zero, zero_mul] at h1 h2
    rw [h1, h2, (hg m le_rfl).1, (hg 0 (Nat.zero_le _)).1, hpm]
  · intro j hj; exact (hprops j hj).1
  · intro j hj; exact (hprops j hj).2.1
  · exact cat_step hM g (Close δ₁)
      (fun i hi => by rw [((hg i hi.le).2 hi).1, (hg (i + 1) hi).1])
      (fun i hi t ht => ((hg i hi.le).2 hi).2.1 t ht)
  · intro j hj; exact (hprops j hj).2.2.1
  · intro j hj; exact (hprops j hj).2.2.2

end PushData

end BezoutCounterexample.Constructive
