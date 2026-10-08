import Mathlib
import BezoutCounterexample.Constructive.ChainLiftBasic

/-!
# The lift off `V(𝔭)` is an explicit formula (`~/COLL/bezout-positive.tex`, §2.1)

A torsor step `B → B'` has filtration generators `gᵢ ∈ F_{dᵢ}`, even exponents `Eᵢ` with
`Eᵢ dᵢ = D₂ (= 2 d!)` and `ν = Σ gᵢ^{Eᵢ}`. At a real point of `B` with `ν > 0` the normalized lift
is `s = ν^{1/D₂} > 0`, `yᵢ = gᵢ / s^{dᵢ}`, `σᵢ = yᵢ^{Eᵢ-1}`; then `Σ yᵢσᵢ = 1`, `|yᵢ|, |σᵢ| ≤ 1`.
No equation is solved: every relation of `B'` holds because evaluation at `t = 1/s` is a ring map.
That last fact is the hypothesis `lift_mem` of `OffStep` (semantic form of the step).

* `IsNormLift`: the relation between `g` and `(s, y, σ)`; `exists_normLift` (one root, one
  inverse: the two primitives of `ChainLiftBasic`), `IsNormLift.sum_eq_one`, `abs_y_le`,
  `abs_sigma_le`, `s_le` (`s ≤ 1 + V` when `ν ≤ V`).
* `normLift_modulus`: on `{ν ≥ ρ}` the lift has an explicit modulus, stated without division as
  `ρ² |Δ| ≤ Λ δ`.
* `OffStep.lift_chain`: every closed `δ`-chain in `{ν ≥ ρ}` lifts to a closed `ε`-chain of real
  points of `B'` with the same projections, `δ` explicit in `ρ, ε` and the box.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

/-! ## Two elementary estimates -/

/-- `|aⁿ - bⁿ| ≤ n Mⁿ⁻¹ |a - b|` when `|a|, |b| ≤ M`. -/
theorem abs_pow_sub_pow_le' {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) :
    ∀ n : ℕ, |a ^ (n + 1) - b ^ (n + 1)| ≤ (n + 1) * M ^ n * |a - b| := by
  have hM : 0 ≤ M := (abs_nonneg a).trans ha
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) = a * (a ^ (n + 1) - b ^ (n + 1)) +
        (a - b) * b ^ (n + 1) := by ring
    rw [e]
    have h1 : |b ^ (n + 1)| ≤ M ^ (n + 1) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hb _
    calc |a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1)|
        ≤ |a| * |a ^ (n + 1) - b ^ (n + 1)| + |a - b| * |b ^ (n + 1)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ M * ((n + 1) * M ^ n * |a - b|) + |a - b| * M ^ (n + 1) := by
          gcongr
      _ = ((n + 1 : ℕ) + 1 : ℝ) * M ^ (n + 1) * |a - b| := by push_cast; ring

/-- The same, for any exponent, with the weaker constant `n Mⁿ` (when `M ≥ 1`). -/
theorem abs_pow_sub_pow_le_of_one {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) (hM : 1 ≤ M)
    (n : ℕ) : |a ^ n - b ^ n| ≤ n * M ^ n * |a - b| := by
  rcases n with _ | n
  · simp
  · refine (abs_pow_sub_pow_le' ha hb n).trans ?_
    have : M ^ n ≤ M ^ (n + 1) := pow_le_pow_right₀ hM (Nat.le_succ n)
    push_cast
    gcongr

/-! ## The normalized lift -/

variable {ι : Type*} [Fintype ι]

/-- The normalized lift `(s, y, σ)` of the values `g` of the generators. -/
structure IsNormLift (g : ι → ℝ) (d E : ι → ℕ) (D₂ : ℕ) (s : ℝ) (y σ : ι → ℝ) : Prop where
  pos : 0 < s
  root : s ^ D₂ = ∑ i, g i ^ E i
  scale : ∀ i, g i = s ^ d i * y i
  sigma : ∀ i, σ i = y i ^ (E i - 1)

section
variable {d E : ι → ℕ} {D₂ : ℕ} (hD : D₂ ≠ 0) (hEd : ∀ i, E i * d i = D₂) (hE : ∀ i, Even (E i))
include hD hEd

omit [Fintype ι] in
lemma E_ne_zero (i : ι) : E i ≠ 0 := by
  intro h; apply hD; rw [← hEd i, h, zero_mul]

lemma IsNormLift.sum_pow_eq_one {g : ι → ℝ} {s : ℝ} {y σ : ι → ℝ}
    (h : IsNormLift g d E D₂ s y σ) : ∑ i, y i ^ E i = 1 := by
  obtain ⟨t, -, hst⟩ := exists_inv_pos h.pos
  have h1 : s ^ D₂ * ∑ i, y i ^ E i = s ^ D₂ := by
    rw [Finset.mul_sum]
    conv_rhs => rw [h.root]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h.scale i, mul_pow, ← pow_mul, mul_comm (d i), hEd i]
  have h2 : (s * t) ^ D₂ * ∑ i, y i ^ E i = (s * t) ^ D₂ := by
    rw [mul_pow, mul_comm (s ^ D₂), mul_assoc, h1]
  rwa [hst, one_pow, one_mul] at h2

lemma IsNormLift.sum_eq_one {g : ι → ℝ} {s : ℝ} {y σ : ι → ℝ}
    (h : IsNormLift g d E D₂ s y σ) : ∑ i, y i * σ i = 1 := by
  rw [← h.sum_pow_eq_one hD hEd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h.sigma i, ← pow_succ']
  congr 1
  have := E_ne_zero hD hEd i
  omega

include hE in
lemma IsNormLift.abs_y_le {g : ι → ℝ} {s : ℝ} {y σ : ι → ℝ}
    (h : IsNormLift g d E D₂ s y σ) (i : ι) : |y i| ≤ 1 := by
  apply le_of_not_lt'
  intro hlt
  have h1 : 1 < |y i| ^ E i := one_lt_pow₀ hlt (E_ne_zero hD hEd i)
  rw [(hE i).pow_abs] at h1
  have h2 : y i ^ E i ≤ ∑ j, y j ^ E j :=
    Finset.single_le_sum (f := fun j => y j ^ E j) (fun j _ => (hE j).pow_nonneg _)
      (Finset.mem_univ i)
  rw [h.sum_pow_eq_one hD hEd] at h2
  linarith

include hE in
lemma IsNormLift.abs_sigma_le {g : ι → ℝ} {s : ℝ} {y σ : ι → ℝ}
    (h : IsNormLift g d E D₂ s y σ) (i : ι) : |σ i| ≤ 1 := by
  rw [h.sigma i, abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (h.abs_y_le hD hEd hE i)

lemma IsNormLift.s_le {g : ι → ℝ} {s : ℝ} {y σ : ι → ℝ} (h : IsNormLift g d E D₂ s y σ)
    {V : ℝ} (hV : ∑ i, g i ^ E i ≤ V) : s ≤ 1 + V := by
  apply le_of_not_lt'
  intro hlt
  have hV0 : 0 ≤ V := by
    have := h.root ▸ (pow_pos h.pos D₂).le
    linarith
  have h1 : 1 ≤ s := by linarith
  have h2 : s ≤ s ^ D₂ := le_self_pow₀ h1 hD
  rw [h.root] at h2
  linarith

omit hEd in
/-- **Existence of the normalized lift** where `ν > 0`. -/
theorem exists_normLift (g : ι → ℝ) (hν : 0 < ∑ i, g i ^ E i) :
    ∃ s y σ, IsNormLift g d E D₂ s y σ := by
  obtain ⟨s, hs, hsD⟩ := exists_root_pos hν hD
  obtain ⟨t, -, hst⟩ := exists_inv_pos hs
  refine ⟨s, fun i => g i * t ^ d i, fun i => (g i * t ^ d i) ^ (E i - 1),
    ⟨hs, hsD, fun i => ?_, fun _ => rfl⟩⟩
  calc g i = g i * (s * t) ^ d i := by rw [hst, one_pow, mul_one]
    _ = s ^ d i * (g i * t ^ d i) := by ring

/-! ## The modulus on `{ν ≥ ρ}` -/

include hE in
/-- **Modulus of the normalized lift.** For values with `|gᵢ| ≤ G`, `ν ≥ ρ`, and two lifts of
`δ`-close values, `ρ² |Δs|, ρ² |Δyᵢ|, ρ² |Δσᵢ| ≤ Λ δ`, with `Λ` explicit in `ρ, G`. -/
theorem normLift_modulus (G ρ : ℝ) (hρ : 0 < ρ) (hG : 0 ≤ G) :
    ∃ Λ, 0 ≤ Λ ∧ ∀ (g g' : ι → ℝ) s s' (y y' σ σ' : ι → ℝ) δ, 0 ≤ δ →
      IsNormLift g d E D₂ s y σ → IsNormLift g' d E D₂ s' y' σ' →
      (∀ i, |g i| ≤ G) → (∀ i, |g' i| ≤ G) → ρ ≤ ∑ i, g i ^ E i →
      (∀ i, |g i - g' i| ≤ δ) →
      ρ ^ 2 * |s - s'| ≤ Λ * δ ∧ (∀ i, ρ ^ 2 * |y i - y' i| ≤ Λ * δ) ∧
        (∀ i, ρ ^ 2 * |σ i - σ' i| ≤ Λ * δ) := by
  -- constants
  set V : ℝ := ∑ i, G ^ E i with hVdef
  set S : ℝ := 1 + V
  set G1 : ℝ := 1 + G
  set Lν : ℝ := ∑ i, (E i : ℝ) * G1 ^ E i
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun i _ => pow_nonneg hG _
  have hS1 : 1 ≤ S := by simp only [S]; linarith
  have hS0 : 0 ≤ S := by linarith
  have hG1 : 1 ≤ G1 := by simp only [G1]; linarith
  have hLν : 0 ≤ Lν := Finset.sum_nonneg fun i _ => by positivity
  set A : ι → ℝ := fun i => (E i : ℝ) * (S ^ D₂ * (ρ + d i * S ^ (d i + 1) * Lν))
  have hA : ∀ i, 0 ≤ A i := fun i => by positivity
  set Λ : ℝ := ρ * S * Lν + ∑ i, A i
  refine ⟨Λ, by positivity, ?_⟩
  intro g g' s s' y y' σ σ' δ hδ hl hl' hg hg' hρν hgg
  -- `ν ≤ V`, so `s, s' ≤ S`
  have hνV : ∀ u : ι → ℝ, (∀ i, |u i| ≤ G) → ∑ i, u i ^ E i ≤ V := fun u hu =>
    Finset.sum_le_sum fun i _ => by
      rw [← (hE i).pow_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hu i) _
  have hsS : |s| ≤ S := by
    rw [abs_of_pos hl.pos]; exact hl.s_le hD hEd (hνV g hg)
  have hs'S : |s'| ≤ S := by
    rw [abs_of_pos hl'.pos]; exact hl'.s_le hD hEd (hνV g' hg')
  -- `|ν - ν'| ≤ Lν δ`
  have hνν : |∑ i, g i ^ E i - ∑ i, g' i ^ E i| ≤ Lν * δ := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : |g i| ≤ G1 := (hg i).trans (by simp only [G1]; linarith)
    have h2 : |g' i| ≤ G1 := (hg' i).trans (by simp only [G1]; linarith)
    calc |g i ^ E i - g' i ^ E i| ≤ E i * G1 ^ E i * |g i - g' i| :=
          abs_pow_sub_pow_le_of_one h1 h2 hG1 _
      _ ≤ E i * G1 ^ E i * δ := by gcongr; exact hgg i
  -- `ρ |s - s'| ≤ S |ν - ν'|`
  have hss : ρ * |s - s'| ≤ S * (Lν * δ) := by
    set P : ℝ := ∑ k ∈ Finset.range D₂, s ^ k * s' ^ (D₂ - 1 - k)
    have hP : P * (s - s') = s ^ D₂ - s' ^ D₂ := geom_sum₂_mul s s' D₂
    have hP0 : s ^ (D₂ - 1) ≤ P := by
      have hmem : D₂ - 1 ∈ Finset.range D₂ := Finset.mem_range.2 (by omega)
      have := Finset.single_le_sum (f := fun k => s ^ k * s' ^ (D₂ - 1 - k))
        (fun k _ => mul_nonneg (pow_nonneg hl.pos.le _) (pow_nonneg hl'.pos.le _)) hmem
      simpa using this
    have hρP : ρ ≤ S * P := by
      have e : s ^ D₂ = s * s ^ (D₂ - 1) := by
        rw [← pow_succ']; congr 1; omega
      calc ρ ≤ s ^ D₂ := by rw [hl.root]; exact hρν
        _ = s * s ^ (D₂ - 1) := e
        _ ≤ S * P := mul_le_mul (le_of_abs_le hsS) hP0 (pow_nonneg hl.pos.le _) hS0
    have hdiff : |P| * |s - s'| ≤ Lν * δ := by
      rw [← abs_mul, hP, hl.root, hl'.root]; exact hνν
    have hP00 : 0 ≤ P := (pow_nonneg hl.pos.le _).trans hP0
    rw [abs_of_nonneg hP00] at hdiff
    calc ρ * |s - s'| ≤ (S * P) * |s - s'| := mul_le_mul_of_nonneg_right hρP (abs_nonneg _)
      _ = S * (P * |s - s'|) := by ring
      _ ≤ S * (Lν * δ) := mul_le_mul_of_nonneg_left hdiff hS0
  -- the `y` estimate
  have hy : ∀ i, ρ ^ 2 * |y i - y' i| ≤ S ^ D₂ * (ρ + d i * S ^ (d i + 1) * Lν) * δ := by
    intro i
    have hdD : d i ≤ D₂ := by
      rw [← hEd i]
      exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (E_ne_zero hD hEd i))
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hdD
    have e1 : s ^ d i * (y i - y' i) = (g i - g' i) - (s ^ d i - s' ^ d i) * y' i := by
      rw [hl.scale i, hl'.scale i]; ring
    have hsd : |s ^ d i - s' ^ d i| ≤ d i * S ^ d i * |s - s'| :=
      abs_pow_sub_pow_le_of_one hsS hs'S hS1 _
    have h1 : s ^ d i * |y i - y' i| ≤ δ + d i * S ^ d i * |s - s'| := by
      have : |s ^ d i * (y i - y' i)| = s ^ d i * |y i - y' i| := by
        rw [abs_mul, abs_of_pos (pow_pos hl.pos _)]
      rw [← this, e1]
      calc |(g i - g' i) - (s ^ d i - s' ^ d i) * y' i|
          ≤ |g i - g' i| + |s ^ d i - s' ^ d i| * |y' i| := by
            refine (abs_sub _ _).trans ?_; rw [abs_mul]
        _ ≤ δ + d i * S ^ d i * |s - s'| * 1 := by
            gcongr
            · exact hgg i
            · exact hl'.abs_y_le hD hEd hE i
        _ = δ + d i * S ^ d i * |s - s'| := by ring
    have h2 : ρ ≤ s ^ d i * S ^ D₂ := by
      have e : s ^ D₂ = s ^ d i * s ^ k := by rw [hk, pow_add]
      have hk' : s ^ k ≤ S ^ D₂ :=
        (pow_le_pow_left₀ hl.pos.le (le_of_abs_le hsS) k).trans
          (pow_le_pow_right₀ hS1 (by omega))
      calc ρ ≤ s ^ D₂ := by rw [hl.root]; exact hρν
        _ = s ^ d i * s ^ k := e
        _ ≤ s ^ d i * S ^ D₂ := mul_le_mul_of_nonneg_left hk' (pow_nonneg hl.pos.le _)
    have hSD : 0 ≤ S ^ D₂ := pow_nonneg hS0 _
    calc ρ ^ 2 * |y i - y' i| = ρ * (ρ * |y i - y' i|) := by ring
      _ ≤ ρ * ((s ^ d i * S ^ D₂) * |y i - y' i|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) hρ.le
      _ = S ^ D₂ * (ρ * (s ^ d i * |y i - y' i|)) := by ring
      _ ≤ S ^ D₂ * (ρ * (δ + d i * S ^ d i * |s - s'|)) := by gcongr
      _ = S ^ D₂ * (ρ * δ + d i * S ^ d i * (ρ * |s - s'|)) := by ring
      _ ≤ S ^ D₂ * (ρ * δ + d i * S ^ d i * (S * (Lν * δ))) := by gcongr
      _ = S ^ D₂ * (ρ + d i * S ^ (d i + 1) * Lν) * δ := by ring
  -- each bound is below `Λ δ`
  have hAΛ : ∀ i, A i * δ ≤ Λ * δ := fun i => by
    apply mul_le_mul_of_nonneg_right _ hδ
    have := Finset.single_le_sum (f := A) (fun j _ => hA j) (Finset.mem_univ i)
    have h0 : 0 ≤ ρ * S * Lν := by positivity
    simp only [Λ]; linarith
  have hE1 : ∀ i, (1 : ℝ) ≤ E i := fun i => by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (E_ne_zero hD hEd i)
  refine ⟨?_, fun i => ?_, fun i => ?_⟩
  · have h0 : 0 ≤ (∑ i, A i) * δ := mul_nonneg (Finset.sum_nonneg fun i _ => hA i) hδ
    calc ρ ^ 2 * |s - s'| = ρ * (ρ * |s - s'|) := by ring
      _ ≤ ρ * (S * (Lν * δ)) := mul_le_mul_of_nonneg_left hss hρ.le
      _ ≤ Λ * δ := by simp only [Λ]; nlinarith
  · have hB : 0 ≤ S ^ D₂ * (ρ + d i * S ^ (d i + 1) * Lν) * δ := by positivity
    calc ρ ^ 2 * |y i - y' i| ≤ S ^ D₂ * (ρ + d i * S ^ (d i + 1) * Lν) * δ := hy i
      _ ≤ A i * δ := by
          simp only [A]
          have := mul_le_mul_of_nonneg_right (hE1 i) hB
          linarith
      _ ≤ Λ * δ := hAΛ i
  · have hσy : |σ i - σ' i| ≤ E i * |y i - y' i| := by
      rw [hl.sigma i, hl'.sigma i]
      refine (abs_pow_sub_pow_le_of_one (hl.abs_y_le hD hEd hE i) (hl'.abs_y_le hD hEd hE i)
        le_rfl _).trans ?_
      rw [one_pow, mul_one]
      gcongr
      exact_mod_cast Nat.sub_le _ _
    calc ρ ^ 2 * |σ i - σ' i| ≤ ρ ^ 2 * (E i * |y i - y' i|) :=
          mul_le_mul_of_nonneg_left hσy (by positivity)
      _ = E i * (ρ ^ 2 * |y i - y' i|) := by ring
      _ ≤ E i * (S ^ D₂ * (ρ + d i * S ^ (d i + 1) * Lν) * δ) :=
          mul_le_mul_of_nonneg_left (hy i) (by positivity)
      _ = A i * δ := by simp only [A]; ring
      _ ≤ Λ * δ := hAΛ i

end

/-! ## Lifting chains over `{ν ≥ ρ}` -/

/-- **A torsor step, semantically.** Real points of `B` and `B'` are given by predicates; the
coordinates of `B'` are functions `Q (w, s, y, σ)` of a point of `B` and the torsor data
(polynomials, since `B' ⊆ B[t^{±1}][σ]/(Σ yᵢσᵢ - 1)` is generated by Rees-algebra elements
`b tᵏ = Σ c_γ y^γ s^{Σγd - k}`). `lift_mem` says that every relation of `B'` holds at such
data, i.e. evaluation at `t = 1/s` is a ring map. -/
structure OffStep (N N' : ℕ) (ι : Type*) [Fintype ι] where
  Pt : (Fin N → ℝ) → Prop
  Pt' : (Fin N' → ℝ) → Prop
  g : ι → (Fin N → ℝ) → ℝ
  d : ι → ℕ
  E : ι → ℕ
  D₂ : ℕ
  hD : D₂ ≠ 0
  hEd : ∀ i, E i * d i = D₂
  hE : ∀ i, Even (E i)
  Q : (Fin N → ℝ) → ℝ → (ι → ℝ) → (ι → ℝ) → (Fin N' → ℝ)
  π : (Fin N' → ℝ) → (Fin N → ℝ)
  lift_mem : ∀ w s y σ, Pt w → 0 < s → (∀ i, g i w = s ^ d i * y i) → ∑ i, y i * σ i = 1 →
    Pt' (Q w s y σ) ∧ π (Q w s y σ) = w
  g_bdd : ∀ C, ∃ G, 0 ≤ G ∧ ∀ i w, Bdd C w → |g i w| ≤ G
  g_lip : ∀ C, ∃ L, 0 ≤ L ∧ ∀ i, LipR C L (g i)
  Q_bdd : ∀ C S, ∃ C', ∀ w s y σ, Bdd C w → |s| ≤ S → (∀ i, |y i| ≤ 1) → (∀ i, |σ i| ≤ 1) →
    Bdd C' (Q w s y σ)
  Q_lip : ∀ C S, ∃ L, 0 ≤ L ∧ ∀ w w' s s' y y' σ σ' δ, Bdd C w → Bdd C w' → |s| ≤ S →
    |s'| ≤ S → (∀ i, |y i| ≤ 1) → (∀ i, |y' i| ≤ 1) → (∀ i, |σ i| ≤ 1) → (∀ i, |σ' i| ≤ 1) →
    Close δ w w' → |s - s'| ≤ δ → (∀ i, |y i - y' i| ≤ δ) → (∀ i, |σ i - σ' i| ≤ δ) →
    Close (L * δ) (Q w s y σ) (Q w' s' y' σ')

namespace OffStep

variable {N N' : ℕ} (T : OffStep N N' ι)

/-- `ν = Σ gᵢ^{Eᵢ}` as a function on real points of `B`. -/
def nu (w : Fin N → ℝ) : ℝ := ∑ i, T.g i w ^ T.E i

/-- **§2.1 for chains.** For every box there is a box for the lifts such that, for all
`ρ, ε > 0`, closed `δ`-chains in `{ν ≥ ρ}` lift to closed `ε`-chains of real points of `B'`
projecting exactly onto the given chain. -/
theorem lift_chain (C : ℝ) : ∃ C', ∀ ρ, 0 < ρ → ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
    ∀ m z, IsChain T.Pt C δ m z → (∀ i ≤ m, ρ ≤ T.nu (z i)) →
      ∃ w, IsChain T.Pt' C' ε m w ∧ ∀ i ≤ m, T.π (w i) = z i := by
  obtain ⟨G, hG0, hG⟩ := T.g_bdd C
  set V : ℝ := ∑ i, G ^ T.E i
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun i _ => pow_nonneg hG0 _
  set S : ℝ := 1 + V
  obtain ⟨C', hC'⟩ := T.Q_bdd C S
  refine ⟨C', fun ρ hρ ε hε => ?_⟩
  obtain ⟨Lg, hLg0, hLg⟩ := T.g_lip C
  obtain ⟨Λ, hΛ0, hΛ⟩ := normLift_modulus T.hD T.hEd T.hE G ρ hρ hG0
  obtain ⟨LQ, hLQ0, hLQ⟩ := T.Q_lip C S
  -- `τ`: the common closeness of the torsor data; `δ`: the input mesh
  obtain ⟨τ, hτ, hτε⟩ := exists_pos_mul_le hε LQ
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := exists_pos_mul_le₂ (mul_pos (pow_pos hρ 2) hτ) hτ (Λ * Lg) 1
  refine ⟨δ, hδ, fun m z hz hν => ?_⟩
  have hνV : ∀ w, Bdd C w → T.nu w ≤ V := fun w hw =>
    Finset.sum_le_sum fun i _ => by
      rw [← (T.hE i).pow_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hG i w hw) _
  -- lifts at every point
  have hex : ∀ i ≤ m, ∃ x : ℝ × (ι → ℝ) × (ι → ℝ),
      IsNormLift (fun j => T.g j (z i)) T.d T.E T.D₂ x.1 x.2.1 x.2.2 := fun i hi => by
    obtain ⟨s, y, σ, h⟩ := exists_normLift T.hD (fun j => T.g j (z i))
      (lt_of_lt_of_le hρ (hν i hi))
    exact ⟨(s, y, σ), h⟩
  obtain ⟨f, hf⟩ := nat_choice m hex
  -- the lift of `z i` uses the data at `i % m`, so that the lifted chain closes
  have hmod : ∀ i ≤ m, i % m ≤ m ∧ z (i % m) = z i := by
    intro i hi
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.mod_zero]; exact ⟨hi, trivial⟩
    rcases Nat.lt_or_ge i m with h | h
    · exact ⟨(Nat.mod_lt _ hm).le, by rw [Nat.mod_eq_of_lt h]⟩
    · have : i = m := le_antisymm hi h
      subst this
      exact ⟨by simp, by rw [Nat.mod_self, hz.closed]⟩
  have hL : ∀ i ≤ m, IsNormLift (fun j => T.g j (z i)) T.d T.E T.D₂ (f (i % m)).1
      (f (i % m)).2.1 (f (i % m)).2.2 := fun i hi => by
    have := hf (i % m) (hmod i hi).1
    rwa [(hmod i hi).2] at this
  set w : ℕ → Fin N' → ℝ := fun i => T.Q (z i) (f (i % m)).1 (f (i % m)).2.1 (f (i % m)).2.2
  have hsS : ∀ i ≤ m, |(f (i % m)).1| ≤ S := fun i hi => by
    rw [abs_of_pos (hL i hi).pos]
    exact (hL i hi).s_le T.hD T.hEd (hνV _ (hz.bdd i hi))
  refine ⟨w, ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩, fun i hi => ?_⟩
  · simp only [w, Nat.mod_self, Nat.zero_mod, hz.closed]
  · exact (T.lift_mem _ _ _ _ (hz.mem i hi) (hL i hi).pos (hL i hi).scale
      ((hL i hi).sum_eq_one T.hD T.hEd)).1
  · exact hC' _ _ _ _ (hz.bdd i hi) (hsS i hi) ((hL i hi).abs_y_le T.hD T.hEd T.hE)
      ((hL i hi).abs_sigma_le T.hD T.hEd T.hE)
  · have hi1 : i + 1 ≤ m := hi
    have hl := hL i hi.le
    have hl' := hL (i + 1) hi1
    have hgg : ∀ j, |T.g j (z i) - T.g j (z (i + 1))| ≤ Lg * δ := fun j =>
      hLg j _ _ _ (hz.bdd i hi.le) (hz.bdd _ hi1) (hz.step i hi)
    obtain ⟨h1, h2, h3⟩ := hΛ _ _ _ _ _ _ _ _ (Lg * δ) (by positivity) hl hl'
      (fun j => hG j _ (hz.bdd i hi.le)) (fun j => hG j _ (hz.bdd _ hi1)) (hν i hi.le) hgg
    have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
    have key : ∀ a : ℝ, ρ ^ 2 * a ≤ Λ * (Lg * δ) → a ≤ τ := fun a ha =>
      le_of_mul_le_mul_left ((ha.trans (by rw [← mul_assoc]; exact hδ1))) hρ2
    have hQ := hLQ (z i) (z (i + 1)) _ _ _ _ _ _ τ (hz.bdd i hi.le) (hz.bdd _ hi1)
      (hsS i hi.le) (hsS _ hi1) (hl.abs_y_le T.hD T.hEd T.hE) (hl'.abs_y_le T.hD T.hEd T.hE)
      (hl.abs_sigma_le T.hD T.hEd T.hE) (hl'.abs_sigma_le T.hD T.hEd T.hE)
      ((hz.step i hi).mono (by linarith)) (key _ h1) (fun j => key _ (h2 j))
      (fun j => key _ (h3 j))
    exact hQ.mono hτε
  · exact (T.lift_mem _ _ _ _ (hz.mem i hi) (hL i hi).pos (hL i hi).scale
      ((hL i hi).sum_eq_one T.hD T.hEd)).2

end OffStep

end BezoutCounterexample.Constructive
