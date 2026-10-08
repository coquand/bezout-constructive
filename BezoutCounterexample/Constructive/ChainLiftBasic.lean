import Mathlib
import BezoutCounterexample.Constructive.Attr
import BezoutCounterexample.Constructive.NuBound
import BezoutCounterexample.Constructive.Moebius

/-!
# Chain lifting: basic notions (`~/COLL/bezout-positive.tex`, §2)

Real points are tuples `w : Fin N → ℝ`; distances are coordinatewise (`Close δ w w'`), bounded
sets are boxes (`Bdd C w`). A closed chain of length `m` is a sequence `z : ℕ → Fin N → ℝ` with
`z m = z 0` and steps `Close δ (z i) (z (i+1))` for `i < m`. A lift of a chain comes with an
index map `ι` that is monotone with steps `0` or `1`, `ι 0 = 0`, `ι m' = m`
(`IsReindex`).

Constructive reals: besides `cotrans` (from `NuBound`), two trusted primitives with valid
statements, used instead of division and `Real.sqrt` (whose Mathlib definitions are total and
classical): positive reals have positive inverses and positive `n`-th roots.
-/

namespace BezoutCounterexample.Constructive

/-- **Positive reals are invertible** (trusted primitive). -/
@[cprim]
theorem exists_inv_pos {x : ℝ} (hx : 0 < x) : ∃ y, 0 < y ∧ x * y = 1 :=
  ⟨x⁻¹, inv_pos.2 hx, mul_inv_cancel₀ hx.ne'⟩

/-- **Positive reals have positive roots** (trusted primitive: intermediate value theorem for
the strictly increasing `y ↦ yⁿ`, with an explicit modulus). -/
@[cprim]
theorem exists_root_pos {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ∃ y, 0 < y ∧ y ^ n = x :=
  ⟨x ^ (1 / (n : ℝ)), Real.rpow_pos_of_pos hx _, by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    field_simp
    simp⟩

/-- `e < 2e` for `e > 0`, without `linarith` (which would prove a strict goal by contradiction). -/
theorem lt_two_mul' {e : ℝ} (he : 0 < e) : e < 2 * e := by
  rw [two_mul]; exact lt_add_of_pos_right e he

/-- `X < Y` from `2X ≤ Y` and `Y > 0`, constructively. -/
theorem lt_of_two_mul_le {X Y : ℝ} (h : 2 * X ≤ Y) (hY : 0 < Y) : X < Y :=
  lt_of_mul_lt_mul_left (lt_of_le_of_lt h (lt_two_mul' hY)) zero_le_two

/-- `A δ ≤ B` for some `δ > 0`. -/
theorem exists_pos_mul_le {B : ℝ} (hB : 0 < B) (A : ℝ) : ∃ δ, 0 < δ ∧ A * δ ≤ B := by
  have hA : 0 < |A| + 1 := by positivity
  obtain ⟨t, ht, htA⟩ := exists_inv_pos hA
  refine ⟨B * t, mul_pos hB ht, ?_⟩
  have h1 : A ≤ |A| + 1 := (le_abs_self A).trans (le_add_of_nonneg_right zero_le_one)
  calc A * (B * t) ≤ (|A| + 1) * (B * t) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = B * ((|A| + 1) * t) := by ring
    _ = B := by rw [htA, mul_one]

/-- `δ > 0` below finitely many positive bounds of the form `Aᵢ δ ≤ Bᵢ`, here two. -/
theorem exists_pos_mul_le₂ {B B' : ℝ} (hB : 0 < B) (hB' : 0 < B') (A A' : ℝ) :
    ∃ δ, 0 < δ ∧ A * δ ≤ B ∧ A' * δ ≤ B' := by
  obtain ⟨δ, hδ, h⟩ := exists_pos_mul_le (mul_pos hB hB') (|A| * B' + |A'| * B + B * B')
  refine ⟨δ, hδ, ?_, ?_⟩
  · -- `A δ B' ≤ B B'`
    have h1 : A * δ * B' ≤ B * B' := by
      have : A * δ * B' ≤ |A| * B' * δ := by
        have := mul_le_mul_of_nonneg_right (le_abs_self A) (mul_nonneg hδ.le hB'.le)
        nlinarith
      have h2 : |A| * B' * δ ≤ (|A| * B' + |A'| * B + B * B') * δ :=
        mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg A', abs_nonneg A]) hδ.le
      linarith
    exact le_of_mul_le_mul_right h1 hB'
  · have h1 : A' * δ * B ≤ B' * B := by
      have : A' * δ * B ≤ |A'| * B * δ := by
        have := mul_le_mul_of_nonneg_right (le_abs_self A') (mul_nonneg hδ.le hB.le)
        nlinarith
      have h2 : |A'| * B * δ ≤ (|A| * B' + |A'| * B + B * B') * δ :=
        mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg A', abs_nonneg A]) hδ.le
      linarith
    exact le_of_mul_le_mul_right h1 hB

/-- Finite choice along `0, …, m`. -/
theorem nat_choice {α : Type*} [Inhabited α] {P : ℕ → α → Prop} :
    ∀ m : ℕ, (∀ i ≤ m, ∃ x, P i x) → ∃ f : ℕ → α, ∀ i ≤ m, P i (f i) := by
  intro m
  induction m with
  | zero =>
    intro h
    obtain ⟨x, hx⟩ := h 0 le_rfl
    exact ⟨fun _ => x, fun i hi => by rw [Nat.le_zero.1 hi]; exact hx⟩
  | succ m ih =>
    intro h
    obtain ⟨f, hf⟩ := ih fun i hi => h i (Nat.le_succ_of_le hi)
    obtain ⟨x, hx⟩ := h (m + 1) le_rfl
    refine ⟨fun i => if i = m + 1 then x else f i, fun i hi => ?_⟩
    by_cases e : i = m + 1
    · simp only [e, ite_true]; exact hx
    · simp only [e, ite_false]; exact hf i (by omega)

/-- Finitely many constraints `Aᵢ r ≤ Bᵢ` (`Aᵢ ≥ 0`, `Bᵢ > 0`) have a common solution `r > 0`. -/
theorem exists_pos_mul_le_list :
    ∀ l : List (ℝ × ℝ), (∀ p ∈ l, 0 ≤ p.1 ∧ 0 < p.2) → ∃ r, 0 < r ∧ ∀ p ∈ l, p.1 * r ≤ p.2 := by
  intro l
  induction l with
  | nil => intro _; exact ⟨1, one_pos, fun p hp => absurd hp List.not_mem_nil⟩
  | cons a l ih =>
    intro h
    obtain ⟨r₀, hr₀, hl⟩ := ih fun p hp => h p (List.mem_cons_of_mem a hp)
    obtain ⟨r, hr, h1, h2⟩ := exists_pos_mul_le₂ (h a List.mem_cons_self).2 hr₀ a.1 1
    refine ⟨r, hr, fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h1
    · have hp0 := (h p (List.mem_cons_of_mem a hp)).1
      calc p.1 * r ≤ p.1 * r₀ := mul_le_mul_of_nonneg_left (by linarith) hp0
        _ ≤ p.2 := hl p hp

/-! ## Concatenating segments of equal length

A sequence made of `m` segments `σ i 0, …, σ i M` (with `σ i M = σ (i+1) 0`) is
`cat M σ j = σ (j / M) (j % M)`, of length `m M`, reindexed by `j ↦ j / M`. -/

section Cat
variable {X : Type*}

/-- Concatenation of segments of length `M`. -/
def cat (M : ℕ) (σ : ℕ → ℕ → X) (j : ℕ) : X := σ (j / M) (j % M)

lemma cat_mul_add {M : ℕ} (hM : 0 < M) (σ : ℕ → ℕ → X) (i t : ℕ) (ht : t < M) :
    cat M σ (i * M + t) = σ i t := by
  have h1 : (i * M + t) / M = i := by
    rw [add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt ht, zero_add]
  have h2 : (i * M + t) % M = t := by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  simp only [cat, h1, h2]

lemma cat_decomp {M : ℕ} (hM : 0 < M) (j : ℕ) : j = j / M * M + j % M ∧ j % M < M := by
  refine ⟨?_, Nat.mod_lt _ hM⟩
  have := Nat.div_add_mod j M
  rw [mul_comm] at this
  omega

lemma cat_step {M m : ℕ} (hM : 0 < M) (σ : ℕ → ℕ → X) (R : X → X → Prop)
    (hjoin : ∀ i < m, σ i M = σ (i + 1) 0)
    (hstep : ∀ i < m, ∀ t < M, R (σ i t) (σ i (t + 1))) :
    ∀ j < m * M, R (cat M σ j) (cat M σ (j + 1)) := by
  intro j hj
  obtain ⟨hdec, ht⟩ := cat_decomp hM j
  set i := j / M
  set t := j % M
  have hi : i < m := by
    by_contra h'
    have : m * M ≤ i * M := Nat.mul_le_mul_right _ (by omega)
    omega
  have e0 : cat M σ j = σ i t := by
    conv_lhs => rw [hdec]
    exact cat_mul_add hM σ i t ht
  rw [e0]
  rcases Nat.lt_or_ge (t + 1) M with h | h
  · have : cat M σ (j + 1) = σ i (t + 1) := by
      rw [show j + 1 = i * M + (t + 1) by omega]; exact cat_mul_add hM σ i _ h
    rw [this]; exact hstep i hi t ht
  · have htM : t + 1 = M := by omega
    have : cat M σ (j + 1) = σ (i + 1) 0 := by
      rw [show j + 1 = (i + 1) * M + 0 by rw [add_mul]; omega]
      exact cat_mul_add hM σ _ _ hM
    rw [this, ← hjoin i hi, ← htM]; exact hstep i hi t ht

lemma cat_prop {M m : ℕ} (hM : 0 < M) (σ : ℕ → ℕ → X) (P : ℕ → X → Prop)
    (h : ∀ i < m, ∀ t < M, P i (σ i t)) (hlast : P m (σ m 0)) :
    ∀ j ≤ m * M, P (j / M) (cat M σ j) := by
  intro j hj
  rcases Nat.lt_or_ge j (m * M) with hlt | hge
  · obtain ⟨hdec, ht⟩ := cat_decomp hM j
    have hi : j / M < m := (Nat.div_lt_iff_lt_mul hM).2 hlt
    have e0 : cat M σ j = σ (j / M) (j % M) := rfl
    rw [e0]; exact h _ hi _ ht
  · have hj' : j = m * M := le_antisymm hj hge
    subst hj'
    have e1 : m * M / M = m := Nat.mul_div_cancel _ hM
    have e2 : m * M % M = 0 := Nat.mul_mod_left _ _
    simp only [cat, e1, e2]; exact hlast

end Cat

/-! ## Boxes, closeness, chains -/

variable {N : ℕ}

/-- Coordinatewise closeness. -/
def Close (δ : ℝ) (w w' : Fin N → ℝ) : Prop := ∀ k, |w k - w' k| ≤ δ

/-- The box of radius `C`. -/
def Bdd (C : ℝ) (w : Fin N → ℝ) : Prop := ∀ k, |w k| ≤ C

lemma Close.symm {δ : ℝ} {w w' : Fin N → ℝ} (h : Close δ w w') : Close δ w' w :=
  fun k => by rw [abs_sub_comm]; exact h k

lemma Close.trans {δ δ' : ℝ} {w w' w'' : Fin N → ℝ} (h : Close δ w w') (h' : Close δ' w' w'') :
    Close (δ + δ') w w'' := fun k =>
  calc |w k - w'' k| = |(w k - w' k) + (w' k - w'' k)| := by ring_nf
    _ ≤ |w k - w' k| + |w' k - w'' k| := abs_add_le _ _
    _ ≤ δ + δ' := add_le_add (h k) (h' k)

lemma Close.mono {δ δ' : ℝ} {w w' : Fin N → ℝ} (h : Close δ w w') (hδ : δ ≤ δ') :
    Close δ' w w' := fun k => (h k).trans hδ

lemma close_refl {δ : ℝ} (hδ : 0 ≤ δ) (w : Fin N → ℝ) : Close δ w w := fun k => by simpa using hδ

lemma Bdd.mono {C C' : ℝ} {w : Fin N → ℝ} (h : Bdd C w) (hC : C ≤ C') : Bdd C' w :=
  fun k => (h k).trans hC

lemma Bdd.of_close {C δ : ℝ} {w w' : Fin N → ℝ} (h : Bdd C w) (h' : Close δ w' w) :
    Bdd (C + δ) w' := fun k =>
  calc |w' k| = |(w' k - w k) + w k| := by ring_nf
    _ ≤ |w' k - w k| + |w k| := abs_add_le _ _
    _ ≤ δ + C := add_le_add (h' k) (h k)
    _ = C + δ := add_comm _ _

/-- Lipschitz on the box of radius `C`, with constant `L`. -/
def LipB (C L : ℝ) {α : Type*} (f : (Fin N → ℝ) → α) (dist : α → α → ℝ → Prop) : Prop :=
  ∀ w w' δ, Bdd C w → Bdd C w' → Close δ w w' → dist (f w) (f w') (L * δ)

/-- Real-valued functions: `|f w - f w'| ≤ L δ`. -/
def LipR (C L : ℝ) (f : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ w w' δ, Bdd C w → Bdd C w' → Close δ w w' → |f w - f w'| ≤ L * δ

/-- Closed chains: `z m = z 0`, all points satisfy `P` and lie in the box `C`, and consecutive
points are `δ`-close. -/
structure IsChain (P : (Fin N → ℝ) → Prop) (C δ : ℝ) (m : ℕ) (z : ℕ → Fin N → ℝ) : Prop where
  closed : z m = z 0
  mem : ∀ i ≤ m, P (z i)
  bdd : ∀ i ≤ m, Bdd C (z i)
  step : ∀ i < m, Close δ (z i) (z (i + 1))

/-- Index maps of lifts: start at `0`, end at `m`, steps `0` or `1`. -/
structure IsReindex (m m' : ℕ) (ι : ℕ → ℕ) : Prop where
  zero : ι 0 = 0
  last : ι m' = m
  step : ∀ j < m', ι (j + 1) = ι j ∨ ι (j + 1) = ι j + 1

lemma IsReindex.le {m m' : ℕ} {ι : ℕ → ℕ} (h : IsReindex m m' ι) : ∀ j ≤ m', ι j ≤ m := by
  -- `ι` is monotone, so `ι j ≤ ι m' = m`
  have hmono : ∀ j k, j + k ≤ m' → ι j ≤ ι (j + k) := by
    intro j k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      rcases h.step (j + k) (by omega) with h2 | h2
      · rw [show j + (k + 1) = j + k + 1 by ring, h2]; exact h1
      · rw [show j + (k + 1) = j + k + 1 by ring, h2]; omega
  intro j hj
  have := hmono j (m' - j) (by omega)
  rw [show j + (m' - j) = m' by omega, h.last] at this
  exact this

lemma IsReindex.id (m : ℕ) : IsReindex m m id :=
  ⟨rfl, rfl, fun _ _ => Or.inr rfl⟩

/-- Composition of index maps. -/
lemma IsReindex.comp {m m' m'' : ℕ} {ι ι' : ℕ → ℕ} (h : IsReindex m m' ι)
    (h' : IsReindex m' m'' ι') : IsReindex m m'' (ι ∘ ι') := by
  refine ⟨by simp [h'.zero, h.zero], by simp [h'.last, h.last], fun j hj => ?_⟩
  have hle := h'.le j (by omega)
  rcases h'.step j hj with e | e
  · left; simp [e]
  · simp only [Function.comp, e]
    by_cases hlt : ι' j < m'
    · exact h.step _ hlt
    · exfalso
      have := h'.le (j + 1) (by omega)
      omega

lemma isReindex_div {M : ℕ} (hM : 0 < M) (m : ℕ) : IsReindex m (m * M) (· / M) := by
  refine ⟨Nat.zero_div _, Nat.mul_div_cancel _ hM, fun j _ => ?_⟩
  obtain ⟨hdec, ht⟩ := cat_decomp hM j
  rcases Nat.lt_or_ge (j % M + 1) M with h | h
  · left
    show (j + 1) / M = j / M
    rw [show j + 1 = j / M * M + (j % M + 1) by omega, add_comm, Nat.add_mul_div_right _ _ hM,
      Nat.div_eq_of_lt h, zero_add]
  · right
    show (j + 1) / M = j / M + 1
    rw [show j + 1 = (j / M + 1) * M by rw [add_mul]; omega, Nat.mul_div_cancel _ hM]


end BezoutCounterexample.Constructive
