import Mathlib

/-!
# Method 1's minimiser as a bounded search (Task D, R6; roadmap §1.2, §1.6)

`Centre.exists_min_Xi` takes `Nat.find` over an arbitrary set `S` of multi-indices (under
`classical`). Here `S` is a decided predicate with a first candidate `β₀` (from (F2⁺)), and the
minimiser of `Ξ_j(β) = tail_j(β) / (1 − λ_e(β))` is found among finitely many `β`:

* `Ξ(β) ≤ Ξ(β₀)` and `λ(β) < 1` put `β` in an explicit box (`mem_box_of_Xi_le`): a head
  exponent (`i < j`, `eᵢ > 0`) satisfies `βᵢ eᵢ ≤ λ(β) < 1`, so `βᵢ < den eᵢ`; a tail exponent
  satisfies `βᵢ ≤ tail(β) = Ξ(β)(1 − λ(β)) ≤ Ξ(β₀)`.
* `exists_min_of_box`: the minimum of a rational function over a decided set, given a witness and
  a finite list containing every candidate at most as large as the witness. Only decided
  comparisons of rationals; no `Nat.find`, no Markov.
* `exists_min_Xi_dec`: the combination, over `β : Fin n → ℕ`.
-/

noncomputable section

namespace BezoutCounterexample.Constructive

/-- **Minimum over a decided set, bounded by a finite list.** -/
theorem exists_min_of_box {α : Type*} (f : α → ℚ) {S : α → Prop} (hS : ∀ a, S a ∨ ¬ S a)
    {a₀ : α} (h₀ : S a₀) (box : List α) (hbox : ∀ a, S a → f a ≤ f a₀ → a ∈ box) :
    ∃ a, S a ∧ ∀ b, S b → f a ≤ f b := by
  have key : ∀ L : List α, ∃ a, S a ∧ f a ≤ f a₀ ∧ ∀ b ∈ L, S b → f a ≤ f b := by
    intro L
    induction L with
    | nil => exact ⟨a₀, h₀, le_rfl, fun _ h => absurd h List.not_mem_nil⟩
    | cons b L ih =>
      obtain ⟨a, ha, ha₀, hmin⟩ := ih
      rcases hS b with hb | hb
      · by_cases hlt : f b < f a
        · refine ⟨b, hb, hlt.le.trans ha₀, fun c hc hSc => ?_⟩
          rcases List.mem_cons.1 hc with rfl | hc
          · exact le_rfl
          · exact hlt.le.trans (hmin c hc hSc)
        · refine ⟨a, ha, ha₀, fun c hc hSc => ?_⟩
          rcases List.mem_cons.1 hc with rfl | hc
          · exact le_of_not_gt hlt
          · exact hmin c hc hSc
      · refine ⟨a, ha, ha₀, fun c hc hSc => ?_⟩
        rcases List.mem_cons.1 hc with rfl | hc
        · exact absurd hSc hb
        · exact hmin c hc hSc
  obtain ⟨a, ha, ha₀, hmin⟩ := key box
  refine ⟨a, ha, fun b hb => ?_⟩
  by_cases hlt : f a₀ < f b
  · exact ha₀.trans hlt.le
  · exact hmin b (hbox b hb (le_of_not_gt hlt)) hb

variable {n : ℕ}

/-- `λ_e(β) = Σ βᵢ eᵢ`. -/
def lamF (e : Fin n → ℚ) (β : Fin n → ℕ) : ℚ := ∑ i, (β i : ℚ) * e i

/-- `tail_j(β) = Σ_{i ≥ j} βᵢ`. -/
def tailF (j : ℕ) (β : Fin n → ℕ) : ℕ := ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), β i

/-- `Ξ_j(β) = tail_j(β) / (1 − λ_e(β))`. -/
def XiF (e : Fin n → ℚ) (j : ℕ) (β : Fin n → ℕ) : ℚ := (tailF j β : ℚ) / (1 - lamF e β)

/-- The bound of the box. -/
def boxBound (e : Fin n → ℚ) (X : ℚ) : ℕ := (∑ i, (e i).den) + X.num.toNat

/-- The box `{β | βᵢ ≤ B}` as an explicit finite list. -/
def boxList (B : ℕ) : (m : ℕ) → List (Fin m → ℕ)
  | 0 => [Fin.elim0]
  | m + 1 => (List.range (B + 1)).flatMap fun a => (boxList B m).map (Fin.cons a)

lemma mem_boxList {B : ℕ} : ∀ {m : ℕ} {β : Fin m → ℕ}, (∀ i, β i ≤ B) → β ∈ boxList B m
  | 0, β, _ => by
    rw [boxList, List.mem_singleton]; funext i; exact i.elim0
  | m + 1, β, h => by
    rw [boxList, List.mem_flatMap]
    refine ⟨β 0, List.mem_range.2 (Nat.lt_succ_of_le (h 0)), List.mem_map.2
      ⟨Fin.tail β, mem_boxList fun i => h i.succ, Fin.cons_self_tail β⟩⟩

lemma lamF_nonneg {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) (β : Fin n → ℕ) : 0 ≤ lamF e β :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (he i)

lemma le_den_of_mul_lt_one {q : ℚ} (hq : 0 < q) {b : ℕ} (hb : (b : ℚ) * q < 1) : b ≤ q.den := by
  have hnum : (1 : ℚ) ≤ q.num := by exact_mod_cast Rat.num_pos.2 hq
  have hden : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hq' : q = q.num / q.den := (Rat.num_div_den q).symm
  have h1 : (b : ℚ) * q.num < q.den := by
    rw [hq', ← mul_div_assoc, div_lt_one hden] at hb; exact hb
  have : (b : ℚ) < q.den := by nlinarith
  exact_mod_cast this.le

lemma le_num_toNat {X : ℚ} (hX : 0 ≤ X) {b : ℕ} (hb : (b : ℚ) ≤ X) : b ≤ X.num.toNat := by
  have hden : (1 : ℚ) ≤ X.den := by exact_mod_cast X.den_pos
  have hnum : (0 : ℚ) ≤ X.num := by exact_mod_cast Rat.num_nonneg.2 hX
  have hX' : X ≤ X.num := by
    have h := Rat.mul_den_eq_num X
    nlinarith
  have h1 : (b : ℤ) ≤ X.num := by exact_mod_cast hb.trans hX'
  omega

/-- **The box**: a candidate at most as large as `X ≥ 0` has all exponents `≤ boxBound e X`. -/
lemma mem_box_of_Xi_le {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) {j : ℕ}
    (hpos : ∀ i : Fin n, (i : ℕ) < j → 0 < e i) {X : ℚ} (hX : 0 ≤ X) {β : Fin n → ℕ}
    (hlt : lamF e β < 1) (hXi : XiF e j β ≤ X) : ∀ i, β i ≤ boxBound e X := by
  intro i
  have hl0 := lamF_nonneg he β
  have hden : 0 < 1 - lamF e β := by linarith
  rcases Nat.lt_or_ge (i : ℕ) j with hij | hij
  · have hi : (β i : ℚ) * e i ≤ lamF e β :=
      Finset.single_le_sum (f := fun k => (β k : ℚ) * e k)
        (fun k _ => mul_nonneg (Nat.cast_nonneg _) (he k)) (Finset.mem_univ i)
    have h1 := le_den_of_mul_lt_one (hpos i hij) (hi.trans_lt hlt)
    have h2 : (e i).den ≤ ∑ k, (e k).den :=
      Finset.single_le_sum (f := fun k => (e k).den) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    rw [boxBound]; omega
  · have hti : β i ≤ tailF j β :=
      Finset.single_le_sum (f := fun k => β k) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, hij⟩)
    have htail : (tailF j β : ℚ) ≤ X := by
      have h1 : (tailF j β : ℚ) = XiF e j β * (1 - lamF e β) := by
        rw [XiF, div_mul_cancel₀ _ hden.ne']
      rw [h1]
      have hXi0 : 0 ≤ XiF e j β := div_nonneg (Nat.cast_nonneg _) hden.le
      nlinarith
    have h2 := le_num_toNat hX ((Nat.cast_le.2 hti).trans htail)
    rw [boxBound]; omega

/-- **Method 1's minimiser, by a bounded search** (replaces `Centre.exists_min_Xi`). -/
theorem exists_min_Xi_dec {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) {j : ℕ}
    (hpos : ∀ i : Fin n, (i : ℕ) < j → 0 < e i) {S : (Fin n → ℕ) → Prop}
    (hS : ∀ β, S β ∨ ¬ S β) {β₀ : Fin n → ℕ} (h₀ : S β₀) (hlt : ∀ β, S β → lamF e β < 1) :
    ∃ β, S β ∧ ∀ β', S β' → XiF e j β ≤ XiF e j β' := by
  have hX : 0 ≤ XiF e j β₀ :=
    div_nonneg (Nat.cast_nonneg _) (by linarith [hlt β₀ h₀])
  exact exists_min_of_box (XiF e j) hS h₀ (boxList (boxBound e (XiF e j β₀)) n)
    fun β hβ hle => mem_boxList (mem_box_of_Xi_le he hpos hX (hlt β hβ) hle)

end BezoutCounterexample.Constructive
