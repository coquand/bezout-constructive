import BezoutCounterexample.Principalization.MaxInvPos
import BezoutCounterexample.Rees

/-!
# The maximal invariant as a relation: the facts used at the top level (D3.5, leaf)

The top level (`ReesData`, `Divisorial`, `Torsor`, `PrincipalizationStar`) reads its facts about
`e = maxinv I` off `maxinv_spec` (`sSup`/`Classical.choose`) and counts the nonzero entries with
`numNonzero` (`Set.ncard`). Here the same facts come from the relation `IsMaxInv I e` (MaxInvPos)
and from the invariants `InvAt` at the witnessing point (`docs/d3-design.md` §5, D3.5):

* `InvAt.mem_Γ`, `InvAt.exists_zero_eq`: an invariant lies in `Γ`; its first weight is `1/a`
  (replacing `inv_mem_Γ`, `exists_inv_zero_eq`, which go through `inv`);
* `IsMaxInv.mem_Γ`, `.exists_zero_eq`, `.zero_ne` (replacing `maxinv_mem_Γ`,
  `exists_maxinv_zero_eq`);
* `kOf e h := Nat.find h`, the number of nonzero entries of `e ∈ Γ` as the first zero
  (`ne_zero_iff_lt_kOf`, replacing `ne_zero_iff_lt_numNonzero`); `kOf_eq_numNonzero` (comparison);
* `weight_le_dec`: for boundedly supported vectors, `v₁ ⪯ v` gives `v₁ ≺ v ∨ v₁ = v` by a finite
  search (`eq_or_ne_bounded`, MaxLocusPtCore; replacing `by_cases heq : maxinv I₁ = maxinv I`).

Leaf module; no `classical`, no `by_contra`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-! ### Invariants at a point -/

/-- **An invariant lies in `Γ`** (the `InvAt` form of `inv_mem_Γ`). -/
theorem InvAt.mem_Γ {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪)
    {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) : v ∈ Γ := by
  refine ⟨InvAt.goodV hI hI𝔪 hv, fun i hi => ?_⟩
  obtain ⟨n, e, he, hev⟩ := hv
  rw [← hev] at hi ⊢
  simp only [ext0] at hi ⊢
  rcases Nat.lt_or_ge (i + 1) n with h1 | h1
  · rw [dite_eq_left h1]
    rw [dite_eq_left (show i < n by omega)] at hi
    have h2 : e ⟨i + 1, h1⟩ ≤ e ⟨i, by omega⟩ := he.anti (Fin.le_def.2 (Nat.le_succ i))
    exact le_antisymm (h2.trans hi.le) (he.nonneg _)
  · rw [dite_eq_right (by omega)]

/-- **The first weight of an invariant is `1/a`** (the `InvAt` form of `exists_inv_zero_eq`). -/
theorem InvAt.exists_zero_eq {I : Ideal A} (hI : I ≠ ⊥) {𝔪 : Ideal A} [𝔪.IsMaximal]
    (hI𝔪 : I ≤ 𝔪) {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) : ∃ a : ℕ, 0 < a ∧ v 0 = 1 / a := by
  rcases InvAt.goodV hI hI𝔪 hv 0 with h0 | ⟨a, ha, h⟩
  · exact absurd h0 (InvAt.zero_ne hI hv)
  · refine ⟨a, ha, ?_⟩
    rw [h]
    simp [denPN]

/-! ### The maximal invariant -/

namespace IsMaxInv

variable {I : Ideal A} {e : ℕ → ℚ}

theorem mem_Γ (hI : I ≠ ⊥) (he : IsMaxInv I e) : e ∈ Γ := by
  obtain ⟨⟨𝔪, _, hI𝔪, hv⟩, -⟩ := he
  exact hv.mem_Γ hI hI𝔪

/-- The first weight of the maximal invariant is `1/a` (replacing `exists_maxinv_zero_eq`). -/
theorem exists_zero_eq (hI : I ≠ ⊥) (he : IsMaxInv I e) : ∃ a : ℕ, 0 < a ∧ e 0 = 1 / a := by
  obtain ⟨⟨𝔪, _, hI𝔪, hv⟩, -⟩ := he
  exact hv.exists_zero_eq hI hI𝔪

omit [Algebra.Smooth ℚ A] in
theorem zero_ne (hI : I ≠ ⊥) (he : IsMaxInv I e) : e 0 ≠ 0 := by
  obtain ⟨⟨𝔪, _, -, hv⟩, -⟩ := he
  exact InvAt.zero_ne hI hv

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- The engine form of maximality (`ReesData.hmax`). -/
theorem hmax (he : IsMaxInv I e) :
    ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex e ≤ toLex v :=
  he.2

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- The support bound of the maximal invariant, from any support bound of the invariants. -/
theorem bound {N : ℕ}
    (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (he : IsMaxInv I e) : ∀ i, N ≤ i → e i = 0 := by
  obtain ⟨⟨𝔪, _, -, hv⟩, -⟩ := he
  exact hbd 𝔪 e hv

end IsMaxInv

/-! ### The number of nonzero entries, as the first zero -/

omit [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
/-- In `Γ`, a zero entry is followed by zeros only. -/
theorem Γ.eq_zero_of_le {e : ℕ → ℚ} (he : e ∈ Γ) {j l : ℕ} (hj : e j = 0) (hjl : j ≤ l) :
    e l = 0 := by
  induction l, hjl using Nat.le_induction with
  | base => exact hj
  | succ l _ ih => exact he.2 l ih

/-- The number of nonzero entries of `e ∈ Γ`: the index of the first zero entry. Decided on `ℚ`;
`h` is only a `Prop` (`Nat.find`). -/
def kOf (e : ℕ → ℚ) (h : ∃ i, e i = 0) : ℕ := Nat.find h

omit [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
/-- **`eᵢ ≠ 0` exactly for `i < k`** (replacing `ne_zero_iff_lt_numNonzero`). -/
theorem ne_zero_iff_lt_kOf {e : ℕ → ℚ} (he : e ∈ Γ) (h : ∃ i, e i = 0) (i : ℕ) :
    e i ≠ 0 ↔ i < kOf e h := by
  constructor
  · intro hi
    rcases Nat.lt_or_ge i (kOf e h) with hlt | hge
    · exact hlt
    · exact absurd (Γ.eq_zero_of_le he (Nat.find_spec h) hge) hi
  · intro hi
    exact Nat.find_min h hi

omit [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
theorem kOf_le {e : ℕ → ℚ} {N : ℕ} (hN : ∀ i, N ≤ i → e i = 0) (h : ∃ i, e i = 0) :
    kOf e h ≤ N :=
  Nat.find_min' h (hN N le_rfl)

omit [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
theorem one_le_kOf {e : ℕ → ℚ} (he : e ∈ Γ) (h : ∃ i, e i = 0) (h0 : e 0 ≠ 0) :
    1 ≤ kOf e h :=
  (ne_zero_iff_lt_kOf he h 0).1 h0

omit [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
/-- **Comparison** (off the constructive path): `kOf` is `numNonzero`. -/
theorem kOf_eq_numNonzero {e : ℕ → ℚ} (he : e ∈ Γ) (h : ∃ i, e i = 0) :
    kOf e h = numNonzero e := by
  have hset : {i | e i ≠ 0} = ↑(Finset.range (kOf e h)) := by
    ext i
    rw [Set.mem_ofPred_eq, Finset.coe_range, Set.mem_Iio]
    exact ne_zero_iff_lt_kOf he h i
  rw [numNonzero, hset, Set.ncard_coe_finset, Finset.card_range]

/-! ### Comparing weight vectors with bounded support -/

omit [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
/-- **`v₁ ⪯ v` splits into `v₁ ≺ v` or `v₁ = v`**, for boundedly supported vectors (replacing
`by_cases heq : maxinv I₁ = maxinv I`). -/
theorem weight_le_dec {N : ℕ} {v₁ v : ℕ → ℚ} (hv₁ : ∀ i, N ≤ i → v₁ i = 0)
    (hv : ∀ i, N ≤ i → v i = 0) (hle : v₁ ⪯ v) : v₁ ≺ v ∨ v₁ = v := by
  rcases eq_or_ne_bounded hv₁ hv with h | h
  · exact Or.inr h
  · exact Or.inl ⟨hle, h⟩

end BezoutCounterexample.Principalization
