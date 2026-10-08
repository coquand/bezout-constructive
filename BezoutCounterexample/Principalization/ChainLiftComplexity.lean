import Mathlib
import BezoutCounterexample.PrincipalizationStar
import BezoutCounterexample.Principalization.MaxInvPos

/-!
# The complexity order with finite supports (Task A, C8)

`ΓN N` (PrincipalizationStar) bounds the support by `Set.encard`, and `eq_zero_of_mem_ΓN` argues by
contradiction. For the data-level recursion of `towerResult` (C2) the support bound is a `Finset`:

* `ΓN' N`: the weight vectors in `Γ` vanishing outside a `Finset` of size `≤ N`;
  `eq_zero_of_mem_ΓN'` (decided on `ℚ`, `ℕ`; no `by_contra`); `ΓN'_subset` (comparison, encard);
* `ComplexityLT' N` on `ΓN'`, well-founded by restriction of `complexityLT_wf`;
* `isMaxInv_mem_ΓN'`: a maximal invariant (`IsMaxInv`, MaxInvPos) vanishing from index `N` on lies in
  `ΓN' N` (the bound comes from the `ChartDim` form of `(⋆_N)`, D3.5);
* `commonDen v N := ∏_{i<N} den (v i)`: the common denominator as a function of `v` (no search).
-/

noncomputable section

namespace BezoutCounterexample

open Principalization

/-- The weight vectors in `Γ` vanishing outside a finite set of at most `N` indices. -/
def ΓN' (N : ℕ) : Set (ℕ → ℚ) := {e ∈ Γ | ∃ s : Finset ℕ, s.card ≤ N ∧ ∀ i ∉ s, e i = 0}

/-- A vector of `Γ` vanishing from index `N` on is in `ΓN' N`. -/
theorem mem_ΓN'_of_bound {N : ℕ} {e : ℕ → ℚ} (he : e ∈ Γ) (hb : ∀ i, N ≤ i → e i = 0) :
    e ∈ ΓN' N :=
  ⟨he, Finset.range N, (Finset.card_range N).le, fun i hi => hb i (by
    rw [Finset.mem_range] at hi; omega)⟩

/-- An element of `ΓN' N` vanishes from index `N` on. -/
theorem eq_zero_of_mem_ΓN' {N : ℕ} {e : ℕ → ℚ} (he : e ∈ ΓN' N) {i : ℕ} (hi : N ≤ i) :
    e i = 0 := by
  obtain ⟨hΓ, s, hs, hsupp⟩ := he
  rcases Decidable.em (e i = 0) with h | h
  · exact h
  · -- every index `j ≤ i` is in the support, so `i + 1 ≤ card s ≤ N ≤ i`
    have hprop : ∀ j, e j = 0 → ∀ l, j ≤ l → e l = 0 := by
      intro j hj l hl
      induction l, hl using Nat.le_induction with
      | base => exact hj
      | succ l _ ih => exact hΓ.2 l ih
    have hsub : Finset.range (i + 1) ⊆ s := by
      intro j hj
      rcases Decidable.em (j ∈ s) with hjs | hjs
      · exact hjs
      · exact absurd (hprop j (hsupp j hjs) i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) h
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega

/-- Comparison: `ΓN' N ⊆ ΓN N`. -/
theorem ΓN'_subset (N : ℕ) : ΓN' N ⊆ ΓN N := by
  rintro e ⟨hΓ, s, hs, hsupp⟩
  refine ⟨hΓ, ?_⟩
  have hsub : {i | e i ≠ 0} ⊆ (s : Set ℕ) := fun i hi => by
    rcases Decidable.em (i ∈ s) with h | h
    · exact h
    · exact absurd (hsupp i h) hi
  calc {i | e i ≠ 0}.encard ≤ (s : Set ℕ).encard := Set.encard_le_encard hsub
    _ = s.card := Set.encard_coe_eq_coe_finsetCard s
    _ ≤ N := by exact_mod_cast hs

/-- The complexity order on `ΓN' N × ℕ`. -/
def ComplexityLT' (N : ℕ) (p q : (ℕ → ℚ) × ℕ) : Prop :=
  p.1 ∈ ΓN' N ∧ q.1 ∈ ΓN' N ∧ (p.1 ≺ q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2))

/-- `ComplexityLT'` is well-founded (a subrelation of `ComplexityLT`). -/
theorem complexityLT'_wf (N : ℕ) : WellFounded (ComplexityLT' N) :=
  Subrelation.wf (fun h => ⟨ΓN'_subset N h.1, ΓN'_subset N h.2.1, h.2.2⟩) (complexityLT_wf N)

/-- **A maximal invariant vanishing from index `N` on lies in `ΓN' N`.** -/
theorem isMaxInv_mem_ΓN' {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
    {I : Ideal A} (hI : I ≠ ⊥) {v : ℕ → ℚ} (h : IsMaxInv I v) {N : ℕ}
    (hb : ∀ i, N ≤ i → v i = 0) : v ∈ ΓN' N := by
  obtain ⟨⟨𝔪, h𝔪, hI𝔪, hv⟩, -⟩ := h
  have hΓ := inv_mem_Γ hI hI𝔪
  rw [InvAt.unique (invAt_inv hI hI𝔪) hv] at hΓ
  exact mem_ΓN'_of_bound hΓ hb

/-- **The common denominator** of a weight vector supported below `N`, as a function. -/
def commonDen (v : ℕ → ℚ) (N : ℕ) : ℕ := ∏ i ∈ Finset.range N, (v i).den

theorem one_le_commonDen (v : ℕ → ℚ) (N : ℕ) : 1 ≤ commonDen v N :=
  Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => (v i).den_ne_zero)

theorem commonDen_spec {v : ℕ → ℚ} {N : ℕ} (hv : ∀ i, N ≤ i → v i = 0) (i : ℕ) :
    ∃ w : ℤ, (commonDen v N : ℚ) * v i = w := by
  rcases Nat.lt_or_ge i N with hi | hi
  · exact dvd_den_mul_int (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi))
  · exact ⟨0, by rw [hv i hi, mul_zero, Int.cast_zero]⟩

end BezoutCounterexample
