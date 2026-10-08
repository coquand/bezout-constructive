import BezoutCounterexample.Principalization.PosWire
import BezoutCounterexample.Invariant

/-!
# The maximal invariant as a computed value (Task D, R6; roadmap §3.2)

`Invariant.maxinv` is `if h : ∃ v, … then h.choose else 0` (`Classical.propDecidable`,
`Classical.choose`), and `MaxLocus.exists_maxInv` chooses over the type of all maximal ideals and
uses Zorn. Here `maxinv(I)` is the `⪯`-**maximum** of the invariant (equivalently the
lexicographic minimum of the weight vectors) over the finite positive cover of `V(I)`
(`exists_maxInv_pos`).

* `IsMaxInv I v₀`: `v₀` is attained at a point of `V(I)` and lexicographically below every
  invariant there; `IsMaxInv.unique`.
* `exists_isMaxInv_of_hasPres`: from a presentation, generators of `I`, and the chart size
  `N` (`ChartDim A N`: R5, Task C). The `¬ (v < v₀)` of the positive cover becomes `v₀ ≤ v` by
  `lex_total_bounded` (supports below `N`), with no `¬¬` and no `le_total`.
* `existsUnique_isMaxInv`: the `∃!` interface for `towerResult` (unique choice; see
  `Constructive/CompList`).
* `maxinv_eq_of_isMaxInv` (comparison, off the constructive path): the classical `maxinv` is the
  computed value.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- `v₀` is the maximal invariant of `I`: attained on `V(I)`, and `v₀ ≤_lex v` for every
invariant `v` at a point of `V(I)` (i.e. `v ⪯ v₀`). -/
def IsMaxInv (I : Ideal A) (v₀ : ℕ → ℚ) : Prop :=
  (∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), I ≤ 𝔪 ∧ InvAt I 𝔪 v₀) ∧
    ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma IsMaxInv.unique {I : Ideal A} {v₀ v₁ : ℕ → ℚ} (h₀ : IsMaxInv I v₀) (h₁ : IsMaxInv I v₁) :
    v₀ = v₁ := by
  obtain ⟨⟨𝔪₀, h𝔪₀, hI₀, hv₀⟩, b₀⟩ := h₀
  obtain ⟨⟨𝔪₁, h𝔪₁, hI₁, hv₁⟩, b₁⟩ := h₁
  exact toLex.injective (le_antisymm (b₀ 𝔪₁ hI₁ v₁ hv₁) (b₁ 𝔪₀ hI₀ v₀ hv₀))

/-- **The maximal invariant, positively**, from a presentation. -/
theorem exists_isMaxInv_of_hasPres (hp : HasPres A) {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤)
    {N : ℕ} (hN : ChartDim A N) (gens : List A) (hgens : I = lspan gens) :
    ∃ v₀, IsMaxInv I v₀ := by
  have hdec : ∀ l : List A, (1 : A) ∈ I ⊔ lspan l ∨ (1 : A) ∉ I ⊔ lspan l := fun l => by
    rw [hgens, ← lspan_append_eq]; exact hp.mem_dec _ 1
  obtain ⟨v₀, ⟨𝔪₀, h𝔪₀, hI₀, hv₀⟩, bnd⟩ := exists_maxInv_pos hI hItop hN gens hgens
    (explicitNS_of_hasPres hp) hdec (indNoeth_quotient_of_hasPres hp I)
  refine ⟨v₀, ⟨𝔪₀, h𝔪₀, hI₀, hv₀⟩, fun 𝔪 _ hI𝔪 v hv => ?_⟩
  rcases lex_total_bounded (invAt_bounded hN hv₀) (invAt_bounded hN hv) with h | h
  · exact h
  · rcases h.lt_or_eq with hlt | heq
    · exact absurd hlt (bnd 𝔪 hI𝔪 v hv)
    · exact heq.ge

/-- The `∃!` interface. -/
theorem existsUnique_isMaxInv (hp : HasPres A) {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤)
    {N : ℕ} (hN : ChartDim A N) (gens : List A) (hgens : I = lspan gens) :
    ∃! v₀, IsMaxInv I v₀ := by
  obtain ⟨v₀, h₀⟩ := exists_isMaxInv_of_hasPres hp hI hItop hN gens hgens
  exact ⟨v₀, h₀, fun _ h₁ => h₁.unique h₀⟩

/-- **Comparison**: the classical `maxinv` is the computed maximal invariant. -/
theorem maxinv_eq_of_isMaxInv {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤) {v₀ : ℕ → ℚ}
    (h₀ : IsMaxInv I v₀) : maxinv I = v₀ := by
  refine IsMaxInv.unique ⟨?_, maxinv_le hI hItop⟩ h₀
  obtain ⟨𝔪, h𝔪, hI𝔪, heq⟩ := (maxinv_spec hI hItop).1
  exact ⟨𝔪, h𝔪, hI𝔪, heq ▸ invAt_inv hI hI𝔪⟩

end BezoutCounterexample.Principalization
