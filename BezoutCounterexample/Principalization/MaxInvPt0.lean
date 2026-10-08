import BezoutCounterexample.Principalization.MaxInvPt
import BezoutCounterexample.Principalization.MaxInvPtDef

/-!
# The maximal invariant at explicit points: `IsMaxInvPt` (leaf, for the top-chain switch)

The engine's `hmax` quantifies over all maximal ideals. Its point form bounds the invariant only
at explicit points (`Pt`), whose kernels are maximal (`Pt.ker_isMaximal`):

* `IsMaxInvPt I v₀`: `toLex v₀ ≤ toLex v` for every invariant `v` at an explicit point of `V(I)`;
* `IsMaxInv.toPt`: the classical relation gives the point form;
* `IsMaxInv.attained_pt`: it is attained at an explicit point (`IsMaxInv.exists_pt`).

The attained part is kept as a separate hypothesis `∃ q : Pt A, I ≤ q.ker ∧ InvAt I q.ker v₀`
(as in `exists_isMaxInv_pt`). Agreed with coll-7c (2026-10-06). Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- The classical relation gives the point form. -/
theorem IsMaxInv.toPt {I : Ideal A} {v₀ : ℕ → ℚ} (he : IsMaxInv I v₀) : IsMaxInvPt I v₀ :=
  fun q hIq v hv => he.2 q.ker hIq v hv

/-- **The maximal invariant is attained at an explicit point.** -/
theorem IsMaxInv.attained_pt (hp : HasPres A) {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤)
    {N : ℕ} (hN : ChartDim A N) (gens : List A) (hgens : I = lspan gens) {v₀ : ℕ → ℚ}
    (he : IsMaxInv I v₀) : ∃ q : Pt A, I ≤ q.ker ∧ InvAt I q.ker v₀ :=
  he.exists_pt hp hI hItop hN gens hgens

end BezoutCounterexample.Principalization
