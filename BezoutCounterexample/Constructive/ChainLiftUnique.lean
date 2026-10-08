import Mathlib
import BezoutCounterexample.Constructive.Attr

/-!
# Unique choice (Task A)

The decisions available in the construction are Prop-valued (`zeroTest : a = 0 ∨ a ≠ 0`,
`mem_dec`, …), and Lean cannot eliminate a Prop `Or` into data. Data is therefore extracted only
from `∃!` statements, by **unique choice**: valid in Bishop's constructive mathematics, in CZF and
in every topos (the description axiom; Troelstra–van Dalen, Ch. 1). It is the one trusted
primitive here; its Lean proof is `Classical.choose`.

* `uniqueChoice`: `(∃! x, P x) → {x // P x}`.
* `decOfOr`: a Prop decision `p ∨ ¬p` as `Decidable p` (unique choice on `Bool`).
* `orDec`: decisions are closed under `∨`.
-/

namespace BezoutCounterexample.Constructive

/-- **Unique choice** (trusted primitive: constructively valid, classical Lean proof). -/
@[cprim]
noncomputable def uniqueChoice {α : Sort*} {P : α → Prop} (h : ∃! x, P x) : {x // P x} :=
  Classical.indefiniteDescription P h.exists

/-- A decided proposition, as `Decidable`, by unique choice of its truth value. -/
noncomputable def decOfOr {p : Prop} (h : p ∨ ¬p) : Decidable p :=
  let b := uniqueChoice (P := fun b : Bool => (b = true ↔ p)) (by
    rcases h with hp | hnp
    · exact ⟨true, by simp [hp], fun b hb => by cases b <;> simp_all⟩
    · exact ⟨false, by simp [hnp], fun b hb => by cases b <;> simp_all⟩)
  if hb : b.1 = true then isTrue (b.2.1 hb)
  else isFalse fun hp => hb (b.2.2 hp)

/-- Decisions are closed under disjunction. -/
theorem orDec {p q : Prop} (hp : p ∨ ¬p) (hq : q ∨ ¬q) : (p ∨ q) ∨ ¬(p ∨ q) := by
  rcases hp with hp | hp
  · exact Or.inl (Or.inl hp)
  · rcases hq with hq | hq
    · exact Or.inl (Or.inr hq)
    · exact Or.inr fun h => h.elim hp hq

end BezoutCounterexample.Constructive
