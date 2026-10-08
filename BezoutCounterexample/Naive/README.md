# The naive Kronecker–Bézout ring is not an elementary divisor domain

Added on top of the Hägg–Mörtberg formalization (copied from
github.com/Zelaron/bezout-counterexample-lean, Lean 4.34.1 / Mathlib v4.34.1).

Main result: `BezoutCounterexample.naive_main_theorem` in `Main.lean`:

    IsDomain RN ∧ IsBezout RN ∧ ¬ IsElementaryDivisorDomain RN

where `RN` is the union of the Kronecker steps `A ↦ A[σ, τ, a/g, b/g]`, `g = aσ + bτ`,
starting from `ℚ[x, y]` (one pair per step, scheduled as in Construction 5.1).
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

* `Kronecker.lean`: the step, `(a, b)U = gU`, and the embedding lemma `exists_extension`
  (σ ↦ c r₀ + c' b', τ ↦ c s₀ − c' a', with c a unit and c, c' algebraically independent).
* `Tower.lean`: the ring `RN`, its Bézout property, and the generic SNF ⇒ five-element step.
* `Embed.lean`: `FreshTarget` (a Bézout domain with fresh units) and `RN → T`.
* `LaurentStep.lean`: `L(P) = P[X₀, X₁][1/(X₀X₁)]` is smooth, factorial, with a homeomorphic
  real lift; composition with a principalization step.
* `ConstructionL.lean`: Construction 5.1 with a Laurent step after each principalization step
  (a renamed copy of `Construction.lean`).
* `Main.lean`: Lemma 5.3 for this variant, the fresh-target structure, the main theorem.

Build: `lake build BezoutCounterexample.Naive.Main`.
