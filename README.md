# A constructive proof that a Bézout domain need not be an elementary divisor domain

This repository contains a *constructive* version, produced by **Claude (Anthropic)**, of the proof in

> C. Hägg and A. Mörtberg, *A Bézout domain that is not an elementary divisor domain*,
> [arXiv:2609.35229](https://arxiv.org/abs/2609.35229).

It is **not** the work of Hägg and Mörtberg, and they have not reviewed it. The Lean code is a fork
of their formalization [Zelaron/bezout-counterexample-lean](https://github.com/Zelaron/bezout-counterexample-lean)
(MIT licence, copyright Hägg and Mörtberg; see [`LICENSE`](LICENSE)). Claude extended it so that the
construction no longer uses classical reasoning in the project's own code.

The theorem: there is a Bézout domain R ⊃ ℚ[x, y] over which the matrix

```text
    [ 1 + x    y   ]
M = [   y    1 - x ]
```

has no Smith normal form.

## Documents

- [`bezout-constructive-proof.pdf`](bezout-constructive-proof.pdf) (LaTeX source alongside): a
  constructive proof in the style of Lombardi–Quitté, written by Claude. The only principles used
  beyond intuitionistic logic are unique choice and Noetherianity in the inductive
  (Richman–Seidenberg / Coquand–Persson) sense. Maximal ideals, Krull dimension and compactness are
  not used.
- [`constructive/lean-formalisation.pdf`](constructive/lean-formalisation.pdf) (LaTeX source
  alongside): a short note by Claude that documents the Lean proof. It covers the constructive
  ingredients (chain lifting, smoothness certificates, points, unique choice) and the status of the
  formalisation.

## The Lean development

The constructive form of the main theorem is `BezoutCounterexample.main_theorem_tower` in
[`Principalization/ChainLiftMain.lean`](BezoutCounterexample/Principalization/ChainLiftMain.lean):

```lean
theorem main_theorem_tower :
    ∃ (R : Type) (_ : CommRing R),
      IsDomain R ∧ IsBezout R ∧ ¬ IsElementaryDivisorDomain R
```

The topological argument (compact sets with monotone surjections) is replaced by chain lifting along
explicit polynomial charts, and the tower is defined by well-founded recursion and unique choice.
Hägg and Mörtberg's original classical proof, `BezoutCounterexample.main_theorem` in
[`MainTheorem.lean`](BezoutCounterexample/MainTheorem.lean), is still part of the build. The
correspondence between their paper and the Lean declarations is in
[`docs/STATEMENTS.md`](docs/STATEMENTS.md).

Claude's additions are mainly in `BezoutCounterexample/Constructive/` and in the
`Principalization/ChainLift*` and `*Pt*` files.

### Status (October 2026)

- The full build succeeds.
- [`scripts/ConstructiveAudit.lean`](scripts/ConstructiveAudit.lean) passes. The audited
  declarations use no classical constant except 8 explicitly marked `@[cprim]` primitives, which
  are constructively valid:
  - sign splitting and cotransitivity on ℝ;
  - inverses and roots of positive reals;
  - a Banach fixed point with rate ½;
  - polynomial gcd over a discrete field;
  - a primitive-element shift.
- No project declaration in the dependency cone of `main_theorem_tower` (about 4800
  declarations) directly uses `Classical.*`, excluded middle or a hidden choice wrapper
  (`Exists.choose`, `Finset.toList`, …). This was measured with
  [`docs/pending/cone-count.lean`](docs/pending/cone-count.lean).
- **Caveat:** `#print axioms main_theorem_tower` still reports
  `[propext, Classical.choice, Quot.sound]`.
  - These uses come from Mathlib lemmas (the Hilbert basis theorem, localisation, finite-set
    bookkeeping). The lemmas are known to be constructively valid, but Mathlib proves them
    classically.
  - Unique choice is used.
  - So the development is constructive *modulo Mathlib*; it is not a choice-free term.
  - Details: [`docs/remaining-classical.md`](docs/remaining-classical.md),
    [`docs/constructive-audit.md`](docs/constructive-audit.md).

### Building

Dependencies: Lean 4.34.1 (pinned in `lean-toolchain`) and Mathlib v4.34.1 (pinned in
`lake-manifest.json`). With [elan](https://github.com/leanprover/elan) installed:

```bash
lake exe cache get
lake build
lake env lean scripts/ConstructiveAudit.lean
```

Loading the full Mathlib import needs roughly 7 GiB of memory.

## Acknowledgments

The construction, the original proof and the Lean formalization this work builds on are due to
Christian Hägg and Anders Mörtberg, who used OpenAI's GPT-6 Astra (via Codex). The constructive
version and the documents in this repository were produced by Claude (Anthropic).

## License

[MIT](LICENSE). The original code is copyright Christian Hägg and Anders Mörtberg, 2026.
