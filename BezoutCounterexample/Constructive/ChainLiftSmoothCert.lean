import Mathlib
import BezoutCounterexample.Constructive.ChainLiftSquare
import BezoutCounterexample.Constructive.ChainLiftOffPres
import BezoutCounterexample.Constructive.Presented

/-!
# Smoothness certificates (Task B: replaces `Algebra.smoothLocus`)

A presentation `B = ℚ[Y₁…Y_{m+n}]/(G)` (`G` integer polynomials) is **certified smooth of
dimension `n`** when finitely many square pieces (`SquarePiece`: `m` relations of `(G)` and `n`
coordinates with unit Jacobian on `D(h)`, and `(G) = (F_eq)` on `D(h)`) cover `B`:
`C ≡ Σ_k u_k h_k` modulo `(G)` with `C` a positive integer. This is the Jacobian criterion in
certificate form (Lombardi–Quitté, Ch. VI; Stacks 00TA): no primes, every condition is an ideal
membership. The dimension is the parameter `n`, the same on every piece.

* `SmoothCert m n G`: the certificate.
* `SmoothCert.QB G`: the presented `ℚ`-algebra `ℚ[Y]/(G)`; `SmoothCert.hasPres`.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

/-- **A smoothness certificate of dimension `n`** for `ℚ[Y_{m+n}]/(G)`: square pieces covering
the presented ring, with a positive integer constant. -/
structure SmoothCert (m n : ℕ) (G : List (MvPolynomial (Fin (m + n)) ℤ)) where
  K : ℕ
  P : Fin K → SquarePiece m n G
  C : ℕ
  hC : 0 < C
  u : Fin K → MvPolynomial (Fin (m + n)) ℤ
  cover : (C : MvPolynomial (Fin (m + n)) ℤ) - ∑ k, u k * (P k).h ∈ lspan G

namespace SmoothCert

variable {m n : ℕ}

/-- The presented `ℚ`-algebra `ℚ[Y_{m+n}]/(G)`. -/
abbrev QB (G : List (MvPolynomial (Fin (m + n)) ℤ)) : Type :=
  MvPolynomial (Fin (m + n)) ℚ ⧸ lspan (G.map toQZ)

/-- The presented ring is explicitly presented. -/
theorem hasPres (G : List (MvPolynomial (Fin (m + n)) ℤ)) : HasPres (QB G) :=
  ⟨m + n, G.map toQZ, ⟨RingEquiv.refl _⟩⟩

end SmoothCert

end BezoutCounterexample.Constructive
