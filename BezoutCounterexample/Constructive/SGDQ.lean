import BezoutCounterexample.Constructive.DynNagata
import BezoutCounterexample.Constructive.Presented
import Mathlib.RingTheory.Smooth.Basic

/-!
# Smooth GCD domains up to an escape (D5; `docs/d5-plan.md`, step 4)

`SmoothGCDDomainQ`: the D5 form of `SmoothGCDDomain`. The tower stays classical; each stage's
decisions are constructive **up to an escape** `esc` collecting the splits met so far.

Only gcds need the escape: zero test and decidable divisibility follow from the presentation
(`SmoothGCDDomainQ.zeroTest`, `.dvdDec`).

* `IsGcdQ.mono`, `IsGcdQ.or_left`: escapes only grow.
* `SmoothGCDDomainQ.weaken`: the same ring with a larger escape.
* `SmoothGCDDomainQ.hasGcd_of_not`: with the escape refuted, ordinary gcds.
-/

namespace BezoutCounterexample.Constructive

section Gcd

variable {A : Type*} [CommRing A]

lemma IsGcdQ.mono {Q Q' : Prop} (hQ : Q → Q') {g a b : A} (h : IsGcdQ Q g a b) :
    IsGcdQ Q' g a b :=
  ⟨h.1.imp_right hQ, h.2.1.imp_right hQ, fun c ha hb => (h.2.2 c ha hb).imp_right hQ⟩

lemma IsGcdQ.isGcd {Q : Prop} (hQ : ¬ Q) {g a b : A} (h : IsGcdQ Q g a b) : IsGcd g a b :=
  ⟨h.1.resolve_right hQ, h.2.1.resolve_right hQ, fun c ha hb => (h.2.2 c ha hb).resolve_right hQ⟩

end Gcd

/-- A smooth finitely presented `ℚ`-domain whose gcds are computed up to the escape `esc`. -/
structure SmoothGCDDomainQ where
  /-- The underlying ring. -/
  carrier : Type
  [commRing : CommRing carrier]
  [isDomain : IsDomain carrier]
  [algebra : Algebra ℚ carrier]
  [smooth : Algebra.Smooth ℚ carrier]
  /-- An explicit presentation (zero test, divisibility, ideal membership). -/
  pres : HasPres carrier
  /-- The escape: a disjunction of the splits met so far. -/
  esc : Prop
  /-- Gcds, up to the escape. -/
  hasGcdQ : ∀ a b : carrier, ∃ g, IsGcdQ esc g a b

namespace SmoothGCDDomainQ

instance : CoeSort SmoothGCDDomainQ Type := ⟨SmoothGCDDomainQ.carrier⟩

attribute [instance] commRing isDomain algebra smooth

variable (B : SmoothGCDDomainQ)

theorem zeroTest (a : B) : a = 0 ∨ a ≠ 0 := B.pres.zeroTest a

theorem dvdDec : DvdDec B := B.pres.dvdDec

/-- The same ring with a larger escape. -/
def weaken (Q : Prop) (hQ : B.esc → Q) : SmoothGCDDomainQ where
  carrier := B
  pres := B.pres
  esc := Q
  hasGcdQ a b := let ⟨g, hg⟩ := B.hasGcdQ a b; ⟨g, hg.mono hQ⟩

/-- With the escape refuted, ordinary gcds. -/
theorem hasGcd_of_not (h : ¬ B.esc) : HasGcd B := fun a b =>
  let ⟨g, hg⟩ := B.hasGcdQ a b; ⟨g, hg.isGcd h⟩

end SmoothGCDDomainQ

end BezoutCounterexample.Constructive
