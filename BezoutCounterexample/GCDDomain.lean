import BezoutCounterexample.Basic
import BezoutCounterexample.Constructive.NagataGCD
import BezoutCounterexample.Constructive.GCDPoly
import BezoutCounterexample.Constructive.Groebner
import BezoutCounterexample.Constructive.Presented

/-!
# Smooth finitely generated GCD domains (`~/COLL/bezout-gcd.tex`)

The invariant of the tower in the GCD form of HM's construction: a smooth finitely generated
`ℚ`-domain with gcds, a zero test, decidable divisibility and an explicit presentation
(`SmoothGCDDomain`). It replaces
`SmoothFactorialDomain` (`Factoriality.lean`, kept as the classical fallback): factoriality is used
by HM only through gcd extraction, the generator of a divisorial component and Nagata's criterion,
all of which go through for GCD domains (`Principalization/GCDStep.lean`).

`A₀ = ℚ[x, y]` is a smooth GCD domain with all three fields proved constructively
(`hasGcd_A₀`, `zeroTest_A₀`, `dvdDec_A₀`, the last one by Gröbner bases).
-/

namespace BezoutCounterexample

open Constructive

/-- A smooth finitely generated `ℚ`-domain with gcds, a zero test and decidable divisibility. -/
structure SmoothGCDDomain where
  /-- The underlying ring. -/
  carrier : Type
  [commRing : CommRing carrier]
  [isDomain : IsDomain carrier]
  [algebra : Algebra ℚ carrier]
  [smooth : Algebra.Smooth ℚ carrier]
  /-- Every pair has a gcd. -/
  hasGcd : HasGcd carrier
  /-- Zero test. -/
  zeroTest : ∀ a : carrier, a = 0 ∨ a ≠ 0
  /-- Decidable divisibility. -/
  dvdDec : DvdDec carrier
  /-- An explicit presentation `ℚ[Y] ⧸ (G)`, which gives decidable membership in finitely
  generated ideals (Gröbner bases). -/
  pres : HasPres carrier

attribute [instance] SmoothGCDDomain.commRing SmoothGCDDomain.isDomain
  SmoothGCDDomain.algebra SmoothGCDDomain.smooth

instance : CoeSort SmoothGCDDomain Type := ⟨SmoothGCDDomain.carrier⟩

/-- Smooth finitely generated `ℚ`-algebras are Noetherian. -/
instance SmoothGCDDomain.isNoetherianRing (A : SmoothGCDDomain) :
    IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A

/-- The presentation of a smooth GCD domain, as an instance (D3: `[Fact (HasPres A)]` threading). -/
instance SmoothGCDDomain.factHasPres (A : SmoothGCDDomain) : Fact (Constructive.HasPres A) :=
  ⟨A.pres⟩

/-- Every finitely generated `ℚ`-algebra is countable. -/
instance SmoothGCDDomain.countable (A : SmoothGCDDomain) : Countable A := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType ℚ A)
  exact hf.countable

/-- Fields with a zero test have gcds. -/
theorem hasGcd_of_field (K : Type*) [Field K] (hz : ∀ a : K, a = 0 ∨ a ≠ 0) : HasGcd K := by
  intro a b
  rcases hz a with rfl | ha
  · exact ⟨b, isGcd_zero_left b⟩
  · exact ⟨1, one_dvd a, one_dvd b, fun c hc _ => by
      obtain ⟨e, he⟩ := hc
      exact ⟨e * a⁻¹, by rw [← mul_assoc, ← he, mul_inv_cancel₀ ha]⟩⟩

theorem zeroTest_rat : ∀ a : ℚ, a = 0 ∨ a ≠ 0 := fun a => deq a 0

theorem hasGcd_A₀ : HasGcd A₀ := (hasGcd_mvPolynomial (hasGcd_of_field ℚ zeroTest_rat)
  zeroTest_rat 2).1

theorem zeroTest_A₀ : ∀ a : A₀, a = 0 ∨ a ≠ 0 := (hasGcd_mvPolynomial (hasGcd_of_field ℚ
  zeroTest_rat) zeroTest_rat 2).2

/-- Divisibility in `ℚ[x, y]` is membership in a principal ideal, decided by Gröbner bases. -/
theorem dvdDec_A₀ : DvdDec A₀ := by
  intro a b
  have h : b ∈ lspan [a] ↔ a ∣ b := by
    rw [lspan, show {x | x ∈ [a]} = ({a} : Set A₀) by ext; simp]
    exact Ideal.mem_span_singleton
  rcases mem_lspan_dec [a] b with hb | hb
  · exact Or.inl (h.1 hb)
  · exact Or.inr fun hab => hb (h.2 hab)

/-- `A₀ = ℚ[x, y]` as a smooth GCD domain. -/
noncomputable def A₀SGD : SmoothGCDDomain :=
  ⟨A₀, hasGcd_A₀, zeroTest_A₀, dvdDec_A₀, hasPres_mvPolynomial 2⟩

end BezoutCounterexample
