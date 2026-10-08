import BezoutCounterexample.Principalization.QuotSeq
import BezoutCounterexample.Constructive.PolyNoeth

/-!
# `QuotSeqCond` from `PolyIndNoeth`

`PolyIndNoeth R` (every `R[Y₁, …, Y_k]` inductively Noetherian, `Constructive/PolyNoeth.lean`)
implies `QuotSeqCond R`. As an instance `[Fact (PolyIndNoeth R)] → Fact (QuotSeqCond R)` this lets
the files whose auxiliary rings (polynomial localisations, vertex localisations, Rees algebras)
are again in `PolyIndNoeth` replace `[IsNoetherianRing S]` by `[Fact (PolyIndNoeth S)]`.
-/

namespace BezoutCounterexample.Principalization

open IsLocalRing Constructive

theorem quotSeqCond_of_polyIndNoeth {R : Type*} [CommRing R] (h : PolyIndNoeth R) :
    QuotSeqCond R := fun J _ _ y hy => by
  rw [hy]; exact h.seqCond_rees J y

instance fact_quotSeqCond_of_polyIndNoeth {R : Type*} [CommRing R] [h : Fact (PolyIndNoeth R)] :
    Fact (QuotSeqCond R) :=
  ⟨quotSeqCond_of_polyIndNoeth h.out⟩

/-- Points of finitely generated `ℚ`-algebras. -/
instance fact_polyIndNoeth_atPrime {A : Type*} [CommRing A] [Algebra ℚ A]
    [Algebra.FiniteType ℚ A] (P : Ideal A) [P.IsPrime] :
    Fact (PolyIndNoeth (Localization.AtPrime P)) :=
  ⟨(polyIndNoeth_of_finiteType A).of_isLocalization P.primeCompl⟩

/-- Localisations. -/
theorem fact_polyIndNoeth_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [h : Fact (PolyIndNoeth R)] :
    Fact (PolyIndNoeth S) :=
  ⟨h.out.of_isLocalization M⟩

/-- Finite-type algebras (e.g. Rees algebras). -/
theorem fact_polyIndNoeth_of_finiteType {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [h : Fact (PolyIndNoeth R)] : Fact (PolyIndNoeth S) :=
  ⟨h.out.of_finiteType⟩

end BezoutCounterexample.Principalization
