import BezoutCounterexample.Constructive.PolyBar

/-!
# Rings all of whose polynomial rings are inductively Noetherian

`PolyIndNoeth R :≡ ∀ k, IndNoeth R[Y₁, …, Y_k]`. This class contains `ℚ` (`polyBar`) and is closed
under surjections, localisations, polynomial extensions and finite-type algebras, with no choice
(each closure is a transfer of the bar along a ring map, `NoethBar.lean`). It therefore contains
every ring built from `ℚ` in HM's pipeline: points of f.t. `ℚ`-algebras, their quotients, the
polynomial localisations of `Stable`, the vertex localisations of `Vertex`, the Rees algebras of
`Rees`. And it gives `SeqCond` for the Rees ring of every f.g. ideal of every quotient
(`PolyIndNoeth.seqCond_rees`), which is what (F1)/(F2) consume.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

/-- Every polynomial ring in finitely many variables over `R` is inductively Noetherian. -/
def PolyIndNoeth (R : Type*) [CommRing R] : Prop := ∀ k : ℕ, IndNoeth (MvPolynomial (Fin k) R)

variable {R S : Type*} [CommRing R] [CommRing S]

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PolyIndNoeth

theorem indNoeth (h : PolyIndNoeth R) : IndNoeth R :=
  (h 0).of_surjective (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom
    (MvPolynomial.isEmptyRingEquiv R (Fin 0)).surjective

theorem of_surjective (f : R →+* S) (hf : Function.Surjective f) (h : PolyIndNoeth R) :
    PolyIndNoeth S := fun k =>
  (h k).of_surjective (MvPolynomial.map f) (MvPolynomial.map_surjective f hf)

theorem quotient (h : PolyIndNoeth R) (J : Ideal R) : PolyIndNoeth (R ⧸ J) :=
  h.of_surjective _ Ideal.Quotient.mk_surjective

theorem of_isLocalization (M : Submonoid R) [Algebra R S] [IsLocalization M S]
    (h : PolyIndNoeth R) : PolyIndNoeth S := fun k =>
  (h k).of_isLocalization (M.map (MvPolynomial.C (σ := Fin k)))

theorem mvPolynomial (h : PolyIndNoeth R) (m : ℕ) : PolyIndNoeth (MvPolynomial (Fin m) R) :=
  fun k => by
    refine (h (k + m)).of_surjective
      ((MvPolynomial.sumRingEquiv R (Fin k) (Fin m)).toRingHom.comp
        (MvPolynomial.renameEquiv R finSumFinEquiv.symm).toRingEquiv.toRingHom) ?_
    exact (MvPolynomial.sumRingEquiv R (Fin k) (Fin m)).surjective.comp
      (MvPolynomial.renameEquiv R finSumFinEquiv.symm).surjective

theorem of_finiteType [Algebra R S] [hS : Algebra.FiniteType R S] (h : PolyIndNoeth R) :
    PolyIndNoeth S := by
  obtain ⟨m, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hS
  exact (h.mvPolynomial m).of_surjective f.toRingHom hf

/-- `SeqCond` for the Rees ring of a f.g. ideal of a quotient. -/
theorem seqCond_rees (h : PolyIndNoeth R) (J : Ideal R) {k : ℕ} (y : Fin k → R ⧸ J) :
    SeqCond (reesSubring (Ideal.span (Set.range y))) :=
  (indNoeth_rees y ((h.quotient J) k)).seqCond

end PolyIndNoeth

theorem polyIndNoeth_rat : PolyIndNoeth ℚ := polyBar

/-- Finitely generated `ℚ`-algebras. -/
theorem polyIndNoeth_of_finiteType (A : Type*) [CommRing A] [Algebra ℚ A]
    [Algebra.FiniteType ℚ A] : PolyIndNoeth A :=
  polyIndNoeth_rat.of_finiteType

end BezoutCounterexample.Constructive
