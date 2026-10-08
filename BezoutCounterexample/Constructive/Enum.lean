import BezoutCounterexample.Constructive.Presented
import BezoutCounterexample.Principalization.ChainLiftEnum

/-!
# Enumerations of presented rings as data (D3.5, group B, leaf)

The torsor of a principalization step is built from generators of the filtration steps
(`gensF`, `genPairs`). In the D3.5 integration these become the canonical generators
(`canonGensF`, `canonGenPairs`, ReesGlobal), which need an enumeration `en : ℕ → A`. It is carried
as an instance binder `[Enum A] [Fact (HasPres A)]` (decided by coll-01, 2026-10-05):

* `class Enum A`: data (`en`), with the surjectivity `hen` a `Prop` field;
* **no global or derived instances**: the only sources are an explicit `letI` at the top (inside
  a `Prop` proof, from `HasPres.nonempty_enum`) and the stage data of the tower (`Enum.ofPres`, with
  `enumQuo`/`enumPoly` for the next ring), so `gensF` is a function of the stage's enumeration and
  never of instance search;
* `Enum.ofPres`: the explicit enumeration of `ℚ[Y]/(G)` (`enumPoly`, encodable lists of terms)
  transported along a presentation `ℚ[Y]/(G) ≃+* A`;
* `HasPres.nonempty_enum : HasPres A → Nonempty (Enum A)`.

Leaf module.
-/

noncomputable section

set_option warn.classDefReducibility false

namespace BezoutCounterexample.Constructive

/-- **An enumeration of `A`, as data.** Never declared as a global instance. -/
class Enum (A : Type*) where
  en : ℕ → A
  hen : Function.Surjective en

/-- The enumeration of a presented ring from its presentation (`enumPoly`). -/
def Enum.ofPres {A : Type*} [CommRing A] {n : ℕ} (G : List (MvPolynomial (Fin n) ℚ))
    (e : (MvPolynomial (Fin n) ℚ ⧸ lspan G) ≃+* A) : Enum A where
  en k := e (Ideal.Quotient.mk _ (enumPoly n k))
  hen x := by
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (e.symm x)
    obtain ⟨k, rfl⟩ := enumPoly_surjective n p
    exact ⟨k, by show e _ = x; rw [hp, RingEquiv.apply_symm_apply]⟩

/-- Transport of an enumeration along a ring isomorphism. -/
def Enum.ofEquiv {A B : Type*} [CommRing A] [CommRing B] (E : Enum A) (e : A ≃+* B) : Enum B where
  en k := e (E.en k)
  hen x := by
    obtain ⟨k, hk⟩ := E.hen (e.symm x)
    exact ⟨k, by show e _ = x; rw [hk, RingEquiv.apply_symm_apply]⟩

/-- **A presented ring has an enumeration** (for `obtain`/`letI` inside `Prop` proofs). -/
theorem HasPres.nonempty_enum {A : Type*} [CommRing A] (h : HasPres A) : Nonempty (Enum A) := by
  obtain ⟨n, G, ⟨e⟩⟩ := h
  exact ⟨Enum.ofPres G e⟩

end BezoutCounterexample.Constructive
