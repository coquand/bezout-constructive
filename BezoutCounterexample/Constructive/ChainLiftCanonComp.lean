import Mathlib
import BezoutCounterexample.Constructive.CompList
import BezoutCounterexample.Constructive.ChainLiftCanon

/-!
# The canonical component (Task A, C2)

`towerResult` needs a component of `V(l)` **as data**. Components are unique only as a set
(`HasPres.existsUnique_compSet`); the canonical one is the minimum for the decidable total order
`P ≤χ Q :↔ List.le (canonIdx P) (canonIdx Q)` (ChainLiftCanon):

* `CompSet l`: the component ideals `lspan C.gens`, `C : Comp l`;
* `IsCanonComp P`: `P ∈ CompSet l` and `P ≤χ Q` for every `Q ∈ CompSet l`;
  `existsUnique_isCanonComp` (from a component list and `existsUnique_canonMin`; needs `1 ∉ (l)`);
* `canonComp : Comp l`, with generators `canonGens P` (a function of the ideal `P` alone),
  extracted by `uniqueChoice`.
-/

namespace BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] (en : ℕ → A) (hen : Function.Surjective en) (hp : HasPres A)

/-- The component ideals of `V(l)`. -/
def CompSet (l : List A) : Set (Ideal A) := {P | ∃ C : Comp l, lspan C.gens = P}

lemma fg_of_mem_compSet {l : List A} {P : Ideal A} (hP : P ∈ CompSet l) :
    ∃ L : List A, P = lspan L := by
  obtain ⟨C, rfl⟩ := hP
  exact ⟨C.gens, rfl⟩

/-- `P` is the `≤χ`-least component ideal. -/
def IsCanonComp (l : List A) (P : Ideal A) : Prop :=
  ∃ hP : P ∈ CompSet l, ∀ (Q : Ideal A) (hQ : Q ∈ CompSet l),
    List.le (canonIdx en hen hp.mem_dec P (fg_of_mem_compSet hP))
      (canonIdx en hen hp.mem_dec Q (fg_of_mem_compSet hQ))

/-- The component ideals are the ideals of the entries of any component list. -/
lemma mem_compSet_iff {l : List A} {Cs : List (List A)} (hC : IsCompList l Cs) (P : Ideal A) :
    P ∈ CompSet l ↔ ∃ L ∈ Cs, lspan L = P := by
  constructor
  · rintro ⟨C, rfl⟩
    exact Comp.exists_mem hC C
  · rintro ⟨L, hL, rfl⟩
    exact ⟨Comp.ofMem hC hL, rfl⟩

/-- **The canonical component is unique.** -/
theorem existsUnique_isCanonComp (l : List A) (hl : (1 : A) ∉ lspan l) :
    ∃! P : Ideal A, IsCanonComp en hen hp l P := by
  obtain ⟨Cs, hC⟩ := hp.exists_compList l
  exact existsUnique_canonMin en hen hp.mem_dec (CompSet l) Cs (hC.ne_nil hl)
    (mem_compSet_iff hC)

/-- **The canonical component**, as data: generators `canonGens P` of the `≤χ`-least component
ideal `P`. -/
noncomputable def canonComp (l : List A) (hl : (1 : A) ∉ lspan l) : Comp l :=
  let P := uniqueChoice (existsUnique_isCanonComp en hen hp l hl)
  have hP : P.1 ∈ CompSet l := P.2.1
  have hgens : lspan (canonGens en hen hp.mem_dec P.1 (fg_of_mem_compSet hP)) = P.1 :=
    lspan_canonGens en hen hp.mem_dec P.1 (fg_of_mem_compSet hP)
  { gens := canonGens en hen hp.mem_dec P.1 (fg_of_mem_compSet hP)
    primeFF := by
      obtain ⟨C, hC⟩ := hP
      rw [hgens, ← hC]; exact C.primeFF
    le := by
      obtain ⟨C, hC⟩ := hP
      rw [hgens, ← hC]; exact C.le
    minimal := by
      obtain ⟨C, hC⟩ := hP
      rw [hgens, ← hC]; exact C.minimal }

/-- The ideal of the canonical component is the canonical one. -/
theorem isCanonComp_canonComp (l : List A) (hl : (1 : A) ∉ lspan l) :
    IsCanonComp en hen hp l (lspan (canonComp en hen hp l hl).gens) := by
  have h := (uniqueChoice (existsUnique_isCanonComp en hen hp l hl)).2
  have hgens := lspan_canonGens en hen hp.mem_dec _ (fg_of_mem_compSet h.1)
  change IsCanonComp en hen hp l (lspan (canonGens en hen hp.mem_dec _ (fg_of_mem_compSet h.1)))
  rw [hgens]
  exact h

/-- Any two canonical components have the same ideal. -/
theorem IsCanonComp.unique {l : List A} {P Q : Ideal A} (hP : IsCanonComp en hen hp l P)
    (hQ : IsCanonComp en hen hp l Q) : P = Q := by
  obtain ⟨hPm, hPmin⟩ := hP
  obtain ⟨hQm, hQmin⟩ := hQ
  exact canonIdx_injective en hen hp.mem_dec (fg_of_mem_compSet hPm) (fg_of_mem_compSet hQm)
    (List.le_antisymm (hPmin Q hQm) (hQmin P hPm))

end BezoutCounterexample.Constructive
