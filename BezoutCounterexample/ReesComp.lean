import BezoutCounterexample.Rees
import BezoutCounterexample.Principalization.MaxLocusPt
import BezoutCounterexample.Constructive.ChainLiftCanonComp

/-!
# The component of `ReesData` as data (D3.3e, leaf)

`ReesData.h𝔭c` produces `LocusComp S.I (maxinv S.I) S.𝔭` through the TEMPORARY classical bridge
`LocusComp.of_minimalPrimes` (generators of `locusPt` from `IsNoetherianRing`, `locusPt = locusIdeal`).
Here the producer side supplies the data instead (`docs/d3-design.md` §8.5, D3.3e; I1):

* `ReesData.CompData S`: explicit generators `Pg` of the locus ideal at points, a component record
  `comp : Comp Pg` with `S.𝔭 = lspan comp.gens`, and the support bound of the invariants;
* `ReesData.CompData.locusComp`: the `LocusComp` from these data (constructive, `LocusComp.of_comp`);
* `ReesData.exists_locusPt_gens`: the generators `Pg` from `S.Igens` and a presentation (constructive,
  `exists_locusPt_gens_pos`);
* `ReesData.CompData.ofCanon`: the record for the canonical component (`canonComp`, Task A C2), when
  `S.𝔭` is chosen as that component.

Leaf module. In the integration diff `ReesData` gets these fields (`𝔭` defined as
`lspan comp.gens`), `S.h𝔭c := S.comp.locusComp`, and the bridge and `LocusComp.toMin` are deleted.
-/

noncomputable section

namespace BezoutCounterexample

open Principalization Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- **The component of `ReesData` as data** (D3.3e, I1). -/
structure ReesData.CompData (S : ReesData A) where
  /-- generators of the locus ideal at points -/
  Pg : List A
  hPg : locusPt S.I S.e = lspan Pg
  /-- the component, as an explicit prime -/
  comp : Comp Pg
  h𝔭 : S.𝔭 = lspan comp.gens
  /-- the support bound of the invariants -/
  N : ℕ
  hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt S.I 𝔪 v → ∀ i, N ≤ i → v i = 0
  hb₀ : ∀ i, N ≤ i → S.e i = 0

namespace ReesData

variable {S : ReesData A}

/-- **The component from the data** (constructive; replaces the bridge in `ReesData.h𝔭c`). -/
theorem CompData.locusComp (R : S.CompData) : LocusComp S.I (S.e) S.𝔭 := by
  rw [R.h𝔭]; exact LocusComp.of_comp R.hPg R.hbd R.hb₀ ⟨S.Igens, S.hIgens⟩
    (S.hN.imp fun _ h => h.exists_chart_away) R.comp

variable (S) in
/-- **Generators of the locus ideal at points**, from `S.Igens` and a presentation. -/
theorem exists_locusPt_gens [IsNoetherianRing A] (hp : HasPres A) {N : ℕ}
    (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt S.I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (hb₀ : ∀ i, N ≤ i → S.e i = 0) :
    ∃ Pg : List A, locusPt S.I (S.e) = lspan Pg :=
  exists_locusPt_gens_pos S.ne_bot S.hmax hbd hb₀ hp S.Igens S.hIgens fun p => by
    obtain ⟨k, hk⟩ := S.hN
    obtain ⟨f, hf, hc⟩ := hk.exists_chart_away p
    exact ⟨f, hf, k, hc⟩

variable (S) in
/-- **The record for the canonical component** (Task A C2), when `S.𝔭` is that component. -/
def CompData.ofCanon (en : ℕ → A) (hen : Function.Surjective en) (hp : HasPres A) (Pg : List A)
    (hPg : locusPt S.I (S.e) = lspan Pg) (h1 : (1 : A) ∉ lspan Pg)
    (h𝔭 : S.𝔭 = lspan (canonComp en hen hp Pg h1).gens) {N : ℕ}
    (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt S.I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (hb₀ : ∀ i, N ≤ i → S.e i = 0) : S.CompData :=
  ⟨Pg, hPg, canonComp en hen hp Pg h1, h𝔭, N, hbd, hb₀⟩

end ReesData

end BezoutCounterexample
