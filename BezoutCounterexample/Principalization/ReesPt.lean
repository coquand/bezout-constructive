import BezoutCounterexample.Principalization.MaxInvPt
import BezoutCounterexample.Principalization.InvariantPt
import BezoutCounterexample.ReesComp

/-!
# The data of `ReesData` from a presentation (D3.5, leaf)

The producers of `ReesData` (`PrincipalizationStar:170`, `ChainLiftStar:103`) take `maxinv`,
a component from `theorem_3_3_3` and a common denominator from `ΓN`. In the D3.5 integration
`ReesData` carries `e` with `IsMaxInv I e`, generators `Pg` of the locus ideal at points, a
component record `comp : Comp Pg` (`𝔭 := lspan comp.gens`), the support bound, and `d`
(`docs/d3-design.md` §5, rewrite-tasks C2/C8). The producer side needs (Prop level here; the data
version is Task A's `uniqueChoice`/`canonComp`):

* `exists_locus_data`: from a presentation, generators of `I` and a chart size: `e` with
  `IsMaxInv I e`, attained at an explicit point, the support bound `N`, and generators `Pg` of
  `locusPt I e` with `1 ∉ (Pg)`;
* `exists_comp_data`: moreover a component record `Comp Pg` (the canonical one, `canonComp`,
  for an enumeration), giving `LocusComp I e (lspan comp.gens)`;
* `ReesData.CompData.ofIsMaxInv`: the `CompData` record of `ReesComp` from these data, when
  `maxinv I = e` (the comparison is only needed while `ReesData` still reads `maxinv`).

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

/-- **The locus data from a presentation.** -/
theorem exists_locus_data (hp : HasPres A) {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤)
    {N : ℕ} (hN : ChartDim A N) (gens : List A) (hgens : I = lspan gens) :
    ∃ e : ℕ → ℚ, IsMaxInvPt I e ∧ (∃ q : Pt A, I ≤ q.ker ∧ InvAt I q.ker e) ∧
      (∀ i, N ≤ i → e i = 0) ∧ ∃ Pg : List A, locusPt I e = lspan Pg ∧ (1 : A) ∉ lspan Pg := by
  obtain ⟨e, he, q, hIq, hv⟩ := exists_isMaxInv_pt hp hI hItop hN gens hgens
  have hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0 :=
    fun _ _ _ hv' => invAt_bounded hN hv'
  have hb₀ : ∀ i, N ≤ i → e i = 0 := fun i hi => hbd q.ker e hv i hi
  obtain ⟨Pg, hPg⟩ := exists_locusPt_gens_pos hI he hbd hb₀ hp gens hgens fun p => by
    obtain ⟨f, hf, hc⟩ := hN.exists_chart_away p
    exact ⟨f, hf, N, hc⟩
  refine ⟨e, he, ⟨q, hIq, hv⟩, hb₀, Pg, hPg, fun h1 => ?_⟩
  rw [← hPg] at h1
  exact (Pt.ker_isMaximal q).ne_top ((Ideal.eq_top_iff_one _).2 (h1 q hIq hv))

/-- **A component record of the locus**, with its `LocusComp`. -/
theorem exists_comp_data (hp : HasPres A) {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤)
    {N : ℕ} (hN : ChartDim A N) (gens : List A) (hgens : I = lspan gens) :
    ∃ e : ℕ → ℚ, IsMaxInvPt I e ∧ (∃ q : Pt A, I ≤ q.ker ∧ InvAt I q.ker e) ∧ (∀ i, N ≤ i → e i = 0) ∧
      ∃ Pg : List A, locusPt I e = lspan Pg ∧ ∃ P : Comp Pg, LocusComp I e (lspan P.gens) := by
  obtain ⟨e, he, hq, hb₀, Pg, hPg, h1⟩ := exists_locus_data hp hI hItop hN gens hgens
  obtain ⟨Cs, hC⟩ := (HasPres.exists_compList hp) Pg
  obtain ⟨C, hCm⟩ := List.exists_mem_of_ne_nil Cs (hC.ne_nil h1)
  refine ⟨e, he, hq, hb₀, Pg, hPg, Comp.ofMem hC hCm, ?_⟩
  exact LocusComp.of_comp hPg (fun _ _ _ hv' => invAt_bounded hN hv') hb₀ ⟨gens, hgens⟩
    ⟨N, hN.exists_chart_away⟩ _

end BezoutCounterexample.Principalization

namespace BezoutCounterexample

open Principalization Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- The `CompData` record of `ReesComp` from relation-level data, when `S.𝔭` is the component
(comparison with `maxinv`, needed only until `ReesData` carries `e`). -/
def ReesData.CompData.ofIsMaxInv (S : ReesData A) {e : ℕ → ℚ} (he : S.e = e)
    (Pg : List A) (hPg : locusPt S.I e = lspan Pg) (P : Comp Pg) (h𝔭 : S.𝔭 = lspan P.gens)
    {N : ℕ}
    (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt S.I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (hb₀ : ∀ i, N ≤ i → e i = 0) : S.CompData :=
  ⟨Pg, he ▸ hPg, P, h𝔭, N, hbd, he ▸ hb₀⟩

end BezoutCounterexample
