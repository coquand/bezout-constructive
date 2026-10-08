import BezoutCounterexample.Principalization.StarPt
import BezoutCounterexample.Principalization.ReesPt
import BezoutCounterexample.Principalization.DivisorialMp
import BezoutCounterexample.Principalization.TorsorMp
import BezoutCounterexample.Principalization.ChainLiftChartDimUCert
import BezoutCounterexample.Principalization.ChainLiftReesFSPt
import BezoutCounterexample.Principalization.ReesI4
import BezoutCounterexample.Constructive.Enum

/-!
# The complexity at points and the two stages with `IsMaxInvPt` (top chain, stage 2)

The recursion of `principalization_star(_tower)` ran on `(maxinv 𝔟, numComponents 𝔟)` and read the
decrease off `divisorial_decrease`/`torsor_invariant` (classical `maxinv`, `components`). Here:

* `IsComplexity 𝔟 μ`: `μ.1` is the maximal invariant (`IsMaxInv`), attained at an explicit point,
  and `μ.2` counts the components of the locus ideal at points (`NumComp` of generators `Pg` of
  `locusPt 𝔟 μ.1`); `exists_isComplexity` from a presentation, a chart size and generators
  (`exists_locus_data`, `HasPres.exists_numComp`);
* `PrincipalizationData.divisorial_decrease_mp` (`divisorial_decrease_pt_mp`) and
  `torsor_decrease_mp` (`torsor_decrease_pt_mp`, `hmaxPt := S.he`): the inputs at points
  (`hchart` from `ChartDim`, `hR4b`/`hchartR` as in `drop_of_pt`, `hexU` from
  `exists_invAt_semicont_ptL` on `U` with the chart size `chartDim_U_cert`) are produced from
  `S.Igens`, `S.hN` and the presentation.

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization Constructive

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B]

/-- **The complexity at points**: `μ.1` is the maximal invariant of `𝔟`, attained at an explicit
point, and the locus ideal at points has generators with `μ.2` components. -/
def IsComplexity (𝔟 : Ideal B) (μ : (ℕ → ℚ) × ℕ) : Prop :=
  IsMaxInvPt 𝔟 μ.1 ∧ (∃ q : Pt B, 𝔟 ≤ q.ker ∧ InvAt 𝔟 q.ker μ.1) ∧
    ∃ Pg : List B, locusPt 𝔟 μ.1 = lspan Pg ∧ NumComp Pg μ.2

/-- The complexity exists, from a presentation, a chart size and generators. -/
theorem exists_isComplexity (hp : HasPres B) {𝔟 : Ideal B} (h𝔟 : 𝔟 ≠ ⊥) (htop : 𝔟 ≠ ⊤)
    {N : ℕ} (hN : ChartDim B N) (gens : List B) (hgens : 𝔟 = lspan gens) :
    ∃ μ, IsComplexity 𝔟 μ := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℚ B
  obtain ⟨e, he, hq, -, Pg, hPg, -⟩ := exists_locus_data hp h𝔟 htop hN gens hgens
  obtain ⟨c, hc⟩ := hp.exists_numComp Pg
  exact ⟨(e, c), he, hq, Pg, hPg, hc⟩

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

namespace PrincipalizationData

variable (S : PrincipalizationData A)

/-- Charts of one size near every explicit point, from a chart size. -/
theorem hchart_of_chartDim {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (hn : ChartDim R n) :
    ∀ p : Pt R, ∃ f : R, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n) :=
  fun p => by
    obtain ⟨f, hf, hc⟩ := hn.exists_chart_away p
    exact ⟨f, hf, _, hc⟩

/-- **Lemma 4.1 at points** (`divisorial_decrease_pt_mp`, `hmaxPt := S.he`). -/
theorem divisorial_decrease_mp [Fact (HasPres A)] (hk : S.k = 1) {a : ℕ}
    (ha : S.e 0 = 1 / (a : ℚ)) {v₁ : ℕ → ℚ}
    (hq₁ : ∃ q : Pt A, S.divI₁ a ≤ q.ker ∧ InvAt (S.divI₁ a) q.ker v₁)
    {Pg Pg₁ : List A} (hPg : locusPt S.I S.e = lspan Pg)
    (hPg₁ : locusPt (S.divI₁ a) v₁ = lspan Pg₁) {c c₁ : ℕ} (hc : NumComp Pg c)
    (hc₁ : NumComp Pg₁ c₁) : v₁ ≺ S.e ∨ (v₁ = S.e ∧ c₁ < c) := by
  obtain ⟨_, hN⟩ := S.hN
  exact divisorial_decrease_pt_mp S.ne_bot S.Igens S.hIgens (hchart_of_chartDim hN) S.he
    (S.a_pos hk ha) ha (S.divisorial_le hk ha) S.h𝔭c (S.divisorial_𝔭_eq hk) hq₁ hPg hPg₁ hc hc₁

/-- **Lemma 4.3 at points** (`torsor_decrease_pt_mp`, `hmaxPt := S.he`). The generators
`l₁` of `I₁` give the invariants at points of `U` (`hexU`). -/
theorem torsor_decrease_mp [Constructive.Enum A] [Fact (HasPres A)] (_hk : 2 ≤ S.k) {v₁ : ℕ → ℚ}
    (hq₁ : ∃ q : Pt S.U, S.I₁ ≤ q.ker ∧ InvAt S.I₁ q.ker v₁)
    (l₁ : List S.U) (hl₁ : S.I₁ = lspan l₁)
    {Pg : List A} (hPg : locusPt S.I S.e = lspan Pg) {Pg₁ : List S.U}
    (hPg₁ : locusPt S.I₁ v₁ = lspan Pg₁) {c c₁ : ℕ} (hc : NumComp Pg c)
    (hc₁ : NumComp Pg₁ c₁) : v₁ ≺ S.e ∨ (v₁ = S.e ∧ c₁ < c) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A
  have : Fact (∃ k, ChartDim A k) := ⟨S.hN⟩
  obtain ⟨dim, hN⟩ := S.hN
  have hA4a : ∀ q : Pt A, Fact (PolyIndNoeth (Localization.AtPrime q.ker)) :=
    fun q => fact_polyIndNoeth_atPrime q.ker
  -- the charts of `R` (`chartDim_rees`) and hR4b (`rees_formallySmooth_pt`), as in `drop_of_pt`
  have hNR := chartDim_rees S.ne_bot S.hmax S.h𝔭c S.d_pos S.hw S.Igens S.hIgens hN
    Constructive.Enum.en Constructive.Enum.hen
    hA4a hN.formallySmooth_pt (fun q => Pt.formallySmooth_residueField q)
  have hR4b := rees_formallySmooth_pt S.ne_bot S.hmax S.h𝔭c S.d_pos S.hw S.Igens S.hIgens hN
    Constructive.Enum.en Constructive.Enum.hen hA4a (fun q => Pt.formallySmooth_residueField q)
  -- invariants at the points of `U` (`exists_invAt_semicont_ptL`, chart size `chartDim_U_cert`)
  have hI₁ : S.I₁ ≠ ⊥ := torsorI_ne_bot S.ne_bot S.hmax S.h𝔭c S.d_pos S.π_mem_fil S.π_ne_zero
  have hexU : ∀ q : Pt S.U, S.I₁ ≤ q.ker → ∃ v, InvAt S.I₁ q.ker v := fun q hq => by
    obtain ⟨v, hv, -⟩ := exists_invAt_semicont_ptL hI₁ l₁ hl₁
      (hchart_of_chartDim (chartDim_U_cert S hN Constructive.Enum.en Constructive.Enum.hen)) q hq
    exact ⟨v, hv⟩
  exact torsor_decrease_pt_mp S.ne_bot S.hmax S.he S.h𝔭c S.d_pos S.hw S.π_mem_fil
    S.π_ne_zero S.Igens S.hIgens (hchart_of_chartDim hN) hN hR4b (hchart_of_chartDim hNR) hexU
    hq₁ hPg hPg₁ hc hc₁

end PrincipalizationData

end BezoutCounterexample
