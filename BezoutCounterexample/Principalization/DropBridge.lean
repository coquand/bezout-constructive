import BezoutCounterexample.Principalization.DropPt
import BezoutCounterexample.Principalization.ReesI4
import BezoutCounterexample.Principalization.Globalize
import BezoutCounterexample.Principalization.PolyQuot
import BezoutCounterexample.Principalization.ChartAtPrime
import BezoutCounterexample.Principalization.ChainLiftChartDimRees
import BezoutCounterexample.Principalization.ChainLiftReesFSPt
import BezoutCounterexample.Constructive.Enum

/-!
# `drop` through `drop_pt` (D3.7a, D3.7b)

`drop_of_pt` has the statement of `drop` (Drop) and is proved by `drop_pt` (DropPt, coll-8a) at the
point `Pt.ofIsMaximal P`. D3.7b: the tower carries `ChartDim` (`StarC`, `ReesData.hN`), taken here as
`[Fact (∃ k, ChartDim A k)]`. From it:

* charts of one size near every point of `A` (`ChartDim.exists_chart_away`);
* the charts of the Rees algebra (`chartDim_rees`, then `exists_chart_away`);
* `hR4b` (`rees_formallySmooth_pt`, coll-8a's PresentationCert; `FormallySmooth` at points of `A`
  from `ChartDim.formallySmooth_pt`);
* `FiniteType A R` (`reesAlg_finiteType_ptL`); `hR4a`, `hR4c` from ReesI4 (coll-8a) at points.

Still classical, marked `TEMPORARY`:

* generators of `I` (`IsNoetherian.noetherian`);
* the point of `P` (`Pt.ofIsMaximal`, `Classical.em` zero test).

Used by `ReesData.drop` (Rees) and `torsor_invAt` (TorsorInv) in place of `drop`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

/-- **`drop` through `drop_pt`** (statement of `drop`). -/
theorem drop_of_pt [Fact (Constructive.HasPres A)] [Fact (∃ k, ChartDim A k)] (P : Ideal (ReesAlg (compFil hI hmax h𝔭 d)))
    [hPm : P.IsMaximal]
    (hIwP : weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil hI hmax h𝔭 hd) ≤ P)
    (hsP : reesS (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj) ∈ P)
    {j : ℤ} (hj : 1 ≤ j) {f : A} (hf : f ∈ (compFil hI hmax h𝔭 d).F j)
    (hyP : (⟨LaurentPolynomial.C f * T j, C_mul_T_mem_ReesAlg hf⟩ :
      ReesAlg (compFil hI hmax h𝔭 d)) ∉ P)
    {v : ℕ → ℚ} (hv : InvAt (weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil hI hmax h𝔭 hd)) P v) :
    toLex v₀ < toLex v := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A
  -- TEMPORARY: generators of `I`, classically
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian (I : Submodule A A))
  obtain ⟨l, hlt⟩ := Quot.exists_rep t.val
  have hl : I = Constructive.lspan l := by
    rw [Constructive.lspan, ← ht]
    show Submodule.span A _ = Submodule.span A _
    congr 1
    ext x
    rw [Finset.mem_coe, Finset.mem_def, ← hlt]
    exact Multiset.mem_coe.symm
  -- charts of one size near every point of `A`, from `ChartDim A dim`
  obtain ⟨dim, hN⟩ := (Fact.out : ∃ k, ChartDim A k)
  have hchartn := hN.exists_chart_away
  have : Algebra.FiniteType A (ReesAlg (compFil hI hmax h𝔭 d)) :=
    reesAlg_finiteType_ptL hI l hl hmax h𝔭 hd hw hchartn
  have : Algebra.FiniteType ℚ (ReesAlg (compFil hI hmax h𝔭 d)) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  -- I4 on the Rees algebra: hR4a, hR4c at points (ReesI4, coll-8a)
  have hR4a : ∀ q : Pt (ReesAlg (compFil hI hmax h𝔭 d)),
      Fact (PolyIndNoeth (Localization.AtPrime q.ker)) :=
    fun q => rees_i4a_ptL hI l hl hmax h𝔭 hd hw hchartn q
  have hR4c : ∀ q : Pt (ReesAlg (compFil hI hmax h𝔭 d)),
      Algebra.FormallySmooth ℚ (IsLocalRing.ResidueField (Localization.AtPrime q.ker)) :=
    fun q => Pt.formallySmooth_residueField q
  -- the charts of `R` (`chartDim_rees`) and hR4b (`rees_formallySmooth_pt`)
  obtain ⟨E⟩ := Constructive.HasPres.nonempty_enum (Fact.out : Constructive.HasPres A)
  have hA4a : ∀ q : Pt A, Fact (PolyIndNoeth (Localization.AtPrime q.ker)) :=
    fun q => fact_polyIndNoeth_atPrime q.ker
  have hNR := chartDim_rees hI hmax h𝔭 hd hw l hl hN E.en E.hen hA4a hN.formallySmooth_pt
    (fun q => Pt.formallySmooth_residueField q)
  have hR4b : ∀ q : Pt (ReesAlg (compFil hI hmax h𝔭 d)),
      Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker) :=
    rees_formallySmooth_pt hI hmax h𝔭 hd hw l hl hN E.en E.hen hA4a
      (fun q => Pt.formallySmooth_residueField q)
  have hchartR : ∀ p : Pt (ReesAlg (compFil hI hmax h𝔭 d)), ∃ f, f ∉ p.ker ∧ ∃ n : ℕ,
      Nonempty (Chart (Localization.Away f) n) := fun p => by
    obtain ⟨f, hf, hc⟩ := hNR.exists_chart_away p
    exact ⟨f, hf, _, hc⟩
  -- TEMPORARY: the point of the maximal ideal `P` (`Classical.em` zero test)
  have hk : (Pt.ofIsMaximal P).ker = P := Pt.ker_ofIsMaximal P
  have hcongr : ∀ {𝔪 𝔪' : Ideal (ReesAlg (compFil hI hmax h𝔭 d))} [𝔪.IsPrime] [𝔪'.IsPrime],
      𝔪 = 𝔪' → InvAt (weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil hI hmax h𝔭 hd)) 𝔪 v →
      InvAt (weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil hI hmax h𝔭 hd)) 𝔪' v := by
    intro _ _ _ _ h hv; subst h; exact hv
  exact drop_pt hI l hl hmax h𝔭 hchartn hd hw (hR4a := hR4a) (hR4b := hR4b) (hR4c := hR4c)
    hchartR (Pt.ofIsMaximal P) (by rw [hk]; exact hIwP) (by rw [hk]; exact hsP) hj hf
    (by rw [hk]; exact hyP) (hcongr hk.symm hv)

end BezoutCounterexample.Principalization
