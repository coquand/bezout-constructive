import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesCoverAll
import BezoutCounterexample.Principalization.ChainLiftReesPresKer
import BezoutCounterexample.Principalization.ChainLiftReesGens
import BezoutCounterexample.Principalization.ChartCoverPtLGlue
import BezoutCounterexample.Principalization.ChartDimPt
import BezoutCounterexample.Principalization.ChainLiftReesGensPtL

/-!
# Chart size of the Rees algebra (Task B, Rees layer S6, §13 step 4)

**`chartDim_rees`**: if `A` has chart size `dim`, the extended Rees algebra of the component
filtration `compFil` has chart size `dim + 1`.

* `hchartn` from `ChartDim.exists_chart_away`; the chart cover `C` from `exists_chartCoverPtL`, all
  charts of size `dim` with `kc = #{i < dim | v₀ i ≠ 0}` heads; `l := dim − kc`, and `A`'s
  certificate is read in the layout `m + (kc + l)` (`ChartDim` is a `Prop`: a rewrite);
* `hglob`, `hloc` from `ChartCoverPtL.global_of_RFB_pt`, `ChartCoverPtL.mem_RFB_of_mem`;
* integer Rees generators (`exists_reesGensZ`), `i^b ∈ F₁` (I3, `exists_pow_mem_compFPt`);
* `exists_smoothCert_rees` and `chartDim_rees_of_cert`, with `ε = finCongr`.

The I4 instances at the local rings `A_q` are hypotheses (filled at the top level from
`Algebra.Smooth ℚ A`); the enumeration `en` of `A` is explicit (an `[Enum A]` binder at integration).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hI hmax h𝔭 hd hw in
/-- **Chart size of the Rees algebra of a component**: `ChartDim A dim → ChartDim R (dim + 1)`. -/
theorem chartDim_rees [Fact (HasPres A)] (l₀ : List A) (hl₀ : I = lspan l₀) {dim : ℕ}
    (hA : ChartDim A dim) (en : ℕ → A) (hen : Function.Surjective en)
    (inst₁ : ∀ q : Pt A, Fact (PolyIndNoeth (Localization.AtPrime q.ker)))
    (inst₂ : ∀ q : Pt A, Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker))
    (inst₃ : ∀ q : Pt A,
      Algebra.FormallySmooth ℚ (IsLocalRing.ResidueField (Localization.AtPrime q.ker))) :
    ChartDim (ReesAlg (compFil hI hmax h𝔭 d)) (dim + 1) := by
  have hchartn := hA.exists_chart_away
  have hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ,
      Nonempty (Chart (Localization.Away f) n) := fun p => by
    obtain ⟨f, hf, hc⟩ := hchartn p
    exact ⟨f, hf, dim, hc⟩
  obtain ⟨C, hCn, hCk⟩ := h𝔭.exists_chartCoverPtL hI hmax l₀ hl₀ dim hchartn
  set kc := (Finset.univ.filter fun i : Fin dim => v₀ i ≠ 0).card with hkc
  have hkd : kc ≤ dim := (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  set l := dim - kc with hl
  have hdim : dim = kc + l := by omega
  rw [hdim] at hA
  obtain ⟨m, G, ⟨e⟩, ⟨hG⟩⟩ := hA
  have hCn' : ∀ k, (C.D k).n = kc + l := fun k => by rw [hCn k]; exact hdim
  have hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀ := fun p h => h𝔭.mem_ptL hI l₀ hl₀ hchart hmax p h
  obtain ⟨r, gZ, δ, hδ, hgF, hgen⟩ := exists_reesGensZ_ptL hI l₀ hl₀ hmax h𝔭 hd hw hchartn G e
  obtain ⟨b, hb⟩ := h𝔭.exists_pow_mem_compFPt_ptL hI l₀ hl₀ hchart hmax hd hw C.hi (((1 : ℤ) : ℚ) / d)
  let ε : Fin ((m + (kc + l)) + (1 + r)) ≃ Fin ((m + r) + ((1 + kc) + l)) := finCongr (by omega)
  obtain ⟨GR, hGR, hcert⟩ := exists_smoothCert_rees G e hG C hCn' hCk
    (fun k b t hb => ChartCoverPtL.global_of_RFB_pt hI l₀ hl₀ hchart C hZ k hb)
    (fun k t z hz => ChartCoverPtL.mem_RFB_of_mem hI C k hz)
    (compFil hI hmax h𝔭 d) (compFil_F hI hmax h𝔭 d) hd hw
    (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) gZ δ (fun j => (hδ j).2) hgF hgen ⟨b, hb⟩
    inst₁ inst₂ inst₃ ε
  have h := chartDim_rees_of_cert G e gZ δ (compFil hI hmax h𝔭 d)
    (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) hgF hgen GR hGR ε hcert
  rwa [show (1 + kc) + l = dim + 1 by omega] at h

end BezoutCounterexample.Principalization
