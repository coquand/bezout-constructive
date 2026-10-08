import Mathlib
import BezoutCounterexample.Principalization.ChainLiftPresCertPt
import BezoutCounterexample.Principalization.ChainLiftChartDimRees

/-!
# hR4b for the Rees algebra (PresentationCert)

**`rees_formallySmooth_pt`**: `FormallySmooth ℚ R_q` at every point `q` of the Rees algebra
`R = ReesAlg (compFil …)`, the `hR4b` binder of `drop_pt`. `R` has chart size `dim + 1`
(`chartDim_rees`, whose own `inst₂` at the points of `A` is `ChartDim.formallySmooth_pt` of `A`),
and `ChartDim.formallySmooth_pt` applies to `R`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hI hmax h𝔭 hd hw in
/-- **hR4b**: `FormallySmooth ℚ R_q` at the points of the Rees algebra of a component. -/
theorem rees_formallySmooth_pt [Fact (HasPres A)] (l₀ : List A) (hl₀ : I = lspan l₀) {dim : ℕ}
    (hA : ChartDim A dim) (en : ℕ → A) (hen : Function.Surjective en)
    (inst₁ : ∀ q : Pt A, Fact (PolyIndNoeth (Localization.AtPrime q.ker)))
    (inst₃ : ∀ q : Pt A,
      Algebra.FormallySmooth ℚ (IsLocalRing.ResidueField (Localization.AtPrime q.ker)))
    (q : Pt (ReesAlg (compFil hI hmax h𝔭 d))) :
    Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker) :=
  (chartDim_rees hI hmax h𝔭 hd hw l₀ hl₀ hA en hen inst₁ hA.formallySmooth_pt inst₃).formallySmooth_pt
    q

end BezoutCounterexample.Principalization
