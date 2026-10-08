import Mathlib
import BezoutCounterexample.Torsor
import BezoutCounterexample.Principalization.ChainLiftChartDimRees
import BezoutCounterexample.Principalization.ChainLiftChartDimJou
import BezoutCounterexample.Principalization.Globalize
import BezoutCounterexample.Principalization.PolyQuot

/-!
# Chart size of the torsor by certificates (Task B, Rees layer S6, step 4b)

The chain `A → 𝓡 → U` carries certificates: `chartDim_rees` gives `ChartDim 𝓡 (dim + 1)`, and
`ChartDim.jou` gives `ChartDim (J_𝓡(h)) (dim + 1 + ℓ)` for any tuple `h` of the Rees algebra.

* `chartDim_jou_rees`: generic in the component data (`LocusComp`) and in `h`; the I4 instances at the
  local rings `A_q` are filled from `Algebra.Smooth ℚ A` (`fact_polyIndNoeth_atPrime`,
  `fs_localization`, `fe_residueField`);
* **`chartDim_U_cert`**: the torsor `S.U` of a principalization step; the certificate form of
  `chartDim_U` (no zero test of `A`, no presentation of `U`, no `exists_smoothCert_of_smooth`).

The enumeration `en` of `A` is explicit (an `[Enum A]` binder at integration).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- The I4 instances at the points of `A`, from smoothness. -/
lemma i4_of_smooth :
    (∀ q : Pt A, Fact (PolyIndNoeth (Localization.AtPrime q.ker))) ∧
    (∀ q : Pt A, Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker)) ∧
    (∀ q : Pt A, Algebra.FormallySmooth ℚ (IsLocalRing.ResidueField (Localization.AtPrime q.ker))) :=
  ⟨fun q => fact_polyIndNoeth_atPrime q.ker, fun q => fs_localization q.ker,
    fun q => (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.1
      (fe_residueField q.ker)).2⟩

/-- **Chart size of a Jouanolou ring over the Rees algebra of a component.** -/
theorem chartDim_jou_rees [IsNoetherianRing A] [Fact (HasPres A)] {I : Ideal A} (hI : I ≠ ⊥)
    {v₀ : ℕ → ℚ}
    (hmax : IsMaxInvPt I v₀)
    {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
    (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) (l₀ : List A) (hl₀ : I = lspan l₀) {dim : ℕ}
    (hA : ChartDim A dim) (en : ℕ → A) (hen : Function.Surjective en) {ℓ : ℕ}
    (h : Fin (ℓ + 1) → ReesAlg (compFil hI hmax h𝔭 d)) :
    ChartDim (Jou.J h) (dim + 1 + ℓ) :=
  (chartDim_rees hI hmax h𝔭 hd hw l₀ hl₀ hA en hen i4_of_smooth.1 i4_of_smooth.2.1
    i4_of_smooth.2.2).jou h

/-- **The torsor has chart size `k + 1 + ℓ`**, by certificates along `A → 𝓡 → U`. -/
theorem chartDim_U_cert [Constructive.Enum A] [Fact (HasPres A)] (S : PrincipalizationData A) {k : ℕ}
    (hA : ChartDim A k) (en : ℕ → A) (hen : Function.Surjective en) :
    ChartDim S.U (k + 1 + S.ℓ) := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A
  exact chartDim_jou_rees S.ne_bot S.hmax S.h𝔭c S.d_pos S.hw S.Igens S.hIgens hA en hen S.h

end BezoutCounterexample.Principalization
