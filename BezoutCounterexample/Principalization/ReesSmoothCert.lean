import BezoutCounterexample.Rees
import BezoutCounterexample.Principalization.ChainLiftPresCertPt
import BezoutCounterexample.Principalization.ChainLiftChartDimRees
import BezoutCounterexample.Principalization.ReesI4

/-!
# Smoothness of the Rees algebra by certificates (leaf, part (a))

`rees_smooth` (ReesGlobal) glues the formal smoothness of the localized Rees algebras at every
maximal ideal (`reesLoc_formallySmooth`: classical `IsInv.exists_run`, `cRF_eq`, `compF_map`,
`compF_antitone`, …) along basic opens found by Zorn (`span_eq_top_of_forall_isMaximal`). With
certificates the cover is explicit:

* `SmoothCert.smooth`: a certified presented ring is smooth: its pieces `D(h_k)` are smooth
  (`SquarePiece.smooth_loc`) and the `h_k` generate the unit ideal (`C ≡ Σ u_k h_k`, `C ≠ 0`), so
  `smooth_of_span_cover` glues them;
* `ChartDim.smooth`: the same for `ChartDim A n`;
* `rees_smooth_cert`: twin of `rees_smooth`, from `chartDim_rees` (charts of the Rees algebra);
* `ReesData.smooth_𝓡_cert`: the instance `Algebra.Smooth ℚ S.𝓡` (Rees) from `S.hN`.

The generators `l` of `I` are an argument (as in `DropBridge.drop_of_pt`). Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

/-- **A certified presented ring is smooth over `ℚ`.** -/
theorem _root_.BezoutCounterexample.Constructive.SmoothCert.smooth {m n : ℕ}
    {G : List (MvPolynomial (Fin (m + n)) ℤ)} (hG : SmoothCert m n G) :
    Algebra.Smooth ℚ (SmoothCert.QB G) := by
  refine smooth_of_span_cover (Set.range fun k => SquarePiece.mkQ G (hG.P k).h) ?_ ?_
  · have hcov := SmoothCert.ψ_eq_zero hG.cover
    rw [map_sub, map_natCast, map_sum, sub_eq_zero] at hcov
    refine Ideal.eq_top_of_isUnit_mem _ (x := ((hG.C : ℕ) : SmoothCert.QB G)) ?_ ?_
    · rw [hcov]
      refine Ideal.sum_mem _ fun k _ => ?_
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self (f := fun k => SquarePiece.mkQ G (hG.P k).h) k))
    · rw [← map_natCast (algebraMap ℚ (SmoothCert.QB G))]
      exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hG.hC.ne')).map _
  · rintro _ ⟨k, rfl⟩
    exact (hG.P k).smooth_loc

/-- **A ring of chart size `n` is smooth over `ℚ`.** -/
theorem ChartDim.smooth {A : Type} [CommRing A] [Algebra ℚ A] {n : ℕ} (hn : ChartDim A n) :
    Algebra.Smooth ℚ A := by
  obtain ⟨m, G, ⟨e⟩, ⟨hG⟩⟩ := hn
  have := hG.smooth
  exact Algebra.Smooth.of_equiv e.toRatAlgEquiv

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hI hmax h𝔭 hd hw in
/-- **The extended Rees algebra is smooth over `ℚ`, by certificates** (twin of `rees_smooth`):
`ChartDim A dim → ChartDim R (dim + 1)` (`chartDim_rees`), then `ChartDim.smooth`. -/
theorem rees_smooth_cert [Fact (HasPres A)] (hN : ∃ k, ChartDim A k) (l : List A)
    (hl : I = lspan l) : Algebra.Smooth ℚ (ReesAlg (compFil hI hmax h𝔭 d)) := by
  obtain ⟨dim, hA⟩ := hN
  obtain ⟨E⟩ := HasPres.nonempty_enum (Fact.out : HasPres A)
  exact (chartDim_rees hI hmax h𝔭 hd hw l hl hA E.en E.hen
    (fun q => fact_polyIndNoeth_atPrime q.ker) hA.formallySmooth_pt
    (fun q => Pt.formallySmooth_residueField q)).smooth

end BezoutCounterexample.Principalization

namespace BezoutCounterexample.ReesData

open Principalization Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  (S : ReesData A)

/-- **`𝓡` is smooth over `ℚ`, by certificates** (twin of the `Algebra.Smooth ℚ S.𝓡` instance). -/
theorem smooth_𝓡_cert [Fact (HasPres A)] (l : List A) (hl : S.I = lspan l) :
    Algebra.Smooth ℚ S.𝓡 :=
  rees_smooth_cert S.ne_bot S.hmax S.h𝔭c S.d_pos S.hw S.hN l hl

end BezoutCounterexample.ReesData
