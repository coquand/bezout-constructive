import BezoutCounterexample.Principalization.ChartDim
import BezoutCounterexample.Principalization.Points
import BezoutCounterexample.Constructive.Groebner

/-!
# A chart of size `n` near every explicit point (`hchartn`)

From `ChartDim A n`: at an explicit point `p` of `A`, some square piece `P_k` of the certificate has
`h_k(p) ≠ 0`, and its chart on `D(h_k)` (`SquarePiece.chart`) moves to `A` along `QB G ≃ A`.

The piece is found by the zero test at `p` (`Pt.mem_ker_dec`, `fin_forall_or_exists`). If every
`h_k` vanishes at `p`, the cover `C ≡ Σ u_k h_k` puts the positive integer `C` in `p.ker`.

* `Chart.awayEquiv`: transport of a chart on `D(x)` along a ring isomorphism.
* **`ChartDim.exists_chart_away`**: the `hchartn` input of `LocusComp.exists_chartCoverPtL`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

/-- **Transport of a chart on `D(x)`** along a ring isomorphism `e`, to `D(e x)`. -/
def Chart.awayEquiv {B A : Type} [CommRing B] [Algebra ℚ B] [CommRing A] [Algebra ℚ A]
    {n : ℕ} (e : B ≃+* A) (x : B) (c : Chart (Localization.Away x) n) :
    Chart (Localization.Away (e x)) n :=
  c.ofRingEquiv (IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers x)
    (T := Submonoid.powers (e x)) _ _ e (Submonoid.map_powers (e : B →* A) x))

namespace ChartDim

variable {A : Type} [CommRing A] [Algebra ℚ A] {n : ℕ}

/-- **A chart of size `n` on some `D(f)` around every explicit point.** -/
theorem exists_chart_away (hn : ChartDim A n) (p : Pt A) :
    ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) n) := by
  obtain ⟨m, G, ⟨e⟩, ⟨hG⟩⟩ := hn
  let hk : Fin hG.K → A := fun k => e (SquarePiece.mkQ G (hG.P k).h)
  rcases fin_forall_or_exists (A := fun k => hk k ∈ p.ker) (B := fun k => hk k ∉ p.ker)
      (fun k => p.mem_ker_dec (hk k)) with hall | ⟨k, hkp⟩
  · exfalso
    have hcov := SmoothCert.ψ_eq_zero hG.cover
    rw [map_sub, map_natCast, map_sum, sub_eq_zero] at hcov
    have hC : e ((hG.C : ℕ) : SmoothCert.QB G) ∈ p.ker := by
      rw [hcov, map_sum]
      exact Ideal.sum_mem _ fun k _ => by
        rw [map_mul, map_mul]; exact Ideal.mul_mem_left _ _ (hall k)
    rw [map_natCast, Pt.mem_ker, map_natCast, ← map_natCast (algebraMap ℚ p.L), map_eq_zero,
      Nat.cast_eq_zero] at hC
    exact hG.hC.ne' hC
  · exact ⟨hk k, hkp, ⟨Chart.awayEquiv e _ (hG.P k).chart⟩⟩

end ChartDim

end BezoutCounterexample.Principalization
