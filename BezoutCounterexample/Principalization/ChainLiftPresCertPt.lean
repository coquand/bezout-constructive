import Mathlib
import BezoutCounterexample.Constructive.ChainLiftPresCert
import BezoutCounterexample.Principalization.ChainLiftReesPtCase

/-!
# `FormallySmooth ℚ A_q` at the points of a certified ring (hR4b, PresentationCert)

* `SquarePiece.formallySmooth_atPrime`: at a prime `𝔭` of `ℚ[Y]/(G)` with `h ∉ 𝔭`, the local ring
  is a localization of `D(h)`, smooth over `ℚ` (`SquarePiece.smooth_loc`), so it is formally smooth
  (`FormallySmooth.of_isLocalization`, `comp`).
* **`SmoothCert.formallySmooth_pt`**: at a point `q` of `A ≅ ℚ[Y]/(G)`, the zero test of the pieces'
  `h_k` at `q` (the cover `C ≡ Σ u_k h_k`, `C ≠ 0`) gives a piece with `h_k ∉ q.ker`.
* **`ChartDim.formallySmooth_pt`**: the same from `ChartDim A n`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}

/-- **Formal smoothness at a prime off `V(h)`.** -/
theorem _root_.BezoutCounterexample.Constructive.SquarePiece.formallySmooth_atPrime
    (S : SquarePiece m n G) (𝔭 : Ideal (SmoothCert.QB G)) [𝔭.IsPrime] (h : SquarePiece.mkQ G S.h ∉ 𝔭) :
    Algebra.FormallySmooth ℚ (Localization.AtPrime 𝔭) := by
  have hle : Submonoid.powers (SquarePiece.mkQ G S.h) ≤ 𝔭.primeCompl := Submonoid.powers_le.2 h
  let _ : Algebra S.Loc (Localization.AtPrime 𝔭) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  have : IsScalarTower (SmoothCert.QB G) S.Loc (Localization.AtPrime 𝔭) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have := IsLocalization.isLocalization_of_submonoid_le S.Loc (Localization.AtPrime 𝔭) _ _ hle
  have : Algebra.FormallySmooth S.Loc (Localization.AtPrime 𝔭) :=
    Algebra.FormallySmooth.of_isLocalization (𝔭.primeCompl.map (algebraMap _ S.Loc))
  have := S.smooth_loc
  have : IsScalarTower ℚ S.Loc (Localization.AtPrime 𝔭) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ (Localization.AtPrime 𝔭))
        ((algebraMap S.Loc (Localization.AtPrime 𝔭)).comp (algebraMap ℚ S.Loc))) r
  exact Algebra.FormallySmooth.comp ℚ S.Loc _

variable {A : Type} [CommRing A] [Algebra ℚ A]

/-- **Formal smoothness at the points of a certified ring.** -/
theorem _root_.BezoutCounterexample.Constructive.SmoothCert.formallySmooth_pt
    (hG : SmoothCert m n G) (e : SmoothCert.QB G ≃+* A) (q : Pt A) : Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker) := by
  have := algebraRat.charZero q.L
  -- the zero test: some piece has `h_k(q) ≠ 0`
  have hcov := SmoothCert.ψ_eq_zero hG.cover
  rw [map_sub, map_natCast, map_sum, sub_eq_zero] at hcov
  have h1 := congrArg (fun x => q.z (e x)) hcov
  simp only [map_natCast, map_sum, map_mul] at h1
  have hne : ∑ k, q.z (e (SmoothCert.ψ G (hG.u k))) * q.z (e (SmoothCert.ψ G (hG.P k).h)) ≠ 0 := by
    rw [← h1]; exact Nat.cast_ne_zero.2 hG.hC.ne'
  obtain ⟨k, -, hk⟩ := exists_ne_of_sum_ne q.dec Finset.univ _ hne
  have hk' : q.z (e (SquarePiece.mkQ G (hG.P k).h)) ≠ 0 := fun h0 => hk (by
    change _ * q.z (e (SquarePiece.mkQ G (hG.P k).h)) = 0
    rw [h0, mul_zero])
  -- the piece at the prime `q.ker.comap e`
  have := Ideal.comap_isPrime (e : SmoothCert.QB G →+* A) q.ker
  have := (hG.P k).formallySmooth_atPrime (q.ker.comap (e : SmoothCert.QB G →+* A))
    fun hm => hk' ((q.mem_ker).1 hm)
  exact Algebra.FormallySmooth.of_equiv (ChartDim.locEquiv e q.ker).toRatAlgEquiv

/-- **Formal smoothness at the points of a ring of chart size `n`.** -/
theorem ChartDim.formallySmooth_pt (hn : ChartDim A n) (q : Pt A) :
    Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker) := by
  obtain ⟨m, G, ⟨e⟩, ⟨hG⟩⟩ := hn
  exact hG.formallySmooth_pt e q

end BezoutCounterexample.Principalization
