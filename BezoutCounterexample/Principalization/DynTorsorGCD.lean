import BezoutCounterexample.Principalization.DynTorsorBridge
import BezoutCounterexample.Constructive.DynJouGCD

/-!
# The torsor has gcds up to an escape (`docs/d5-plan.md`, step 4)

`torsor_gcdQ`: the D5 form of `torsor_gcd`, generic over the filtration `Φ` and the row `y` (so it
applies to the torsor of a radical `(P)` once its filtration is explicit). Inputs:

* gcds of `A` up to `Q`, a zero test, `PolyIndNoeth A`;
* the row `c = y` in `A[T^±]` coprime up to `Q` (`gcd1_dyn`), `c₀ ≠ 0`;
* `s` prime up to `Q` in `U` (`torsor_s_dyn`, with `Q` already containing `RadSplit P`);
* the decisions of `U`, `J_{A[T^±]}(c)` and the generic Jouanolou ring (from presentations).

Proof: `U[1/s] = J_{A[T^±]}(c)` has gcds up to `Q` (`hasGcdQ_jou`); then decide whether `s` is a
unit of `U`. If so, `U ≅ U[1/s]` (`IsLocalization.atUnits`); otherwise Nagata at `s` up to `Q`
(`hasGcd_of_away_dyn`), with the valuations from the bar.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open LaurentPolynomial Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] (Φ : WFil A)
  (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤) {n : ℕ} (y : Fin (n + 1) → ReesAlg Φ)

set_option maxHeartbeats 1000000 in
/-- **The torsor has gcds, up to `Q`.** -/
theorem torsor_gcdQ {Q : Prop} (hG : HasGcdQ Q A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0)
    (hNA : PolyIndNoeth A) (hy0 : y 0 ≠ 0)
    (hc0 : (algebraMap (ReesAlg Φ) A[T;T⁻¹] ∘ y) 0 ≠ 0)
    (hrel : ∀ e : A[T;T⁻¹], (∀ i, e ∣ (algebraMap (ReesAlg Φ) A[T;T⁻¹] ∘ y) i) → IsUnit e ∨ Q)
    (hzJ : ∀ z : Jou.J (algebraMap (ReesAlg Φ) A[T;T⁻¹] ∘ y), z = 0 ∨ z ≠ 0)
    (hdvd : ∀ z : genJ (algebraMap (ReesAlg Φ) A[T;T⁻¹] ∘ y),
      genπJ (algebraMap (ReesAlg Φ) A[T;T⁻¹] ∘ y) ∣ z ∨
        ¬ genπJ (algebraMap (ReesAlg Φ) A[T;T⁻¹] ∘ y) ∣ z)
    (hdvdπ : ∀ x, genπ (algebraMap (ReesAlg Φ) A[T;T⁻¹] ∘ y) ∣ x ∨
      ¬ genπ (algebraMap (ReesAlg Φ) A[T;T⁻¹] ∘ y) ∣ x)
    (hsQ : ∀ u v : Jou.J y, algebraMap _ (Jou.J y) (reesS Φ hneg) ∣ u * v →
      algebraMap _ (Jou.J y) (reesS Φ hneg) ∣ u ∨ algebraMap _ (Jou.J y) (reesS Φ hneg) ∣ v ∨ Q)
    (hzU : ∀ x : Jou.J y, x = 0 ∨ x ≠ 0) (hdU : DvdDec (Jou.J y)) (hIN : IndNoeth (Jou.J y)) :
    HasGcdQ Q (Jou.J y) := by
  set s := reesS Φ hneg
  set c : Fin (n + 1) → A[T;T⁻¹] := algebraMap (ReesAlg Φ) A[T;T⁻¹] ∘ y
  have : IsDomain (Jou.J y) := Jou.isDomain (l := 0) hy0
  have : IsLocalization.Away s A[T;T⁻¹] := isLocalization_away_s _ _
  let : Algebra (Jou.J y) (Jou.J c) := (Jou.map (algebraMap (ReesAlg Φ) A[T;T⁻¹]) y).toAlgebra
  have hloc : IsLocalization ((Submonoid.powers s).map (algebraMap (ReesAlg Φ) (Jou.J y))) (Jou.J c) :=
    Jou.isLocalization_map y (Submonoid.powers s)
  have : IsLocalization.Away (algebraMap (ReesAlg Φ) (Jou.J y) s) (Jou.J c) := by
    rw [Submonoid.map_powers] at hloc; exact hloc
  -- the base `A[T^±] = A[X][1/X]`
  have hGB : HasGcdQ Q A[T;T⁻¹] := hasGcdQ_laurent hG hz
  have hzX := polynomial_eq_zero_or hz
  have hzB : ∀ b : A[T;T⁻¹], b = 0 ∨ b ≠ 0 :=
    localization_eq_zero_or hzX (Submonoid.powers (Polynomial.X : Polynomial A))
      (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero) _
  have hAX : PolyIndNoeth (Polynomial A) := hNA.of_finiteType
  have hNB : PolyIndNoeth A[T;T⁻¹] :=
    hAX.of_isLocalization (Submonoid.powers (Polynomial.X : Polynomial A))
  have hJ : HasGcdQ Q (Jou.J c) := hasGcdQ_jou c hGB hzB hNB hc0 hrel hzJ hdvd hdvdπ
  -- `s ≠ 0` in `U`
  have hs0 : algebraMap (ReesAlg Φ) (Jou.J y) s ≠ 0 := by
    intro h
    have : s = 0 := Jou.algebraMap_injective (l := 0) hy0 (by rw [h, map_zero])
    have := congrArg (fun p : (ReesAlg Φ) => (p : A[T;T⁻¹]).coeff (-1)) this
    simp [s, reesS_coe] at this
  rcases hdU (algebraMap (ReesAlg Φ) (Jou.J y) s) 1 with hu | hnu
  · -- `s` is a unit: `U ≅ U[1/s]`
    have hunit : Submonoid.powers (algebraMap (ReesAlg Φ) (Jou.J y) s) ≤ IsUnit.submonoid (Jou.J y) := by
      rintro _ ⟨k, rfl⟩
      exact (isUnit_of_dvd_one hu).pow k
    exact hasGcdQ_of_ringEquiv
      (IsLocalization.atUnits (Jou.J y) _ (S := Jou.J c) hunit).toRingEquiv hJ
  · -- Nagata at `s`, up to `Q`
    have hnu' : ¬ IsUnit (algebraMap (ReesAlg Φ) (Jou.J y) s) := fun h => hnu h.dvd
    exact hasGcd_of_away_dyn hs0 hsQ (Jou.J c) hzU
      (fun a ha => hIN.exists_val hnu' hdU ha) hJ

end BezoutCounterexample.Principalization
