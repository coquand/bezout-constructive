import Mathlib
import BezoutCounterexample.Constructive.ChainLiftBasic

/-!
# Polynomials are bounded and Lipschitz on boxes

The analytic hypotheses of `OffStep` (`g_bdd`, `g_lip`, `Q_lip`), `ChainLift.comp` (`LipMap`) and
`no_moebius_lift` (`hbd`, `hlip`) are instances of `poly_bdd_lip`: an integer polynomial,
evaluated at real points, is bounded and Lipschitz on every box, with explicit constants
(induction on the polynomial). Integer coefficients avoid `Rat.cast` into `ℝ`; a presentation
over `ℚ` is cleared of denominators first.
-/

namespace BezoutCounterexample.Constructive

variable {N : ℕ}

/-- Evaluation of an integer polynomial at a real point. -/
noncomputable def evalR (w : Fin N → ℝ) (P : MvPolynomial (Fin N) ℤ) : ℝ :=
  MvPolynomial.eval₂ (Int.castRingHom ℝ) w P

/-- **Bounds and Lipschitz constants of polynomials on boxes.** -/
theorem poly_bdd_lip (C : ℝ) (hC : 0 ≤ C) (P : MvPolynomial (Fin N) ℤ) :
    ∃ M L, 0 ≤ M ∧ 0 ≤ L ∧ (∀ w, Bdd C w → |evalR w P| ≤ M) ∧ LipR C L (fun w => evalR w P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨|(a : ℝ)|, 0, abs_nonneg _, le_rfl, fun w _ => ?_, fun w w' δ _ _ _ => ?_⟩
    · show |(MvPolynomial.eval₂Hom (Int.castRingHom ℝ) w) (a : MvPolynomial (Fin N) ℤ)| ≤ _
      rw [map_intCast]
    · simp only [evalR, MvPolynomial.eval₂_C, sub_self, abs_zero, zero_mul, le_refl]
  | add p q hp hq =>
    obtain ⟨Mp, Lp, hMp, hLp, hbp, hlp⟩ := hp
    obtain ⟨Mq, Lq, hMq, hLq, hbq, hlq⟩ := hq
    refine ⟨Mp + Mq, Lp + Lq, by positivity, by positivity, fun w hw => ?_,
      fun w w' δ hw hw' hc => ?_⟩
    · simp only [evalR, MvPolynomial.eval₂_add] at *
      exact (abs_add_le _ _).trans (add_le_add (hbp w hw) (hbq w hw))
    · simp only [evalR, MvPolynomial.eval₂_add] at *
      have e : MvPolynomial.eval₂ (Int.castRingHom ℝ) w p + MvPolynomial.eval₂ (Int.castRingHom ℝ) w q -
          (MvPolynomial.eval₂ (Int.castRingHom ℝ) w' p + MvPolynomial.eval₂ (Int.castRingHom ℝ) w' q) =
          (MvPolynomial.eval₂ (Int.castRingHom ℝ) w p - MvPolynomial.eval₂ (Int.castRingHom ℝ) w' p) +
          (MvPolynomial.eval₂ (Int.castRingHom ℝ) w q - MvPolynomial.eval₂ (Int.castRingHom ℝ) w' q) := by
        ring
      rw [e, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (hlp w w' δ hw hw' hc) (hlq w w' δ hw hw' hc))
  | mul_X p i hp =>
    obtain ⟨Mp, Lp, hMp, hLp, hbp, hlp⟩ := hp
    refine ⟨Mp * C, Lp * C + Mp, by positivity, by positivity, fun w hw => ?_,
      fun w w' δ hw hw' hc => ?_⟩
    · simp only [evalR, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] at *
      rw [abs_mul]
      exact mul_le_mul (hbp w hw) (hw i) (abs_nonneg _) hMp
    · simp only [evalR, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] at *
      have h := abs_mul_sub_mul_le (MvPolynomial.eval₂ (Int.castRingHom ℝ) w' p) (w' i)
        (MvPolynomial.eval₂ (Int.castRingHom ℝ) w p) (w i)
      refine h.trans ?_
      have h1 := hlp w w' δ hw hw' hc
      have h2 := hc i
      have h3 := hbp w' hw'
      calc |MvPolynomial.eval₂ (Int.castRingHom ℝ) w p - MvPolynomial.eval₂ (Int.castRingHom ℝ) w' p| *
            |w i| + |MvPolynomial.eval₂ (Int.castRingHom ℝ) w' p| * |w i - w' i|
          ≤ (Lp * δ) * C + Mp * δ :=
            add_le_add (mul_le_mul h1 (hw i) (abs_nonneg _) ((abs_nonneg _).trans h1))
              (mul_le_mul h3 h2 (abs_nonneg _) hMp)
      _ = (Lp * C + Mp) * δ := by ring

end BezoutCounterexample.Constructive
