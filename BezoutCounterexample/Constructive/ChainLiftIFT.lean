import Mathlib
import BezoutCounterexample.Constructive.ChainLiftPoly
import BezoutCounterexample.Constructive.Kantorovich
import BezoutCounterexample.Constructive.ChainLiftChart

/-!
# Quantitative inverse function theorem for polynomial systems (`bezout-positive.tex`, §2.2)

For a square system `F = (F₁, …, F_N)` of integer polynomials and a base point `x₀` with an
explicit two-sided inverse `M` of the Jacobian `J(x₀) = (∂ⱼFᵢ(x₀))` (in the application
`M = u · adj J(x₀)`, where `det J · u ≡ 1` is a polynomial identity on the chart), there is an
explicit radius `r` such that, in the box of radius `r` around `x₀`:

* every target `y` with `2 N μ |F(x₀) - y| ≤ r` is hit exactly (`sect`), and
* `|x - x'| ≤ 2 N μ |F x - F x'|` (`inj`),

where `|M i j| ≤ μ`. These are the fields `sect` and `inj` of `PushData`.

No derivative in the sense of analysis is used: `poly_taylor` is the algebraic Taylor estimate
`|P x - P x' - Σⱼ ∂ⱼP(x') (xⱼ - x'ⱼ)| ≤ K δ²` on boxes, proved by induction on `P` (formal partial
derivatives `MvPolynomial.pderiv`). The fixed point comes from `exists_fixedPoint_half`.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {N : ℕ}

lemma evalR_add (x : Fin N → ℝ) (p q : MvPolynomial (Fin N) ℤ) :
    evalR x (p + q) = evalR x p + evalR x q := eval₂_add _ _

lemma evalR_mul (x : Fin N → ℝ) (p q : MvPolynomial (Fin N) ℤ) :
    evalR x (p * q) = evalR x p * evalR x q := eval₂_mul _ _

lemma evalR_X (x : Fin N → ℝ) (i : Fin N) : evalR x (X i) = x i := eval₂_X _ _ _

lemma evalR_C (x : Fin N → ℝ) (a : ℤ) : evalR x (C a) = a := by
  rw [evalR, eval₂_C]; exact eq_intCast _ a

lemma sum_pderiv_X (x' Δ : Fin N → ℝ) (i : Fin N) :
    ∑ j, evalR x' (pderiv j (X i : MvPolynomial (Fin N) ℤ)) * Δ j = Δ i := by
  rw [Finset.sum_eq_single i]
  · rw [pderiv_X_self]; simp [evalR]
  · intro j _ hj
    rw [pderiv_X_of_ne (Ne.symm hj)]; simp [evalR]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Algebraic Taylor estimate** on boxes. -/
theorem poly_taylor (C : ℝ) (hC : 0 ≤ C) (P : MvPolynomial (Fin N) ℤ) :
    ∃ K, 0 ≤ K ∧ ∀ x x' δ, Bdd C x → Bdd C x' → Close δ x x' →
      |evalR x P - evalR x' P - ∑ j, evalR x' (pderiv j P) * (x j - x' j)| ≤ K * δ ^ 2 := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, le_rfl, fun x x' δ _ _ _ => ?_⟩
    have e : ∀ y : Fin N → ℝ, evalR y (MvPolynomial.C a) = (a : ℝ) := fun y => evalR_C y a
    have e0 : ∀ y : Fin N → ℝ, evalR y 0 = 0 := fun y => eval₂_zero _ _
    simp only [e, pderiv_C, e0, zero_mul, Finset.sum_const_zero, sub_self,
      sub_zero, abs_zero, le_refl]
  | add p q hp hq =>
    obtain ⟨Kp, hKp, hp⟩ := hp
    obtain ⟨Kq, hKq, hq⟩ := hq
    refine ⟨Kp + Kq, by positivity, fun x x' δ hx hx' hc => ?_⟩
    have e : evalR x (p + q) - evalR x' (p + q) -
        ∑ j, evalR x' (pderiv j (p + q)) * (x j - x' j) =
        (evalR x p - evalR x' p - ∑ j, evalR x' (pderiv j p) * (x j - x' j)) +
        (evalR x q - evalR x' q - ∑ j, evalR x' (pderiv j q) * (x j - x' j)) := by
      simp only [map_add, evalR_add, add_mul, Finset.sum_add_distrib]; ring
    rw [e, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hp x x' δ hx hx' hc) (hq x x' δ hx hx' hc))
  | mul_X p i hp =>
    obtain ⟨K, hK, hp⟩ := hp
    obtain ⟨M, L, hM, hL, -, hlip⟩ := poly_bdd_lip C hC p
    refine ⟨C * K + L, by positivity, fun x x' δ hx hx' hc => ?_⟩
    set Tp := evalR x p - evalR x' p - ∑ j, evalR x' (pderiv j p) * (x j - x' j)
    have e : evalR x (p * X i) - evalR x' (p * X i) -
        ∑ j, evalR x' (pderiv j (p * X i)) * (x j - x' j) =
        x' i * Tp + (evalR x p - evalR x' p) * (x i - x' i) := by
      have hs : ∑ j, evalR x' (pderiv j (p * X i)) * (x j - x' j) =
          x' i * ∑ j, evalR x' (pderiv j p) * (x j - x' j) + evalR x' p * (x i - x' i) := by
        simp only [pderiv_mul, evalR_add, evalR_mul, evalR_X, add_mul, Finset.sum_add_distrib]
        rw [← sum_pderiv_X x' (fun j => x j - x' j) i, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun j _ => by ring
        · exact Finset.sum_congr rfl fun j _ => by ring
      rw [hs, evalR_mul, evalR_mul, evalR_X, evalR_X]
      simp only [Tp]; ring
    rw [e]
    have h1 : |x' i * Tp| ≤ C * (K * δ ^ 2) := by
      rw [abs_mul]; exact mul_le_mul (hx' i) (hp x x' δ hx hx' hc) (abs_nonneg _) hC
    have hpl := hlip x x' δ hx hx' hc
    have h2 : |(evalR x p - evalR x' p) * (x i - x' i)| ≤ L * δ * δ := by
      rw [abs_mul]; exact mul_le_mul hpl (hc i) (abs_nonneg _) ((abs_nonneg _).trans hpl)
    calc |x' i * Tp + (evalR x p - evalR x' p) * (x i - x' i)|
        ≤ C * (K * δ ^ 2) + L * δ * δ := (abs_add_le _ _).trans (add_le_add h1 h2)
      _ = (C * K + L) * δ ^ 2 := by ring

/-- Uniform constants for a finite family (monotone properties). -/
theorem exists_uniform {ι : Type*} [DecidableEq ι] (Q : ι → ℝ → Prop)
    (hmono : ∀ i K K', Q i K → K ≤ K' → Q i K') (h : ∀ i, ∃ K, 0 ≤ K ∧ Q i K) :
    ∀ s : Finset ι, ∃ K, 0 ≤ K ∧ ∀ i ∈ s, Q i K := by
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s _ ih =>
    obtain ⟨K, hK, hs⟩ := ih
    obtain ⟨Ka, hKa, ha⟩ := h a
    refine ⟨K + Ka, by positivity, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hmono _ _ _ ha (by linarith)
    · exact hmono _ _ _ (hs i hi) (by linarith)

lemma abs_sum_le_card {f : Fin N → ℝ} {A : ℝ} (h : ∀ j, |f j| ≤ A) : |∑ j, f j| ≤ N * A := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => h j).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Values and Jacobian of a polynomial system at a real point. -/
noncomputable def Fval (F : Fin N → MvPolynomial (Fin N) ℤ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => evalR x (F i)

noncomputable def Jac (F : Fin N → MvPolynomial (Fin N) ℤ) (x : Fin N → ℝ) (i j : Fin N) : ℝ :=
  evalR x (pderiv j (F i))

/-- **Quantitative inverse function theorem** for a square integer-polynomial system with an
explicit two-sided inverse `M` of `J(x₀)`, `|M i j| ≤ μ`. -/
theorem poly_ift (F : Fin N → MvPolynomial (Fin N) ℤ) (C : ℝ) (hC : 0 ≤ C) (μ : ℝ)
    (hμ : 0 ≤ μ) :
    ∃ r, 0 < r ∧ r ≤ 1 ∧ ∀ (x₀ : Fin N → ℝ), Bdd C x₀ → ∀ (M : Fin N → Fin N → ℝ),
      (∀ i j, |M i j| ≤ μ) →
      (∀ i j, ∑ k, M i k * Jac F x₀ k j = if i = j then 1 else 0) →
      (∀ i j, ∑ k, Jac F x₀ i k * M k j = if i = j then 1 else 0) →
      (∀ y η, 0 ≤ η → Close η (Fval F x₀) y → 2 * (N * μ * η) ≤ r →
        ∃ x, Close r x x₀ ∧ Fval F x = y) ∧
      (∀ x x' e, 0 ≤ e → Close r x x₀ → Close r x' x₀ → Close e (Fval F x) (Fval F x') →
        Close (2 * (N * μ) * e) x x') := by
  -- uniform Taylor and Lipschitz constants on the box `C + 1`
  have hC1 : 0 ≤ C + 1 := by linarith
  obtain ⟨K, hK, hTay⟩ := exists_uniform
    (fun i K => ∀ x x' δ, Bdd (C + 1) x → Bdd (C + 1) x' → Close δ x x' →
      |evalR x (F i) - evalR x' (F i) - ∑ j, evalR x' (pderiv j (F i)) * (x j - x' j)| ≤ K * δ ^ 2)
    (fun i K K' h hKK' x x' δ hx hx' hc =>
      (h x x' δ hx hx' hc).trans (mul_le_mul_of_nonneg_right hKK' (sq_nonneg _)))
    (fun i => poly_taylor (C + 1) hC1 (F i)) Finset.univ
  obtain ⟨L, hL, hLip⟩ := exists_uniform
    (fun (ij : Fin N × Fin N) L => ∀ x x' δ, 0 ≤ δ → Bdd (C + 1) x → Bdd (C + 1) x' →
      Close δ x x' → |Jac F x ij.1 ij.2 - Jac F x' ij.1 ij.2| ≤ L * δ)
    (fun ij L L' h hLL' x x' δ hδ hx hx' hc =>
      (h x x' δ hδ hx hx' hc).trans (mul_le_mul_of_nonneg_right hLL' hδ))
    (fun ij => by
      obtain ⟨_, L, -, hL, -, hl⟩ := poly_bdd_lip (C + 1) hC1 (pderiv ij.2 (F ij.1))
      exact ⟨L, hL, fun x x' δ _ hx hx' hc => hl x x' δ hx hx' hc⟩) Finset.univ
  -- the radius
  set A := 2 * ((N : ℝ) * N * μ * L + 2 * N * μ * K)
  have hA : 0 ≤ A := by positivity
  obtain ⟨r, hr, hrA, hr1⟩ := exists_pos_mul_le₂ one_pos one_pos A 1
  rw [one_mul] at hr1
  set c := (N : ℝ) * N * μ * L * r + 2 * N * μ * K * r
  have hc : 2 * c ≤ 1 := by simp only [c, A] at hrA ⊢; linarith
  have hc0 : 0 ≤ c := by positivity
  refine ⟨r, hr, hr1, fun x₀ hx₀ M hM hML hMR => ?_⟩
  have hbox : ∀ x, Close r x x₀ → Bdd (C + 1) x := fun x hx =>
    (hx₀.of_close hx).mono (by linarith)
  -- the key estimate: `Φ x - Φ x'` for `Φ x = x - M (F x - y)`
  have key : ∀ x x' d, 0 ≤ d → d ≤ 2 * r → Close r x x₀ → Close r x' x₀ → Close d x x' → ∀ i,
      |(x i - x' i) - ∑ k, M i k * (Fval F x k - Fval F x' k)| ≤ c * d := by
    intro x x' d hd hd2 hx hx' hxx' i
    set Δ : Fin N → ℝ := fun j => x j - x' j
    set R : Fin N → ℝ := fun k => Fval F x k - Fval F x' k - ∑ j, Jac F x' k j * Δ j
    set E : Fin N → Fin N → ℝ := fun k j => Jac F x' k j - Jac F x₀ k j
    have hR : ∀ k, |R k| ≤ K * d ^ 2 := fun k =>
      hTay k (Finset.mem_univ k) x x' d (hbox x hx) (hbox x' hx') hxx'
    have hE : ∀ k j, |E k j| ≤ L * r := fun k j =>
      hLip (k, j) (Finset.mem_univ _) x' x₀ r hr.le (hbox x' hx') (hx₀.mono (by linarith)) hx'
    have h1 : ∑ k, M i k * (Fval F x k - Fval F x' k) =
        ∑ j, (∑ k, M i k * Jac F x' k j) * Δ j + ∑ k, M i k * R k := by
      have e1 : ∀ k, M i k * (Fval F x k - Fval F x' k) =
          M i k * (∑ j, Jac F x' k j * Δ j) + M i k * R k := fun k => by simp only [R]; ring
      rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_add_distrib]
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have h2 : ∑ j, (∑ k, M i k * Jac F x' k j) * Δ j =
        Δ i + ∑ j, (∑ k, M i k * E k j) * Δ j := by
      have e2 : ∀ j, (∑ k, M i k * Jac F x' k j) =
          (if i = j then 1 else 0) + ∑ k, M i k * E k j := fun j => by
        rw [← hML i j, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by simp only [E]; ring
      simp only [e2, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have e : (x i - x' i) - ∑ k, M i k * (Fval F x k - Fval F x' k) =
        -(∑ j, (∑ k, M i k * E k j) * Δ j) - ∑ k, M i k * R k := by
      rw [h1, h2]; simp only [Δ]; ring
    rw [e]
    have b1 : |∑ j, (∑ k, M i k * E k j) * Δ j| ≤ N * (N * (μ * (L * r)) * d) := by
      refine abs_sum_le_card fun j => ?_
      rw [abs_mul]
      refine mul_le_mul (abs_sum_le_card fun k => ?_) (hxx' j) (abs_nonneg _) (by positivity)
      rw [abs_mul]; exact mul_le_mul (hM i k) (hE k j) (abs_nonneg _) hμ
    have b2 : |∑ k, M i k * R k| ≤ N * (μ * (K * d ^ 2)) := by
      refine abs_sum_le_card fun k => ?_
      rw [abs_mul]; exact mul_le_mul (hM i k) (hR k) (abs_nonneg _) hμ
    have b3 : (N : ℝ) * (μ * (K * d ^ 2)) ≤ 2 * N * μ * K * r * d := by
      have : d ^ 2 ≤ 2 * r * d := by rw [sq]; exact mul_le_mul_of_nonneg_right hd2 hd
      have h0 : 0 ≤ (N : ℝ) * μ * K := by positivity
      have := mul_le_mul_of_nonneg_left this h0
      nlinarith
    calc |-(∑ j, (∑ k, M i k * E k j) * Δ j) - ∑ k, M i k * R k|
        ≤ |∑ j, (∑ k, M i k * E k j) * Δ j| + |∑ k, M i k * R k| := by
          rw [sub_eq_add_neg]; refine (abs_add_le _ _).trans ?_; rw [abs_neg, abs_neg]
      _ ≤ N * (N * (μ * (L * r)) * d) + 2 * N * μ * K * r * d := add_le_add b1 (b2.trans b3)
      _ = c * d := by simp only [c]; ring
  -- the map `Φ` and its two properties
  set Φ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) :=
    fun y x i => x i - ∑ k, M i k * (Fval F x k - y k)
  have hΦ : ∀ y x x' i, Φ y x i - Φ y x' i =
      (x i - x' i) - ∑ k, M i k * (Fval F x k - Fval F x' k) := fun y x x' i => by
    simp only [Φ]
    rw [show (x i - ∑ k, M i k * (Fval F x k - y k)) - (x' i - ∑ k, M i k * (Fval F x' k - y k)) =
      (x i - x' i) - (∑ k, M i k * (Fval F x k - y k) - ∑ k, M i k * (Fval F x' k - y k)) by ring,
      ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hball : ∀ x, x ∈ Metric.closedBall x₀ r ↔ Close r x x₀ := fun x => by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact ⟨fun h => close_of_norm_le h, fun h => norm_le_of_close hr.le h⟩
  have hdist : ∀ x x', Close r x x₀ → Close r x' x₀ →
      Close ‖x - x'‖ x x' ∧ 0 ≤ ‖x - x'‖ ∧ ‖x - x'‖ ≤ 2 * r := fun x x' hx hx' =>
    ⟨close_of_norm_le le_rfl, norm_nonneg _,
      by have := norm_le_of_close (by linarith) (hx.trans hx'.symm); linarith⟩
  refine ⟨fun y η hη hy hηr => ?_, fun x x' e he hx hx' hF => ?_⟩
  · have hcon : ∀ x ∈ Metric.closedBall x₀ r, ∀ x' ∈ Metric.closedBall x₀ r,
        2 * ‖Φ y x - Φ y x'‖ ≤ ‖x - x'‖ := by
      intro x hx x' hx'
      rw [hball] at hx hx'
      obtain ⟨hcl, hd0, hd2⟩ := hdist x x' hx hx'
      have h := norm_le_of_close (w := Φ y x) (w' := Φ y x') (mul_nonneg hc0 hd0) (fun i => by
        rw [hΦ]; exact key x x' _ hd0 hd2 hx hx' hcl i)
      have := mul_le_mul_of_nonneg_right hc hd0
      linarith
    have hmaps : ∀ x ∈ Metric.closedBall x₀ r, Φ y x ∈ Metric.closedBall x₀ r := by
      intro x hx
      rw [hball] at hx ⊢
      intro i
      have h1 := key x x₀ r hr.le (by linarith) hx (close_refl hr.le _) hx i
      rw [← hΦ y] at h1
      have h2 : |Φ y x₀ i - x₀ i| ≤ N * (μ * η) := by
        simp only [Φ, sub_sub_cancel_left, abs_neg]
        refine abs_sum_le_card fun k => ?_
        rw [abs_mul]; exact mul_le_mul (hM i k) (hy k) (abs_nonneg _) hμ
      have h3 : 2 * (c * r) ≤ r := by
        have := mul_le_mul_of_nonneg_right hc hr.le; linarith
      calc |Φ y x i - x₀ i| = |(Φ y x i - Φ y x₀ i) + (Φ y x₀ i - x₀ i)| := by ring_nf
        _ ≤ |Φ y x i - Φ y x₀ i| + |Φ y x₀ i - x₀ i| := abs_add_le _ _
        _ ≤ c * r + N * (μ * η) := add_le_add h1 h2
        _ ≤ r := by nlinarith
    obtain ⟨x, hx, hfix⟩ := exists_fixedPoint_half (Φ y) x₀ r hr.le hmaps hcon
    refine ⟨x, (hball x).1 hx, funext fun j => ?_⟩
    set v : Fin N → ℝ := fun k => Fval F x k - y k
    have hv : ∀ i, ∑ k, M i k * v k = 0 := fun i => by
      have := congrFun hfix i
      simp only [Φ] at this
      linarith
    have : v j = 0 := by
      have e : ∑ i, Jac F x₀ j i * ∑ k, M i k * v k = v j := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        have e3 : ∀ k, ∑ i, Jac F x₀ j i * (M i k * v k) = (if j = k then 1 else 0) * v k :=
          fun k => by
            rw [← hMR j k, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
        simp only [e3, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [← e]; simp only [hv, mul_zero, Finset.sum_const_zero]
    simp only [v] at this; linarith
  · obtain ⟨hcl, hd0, hd2⟩ := hdist x x' hx hx'
    set d := ‖x - x'‖
    have hcoord : ∀ i, |x i - x' i| ≤ c * d + N * (μ * e) := fun i => by
      have h1 := key x x' d hd0 hd2 hx hx' hcl i
      have h2 : |∑ k, M i k * (Fval F x k - Fval F x' k)| ≤ N * (μ * e) := by
        refine abs_sum_le_card fun k => ?_
        rw [abs_mul]; exact mul_le_mul (hM i k) (hF k) (abs_nonneg _) hμ
      calc |x i - x' i| = |((x i - x' i) - ∑ k, M i k * (Fval F x k - Fval F x' k)) +
            ∑ k, M i k * (Fval F x k - Fval F x' k)| := by ring_nf
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)
    have hd : d ≤ c * d + N * (μ * e) := by
      have := norm_le_of_close (w := x) (w' := x') (by positivity) hcoord
      exact this
    have hcd : 2 * (c * d) ≤ d := by
      have := mul_le_mul_of_nonneg_right hc hd0; linarith
    intro i
    have := (norm_le_pi_norm (x - x') i).trans (le_refl d)
    rw [Pi.sub_apply, Real.norm_eq_abs] at this
    nlinarith

/-! ## The inverse of the Jacobian from a determinant witness -/

/-- **Two-sided inverse with a bound**, from `det A · u = 1`: `M = u · adj A`. In the
application `A = J(x₀)` and `u` is the value of a polynomial witness of `det J · u ≡ 1` on the
chart, so `|u| ≤ U` is explicit. -/
theorem inverse_of_det (A : Matrix (Fin N) (Fin N) ℝ) (u : ℝ) (hu : A.det * u = 1) (B : ℝ)
    (hB1 : 1 ≤ B) (hB : ∀ i j, |A i j| ≤ B) :
    (∀ i j, ∑ k, (u • A.adjugate) i k * A k j = if i = j then 1 else 0) ∧
    (∀ i j, ∑ k, A i k * (u • A.adjugate) k j = if i = j then 1 else 0) ∧
    (∀ i j, |(u • A.adjugate) i j| ≤ |u| * ((N.factorial : ℝ) * B ^ N)) := by
  have hL : (u • A.adjugate) * A = 1 := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm u, hu, one_smul]
  have hR : A * (u • A.adjugate) = 1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm u, hu, one_smul]
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · have := congrFun (congrFun hL i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this; exact this
  · have := congrFun (congrFun hR i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this; exact this
  · rw [Matrix.smul_apply, smul_eq_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [Matrix.adjugate_apply]
    have hent : ∀ k l, AbsoluteValue.abs ((A.updateRow j (Pi.single i 1)) k l) ≤ B := by
      intro k l
      rw [AbsoluteValue.abs_apply, Matrix.updateRow_apply]
      split_ifs
      · by_cases hl : l = i
        · subst hl; simp only [Pi.single_eq_same, abs_one]; exact hB1
        · rw [Pi.single_eq_of_ne hl, abs_zero]; linarith
      · exact hB k l
    have := Matrix.det_le hent
    rw [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] at this
    exact this

end BezoutCounterexample.Constructive
