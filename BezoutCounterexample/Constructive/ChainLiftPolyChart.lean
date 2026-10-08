import Mathlib
import BezoutCounterexample.Constructive.ChainLiftIFT

/-!
# Polynomial charts give the fields `sect`, `inj`, `lipφ` of `PushData` (§2.2)

A *polynomial chart* of an explicitly presented ring `B = ℤ[X₁…X_N]/(G) ⊗ ℚ` on `D(h)`:
a square system `F` of `N = m + n` integer polynomials, the first `m` equations (they vanish on
real points, and on `{|h| ≥ θ_lo}` they generate `(G)`: `gen`), the last `n` the chart coordinates
`φ`, and a witness that the Jacobian determinant is a unit on `{|h| ≥ θ_lo}` with `|u| ≤ U`
(`det`). The field `det` is pointwise on real points, so a congruence suffices: from
`det J · U' ∈ hᵉ + (G)` (invertibility modulo the chart ideal, not a polynomial identity) one gets
`det J(x) · u = 1` with `u = U'(x) / h(x)ᵉ` at every real point with `|h(x)| ≥ θ_lo`, and
`|u| ≤ sup|U'| / θ_loᵉ` on each box. Valid base points: `θ ≤ |h|`.

`PolyChart.fields`: on every box there are uniform constants `R, K, S, Lφ` for which the
quantitative inverse function theorem (`poly_ift`, with `M = u · adj J`, `inverse_of_det`) gives
exactly the fields `sect`, `inj`, `lipφ` of `PushData`.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

open MvPolynomial

/-- Real points of the presentation `G`. -/
def PtG {N : ℕ} (G : List (MvPolynomial (Fin N) ℤ)) (x : Fin N → ℝ) : Prop :=
  ∀ g ∈ G, evalR x g = 0

/-- A polynomial chart with `m` equations and `n` chart coordinates. -/
structure PolyChart (m n : ℕ) where
  G : List (MvPolynomial (Fin (m + n)) ℤ)
  F : Fin (m + n) → MvPolynomial (Fin (m + n)) ℤ
  h : MvPolynomial (Fin (m + n)) ℤ
  hn : 0 < n
  θ : ℝ
  θlo : ℝ
  hθlo : 0 < θlo
  hθ : θlo < θ
  eqs : ∀ x, PtG G x → ∀ i : Fin m, evalR x (F (Fin.castAdd n i)) = 0
  gen : ∀ x, θlo ≤ |evalR x h| → (∀ i : Fin m, evalR x (F (Fin.castAdd n i)) = 0) → PtG G x
  det : ∀ C, ∃ U, 0 ≤ U ∧ ∀ x, Bdd C x → PtG G x → θlo ≤ |evalR x h| →
    ∃ u, Matrix.det (Jac F x : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * u = 1 ∧ |u| ≤ U

namespace PolyChart

variable {m n : ℕ} (P : PolyChart m n)

/-- The chart coordinates. -/
noncomputable def φ (x : Fin (m + n) → ℝ) : Fin n → ℝ := fun j => evalR x (P.F (Fin.natAdd m j))

/-- Valid base points. -/
def valid (x : Fin (m + n) → ℝ) : Prop := P.θ ≤ |evalR x P.h|

include P in
lemma nonneg_of_close {e : ℝ} {c c' : Fin n → ℝ} (h : Close e c c') : 0 ≤ e :=
  (abs_nonneg _).trans (h ⟨0, P.hn⟩)

/-- Closeness of chart coordinates is closeness of `F` at real points. -/
lemma close_Fval {x x' : Fin (m + n) → ℝ} (hx : PtG P.G x) (hx' : PtG P.G x') {e : ℝ}
    (h : Close e (P.φ x) (P.φ x')) : Close e (Fval P.F x) (Fval P.F x') := by
  have he := P.nonneg_of_close h
  intro k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [Fval, P.eqs x hx i, P.eqs x' hx' i, sub_self, abs_zero]; exact he
  · exact h j

/-- **The fields `sect`, `inj`, `lipφ` of `PushData`**, with uniform constants on the box `C`. -/
theorem fields (C : ℝ) (hC : 0 ≤ C) : ∃ R K S Lφ, 0 < R ∧ 0 ≤ K ∧ 0 < S ∧ 0 ≤ Lφ ∧
    (∀ z, PtG P.G z → Bdd C z → P.valid z → ∀ c e, e ≤ R → Close e c (P.φ z) →
      ∃ z', PtG P.G z' ∧ P.φ z' = c ∧ Close (K * e) z' z) ∧
    (∀ z, PtG P.G z → Bdd C z → P.valid z → ∀ z' z'', PtG P.G z' → PtG P.G z'' →
      Close S z' z → Close S z'' z → ∀ e, Close e (P.φ z') (P.φ z'') → Close (K * e) z' z'') ∧
    (∀ z, PtG P.G z → Bdd C z → P.valid z → ∀ z' z'' e, Close S z' z → Close S z'' z →
      Close e z' z'' → Close (Lφ * e) (P.φ z') (P.φ z'')) := by
  set N := m + n
  have hC1 : 0 ≤ C + 1 := by linarith
  -- bound `B` for the Jacobian entries on the box `C`
  obtain ⟨B₀, hB₀, hJ⟩ := exists_uniform
    (fun (ij : Fin N × Fin N) B => ∀ x, Bdd C x → |Jac P.F x ij.1 ij.2| ≤ B)
    (fun ij B B' h hBB' x hx => (h x hx).trans hBB')
    (fun ij => by
      obtain ⟨M, -, hM, -, hb, -⟩ := poly_bdd_lip C hC (pderiv ij.2 (P.F ij.1))
      exact ⟨M, hM, hb⟩) Finset.univ
  set B := B₀ + 1
  have hB1 : 1 ≤ B := by simp only [B]; linarith
  obtain ⟨U, hU0, hdet⟩ := P.det C
  set μ := U * ((N.factorial : ℝ) * B ^ N)
  have hμ : 0 ≤ μ := mul_nonneg hU0 (by positivity)
  obtain ⟨r, hr, hr1, hift⟩ := poly_ift P.F C hC μ hμ
  -- Lipschitz constants of `h` and of the chart coordinates on the box `C + 1`
  obtain ⟨-, Lh, -, hLh, -, hlh⟩ := poly_bdd_lip (C + 1) hC1 P.h
  obtain ⟨Lφ, hLφ, hlφ⟩ := exists_uniform
    (fun (j : Fin n) L => ∀ x x' δ, 0 ≤ δ → Bdd (C + 1) x → Bdd (C + 1) x' → Close δ x x' →
      |P.φ x j - P.φ x' j| ≤ L * δ)
    (fun j L L' h hLL' x x' δ hδ hx hx' hc =>
      (h x x' δ hδ hx hx' hc).trans (mul_le_mul_of_nonneg_right hLL' hδ))
    (fun j => by
      obtain ⟨-, L, -, hL, -, hl⟩ := poly_bdd_lip (C + 1) hC1 (P.F (Fin.natAdd m j))
      exact ⟨L, hL, fun x x' δ _ hx hx' hc => hl x x' δ hx hx' hc⟩) Finset.univ
  set K := 2 * ((N : ℝ) * μ)
  have hK : 0 ≤ K := by positivity
  -- the radius `R` of target chart coordinates
  obtain ⟨R, hR, hRl⟩ := exists_pos_mul_le_list [(K, r), (Lh * K, P.θ - P.θlo)]
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨hK, hr⟩
      · exact ⟨by positivity, sub_pos.2 P.hθ⟩)
  have hKR : K * R ≤ r := hRl (K, r) (by simp)
  have hLKR : Lh * K * R ≤ P.θ - P.θlo := hRl (Lh * K, P.θ - P.θlo) (by simp)
  -- the inverse of the Jacobian at a valid base point
  have hinv : ∀ z, PtG P.G z → Bdd C z → P.valid z → ∃ M : Fin N → Fin N → ℝ,
      (∀ i j, |M i j| ≤ μ) ∧ (∀ i j, ∑ k, M i k * Jac P.F z k j = if i = j then 1 else 0) ∧
      (∀ i j, ∑ k, Jac P.F z i k * M k j = if i = j then 1 else 0) := by
    intro z hz hzC hv
    obtain ⟨u, hu, hU⟩ := hdet z hzC hz (le_trans P.hθ.le hv)
    obtain ⟨h1, h2, h3⟩ := inverse_of_det (Jac P.F z : Matrix (Fin N) (Fin N) ℝ) u hu B hB1
      (fun i j => (hJ (i, j) (Finset.mem_univ _) z hzC).trans (by simp only [B]; linarith))
    exact ⟨u • Matrix.adjugate (Jac P.F z : Matrix (Fin N) (Fin N) ℝ), fun i j => (h3 i j).trans
      (mul_le_mul_of_nonneg_right hU (by positivity)), h1, h2⟩
  have hbox : ∀ z x : Fin N → ℝ, Bdd C z → Close r x z → Bdd (C + 1) x := fun z x hz hx =>
    (hz.of_close hx).mono (by linarith)
  refine ⟨R, K, r, Lφ, hR, hK, hr, hLφ, ?_, ?_, ?_⟩
  · -- `sect`
    intro z hz hzC hv c e heR hc
    have he := P.nonneg_of_close hc
    obtain ⟨M, hM, hML, hMR⟩ := hinv z hz hzC hv
    obtain ⟨hsect, hinj⟩ := hift z hzC M hM hML hMR
    set y : Fin N → ℝ := Fin.append (fun _ : Fin m => (0 : ℝ)) c
    have hy : Close e (Fval P.F z) y := by
      intro k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · simp only [y, Fin.append_left, Fval, P.eqs z hz i, sub_self, abs_zero]; exact he
      · simp only [y, Fin.append_right]; rw [abs_sub_comm]; exact hc j
    obtain ⟨x, hxz, hFx⟩ := hsect y e he hy (by
      have := mul_le_mul_of_nonneg_left heR hK
      simp only [K] at this hKR ⊢; nlinarith)
    have hKe : Close (K * e) x z := by
      have := hinj x z e he hxz (close_refl hr.le z) (by rw [hFx]; exact hy.symm)
      exact this
    -- `x` is valid enough for `gen`
    have hhx : P.θlo ≤ |evalR x P.h| := by
      have h1 := hlh x z (K * e) (hbox z x hzC hxz) (hzC.mono (by linarith)) hKe
      have h2 : Lh * (K * e) ≤ P.θ - P.θlo := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left heR hK) hLh
        linarith
      have h3 := abs_sub_abs_le_abs_sub (evalR z P.h) (evalR x P.h)
      rw [abs_sub_comm] at h1
      simp only [valid] at hv
      linarith
    have hFeq : ∀ i : Fin m, evalR x (P.F (Fin.castAdd n i)) = 0 := fun i => by
      have := congrFun hFx (Fin.castAdd n i)
      simpa [Fval, y] using this
    refine ⟨x, P.gen x hhx hFeq, funext fun j => ?_, hKe⟩
    have := congrFun hFx (Fin.natAdd m j)
    simpa [Fval, y, φ] using this
  · -- `inj`
    intro z hz hzC hv z' z'' hz' hz'' h1 h2 e hc
    obtain ⟨M, hM, hML, hMR⟩ := hinv z hz hzC hv
    obtain ⟨-, hinj⟩ := hift z hzC M hM hML hMR
    exact hinj z' z'' e (P.nonneg_of_close hc) h1 h2 (P.close_Fval hz' hz'' hc)
  · -- `lipφ`
    intro z hz hzC hv z' z'' e h1 h2 hc j
    have he : 0 ≤ e := (abs_nonneg _).trans (hc ⟨m, by have := P.hn; omega⟩)
    exact hlφ j (Finset.mem_univ j) z' z'' e he (hbox z z' hzC h1) (hbox z z'' hzC h2) hc

end PolyChart

end BezoutCounterexample.Constructive
