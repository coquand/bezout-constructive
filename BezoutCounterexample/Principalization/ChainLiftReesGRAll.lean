import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesRowsCongr

/-!
# One global presentation containing the rows of all opens (Task B, Rees layer S6, §13 step 1)

The rows of every open are appended to the kernel of the Rees map in one call of
`exists_reesKer_ext`:
* `G` renamed into `(Y, s, y)` (so that the `F_eq` rows of every `A`-piece lie in `(GR)`);
* the Laurent rows of `ε₀` (a multiple of a power of the element `i ∈ 𝔭` of the cover);
* per chart `k`: the weighted rows `rowsW (headF ãₖ) γₖ wₖ P̃ₖ βₖ Qₖ`, and for each head `q` the
  Laurent rows of `γₖ ãₖ_q` with `Pt = s^{w−1} P̃ₖ_q` (`laurPt_head`).

`exists_GR_all`: such a `GR`, with its kernel property and the memberships.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

set_option linter.unusedSectionVars false

variable {A : Type} [CommRing A] [Algebra ℚ A] {m kc l r : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (gZ : Fin r → MvPolynomial (Fin (m + (kc + l))) ℤ) (δ : Fin r → ℕ)

/-- The Laurent point of the head `q` of a chart. -/
def headPt (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) (w : Fin kc → ℕ)
    (q : Fin kc) : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ :=
  X gS ^ (w q - 1) * P q

/-- **All rows**, in one list. -/
def allRows {K : ℕ} (d : ℕ) (ε₀ : MvPolynomial (Fin (m + (kc + l))) ℤ)
    (Pt₀ : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (ã : Fin K → Fin kc → MvPolynomial (Fin (m + (kc + l))) ℤ)
    (γ β : Fin K → MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin K → Fin kc → ℕ)
    (P : Fin K → Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (Q : Fin K → Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ) :
    List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) :=
  G.map (rename gY) ++ rowsL gZ δ (fun _ => 0) d ε₀ Pt₀ ++
    (List.finRange K).flatMap fun k =>
      rowsW (headF (ã k)) (γ k) (w k) (P k) (β k) (Q k) ++
        (List.finRange kc).flatMap fun q =>
          rowsL gZ δ (fun _ => 0) d (γ k * ã k q) (headPt (P k) (w k) q)

/-- **A global presentation of the Rees algebra containing all rows.** -/
theorem exists_GR_all {K : ℕ} {d : ℕ} (hδ : ∀ j, δ j ≤ d)
    (ε₀ : MvPolynomial (Fin (m + (kc + l))) ℤ) (Pt₀ : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hPt₀ : aeval (evG G e (reesYL G e gZ δ)) Pt₀ = LaurentPolynomial.C (toAZ G e ε₀) * T 1)
    (ã : Fin K → Fin kc → MvPolynomial (Fin (m + (kc + l))) ℤ)
    (γ β : Fin K → MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin K → Fin kc → ℕ)
    (hw0 : ∀ k q, 0 < w k q)
    (P : Fin K → Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (Q : Fin K → Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)
    (hP : ∀ k i, aeval (evG G e (reesYL G e gZ δ)) (P k i) =
      LaurentPolynomial.C (toAZ G e (γ k * headF (ã k) (Fin.natAdd m (Fin.castAdd l i)))) * T (w k i))
    (hy : ∀ k j, LaurentPolynomial.C (toAZ G e (β k)) * reesYL G e gZ δ j =
      aeval (evW G e (headF (ã k)) (γ k) (w k)) (Q k j)) :
    ∃ GR : List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ),
      (∀ h, aeval (reesVec G e gZ δ) h = 0 ↔ h ∈ lspan (GR.map toQZ)) ∧
      (∀ g ∈ G, rename gY g ∈ GR) ∧
      (∀ x ∈ rowsL gZ δ (fun _ => 0) d ε₀ Pt₀, x ∈ GR) ∧
      (∀ k, ∀ x ∈ rowsW (headF (ã k)) (γ k) (w k) (P k) (β k) (Q k), x ∈ GR) ∧
      (∀ k q, ∀ x ∈ rowsL gZ δ (fun _ => 0) d (γ k * ã k q) (headPt (P k) (w k) q), x ∈ GR) := by
  set Xs := allRows G gZ δ d ε₀ Pt₀ ã γ β w P Q with hXs
  have hvan : ∀ x ∈ Xs, aeval (evG G e (reesYL G e gZ δ)) x = 0 := by
    intro x hx
    simp only [hXs, allRows, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
      List.mem_map] at hx
    rcases hx with (⟨g, hg, rfl⟩ | hx) | ⟨k, hx | ⟨q, hx⟩⟩
    · rw [aeval_evG_gY, toAZ_eq_zero_of_mem G e (Ideal.subset_span hg), map_zero]
    · exact rowsL_vanish G e gZ δ _ (fun _ => Ideal.zero_mem _) hδ ε₀ Pt₀ hPt₀ x hx
    · exact rowsW_vanish G e (reesYL G e gZ δ) (headF (ã k)) (γ k) (w k)
        (fun i => by rw [headF_eq]; exact Ideal.zero_mem _) (P k) (hP k) (β k) (Q k) (hy k) x hx
    · refine rowsL_vanish G e gZ δ _ (fun _ => Ideal.zero_mem _) hδ _ _ ?_ x hx
      exact laurPt_head G e _ _ _ (hw0 k q) (by rw [hP k q, headF_head])
  obtain ⟨GR, hsub, hGR⟩ := exists_reesKer_ext G e gZ δ Xs fun x hx => by
    rw [← evG_reesYL G e gZ δ, aeval_int_cast]
    exact hvan x hx
  have hmem : ∀ x, x ∈ Xs → x ∈ GR := hsub
  simp only [hXs, allRows, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_map] at hmem
  refine ⟨GR, hGR, fun g hg => hmem _ (Or.inl (Or.inl ⟨g, hg, rfl⟩)),
    fun x hx => hmem _ (Or.inl (Or.inr hx)), fun k x hx => hmem _ (Or.inr ⟨k, Or.inl hx⟩),
    fun k q x hx => hmem _ (Or.inr ⟨k, Or.inr ⟨q, hx⟩⟩)⟩

end BezoutCounterexample.Principalization
