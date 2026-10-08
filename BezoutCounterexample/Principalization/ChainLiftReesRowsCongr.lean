import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesAsm
import BezoutCounterexample.Principalization.ChainLiftReesOpenPt

/-!
# Rows depend only on the heads (Task B, Rees layer S6, §13 step 1)

The rows of an open (`rowsW`, `rowsL`) involve the `A`-piece `S` through its `F_eq` rows (which lie
in `(G)`, hence in `(GR)` once `G` is renamed into `GR`) and, for the weighted opens, its heads. So
one row set per chart serves every `A`-piece with the same heads: it is computed for
`headF ã` (heads `ã`, everything else `0`).

* `headF`, `headF_head`, `headF_eq`;
* `evW_congr`: `evW` depends only on the heads;
* `rowsW_mem_of_heads`, `rowsL_mem_of_eq`: membership in `(GR)` transported between pieces;
* `laurPt_head`: the Laurent preimage `s^{w−1} P̃_q` of `C(γ ã_q) T`;
* `finset_exists_or_forall`: a decided property is decided on a finset.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

set_option linter.unusedSectionVars false

/-- A decided property is decided on a finset (no `toList`). -/
lemma finset_exists_or_forall {α : Type*} [DecidableEq α] {P : α → Prop} (hP : ∀ x, P x ∨ ¬ P x)
    (s : Finset α) : (∃ x ∈ s, P x) ∨ ∀ x ∈ s, ¬ P x := by
  induction s using Finset.induction_on with
  | empty => exact Or.inr fun _ h => absurd h (Finset.notMem_empty _)
  | insert a s _ ih =>
    rcases hP a with ha | ha
    · exact Or.inl ⟨a, Finset.mem_insert_self _ _, ha⟩
    · rcases ih with ⟨x, hx, hPx⟩ | h
      · exact Or.inl ⟨x, Finset.mem_insert_of_mem hx, hPx⟩
      · exact Or.inr fun x hx => (Finset.mem_insert.1 hx).elim (fun h' => h' ▸ ha) (h x)

variable {A : Type} [CommRing A] [Algebra ℚ A] {m kc l r : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (gZ : Fin r → MvPolynomial (Fin (m + (kc + l))) ℤ) (δ : Fin r → ℕ)

/-- The coordinate family with heads `ã` and all other entries `0`. -/
def headF (ã : Fin kc → MvPolynomial (Fin (m + (kc + l))) ℤ) :
    Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ :=
  Fin.addCases (fun _ => 0) (Fin.addCases ã fun _ => 0)

@[simp] lemma headF_head (ã : Fin kc → MvPolynomial (Fin (m + (kc + l))) ℤ) (i : Fin kc) :
    headF ã (Fin.natAdd m (Fin.castAdd l i)) = ã i := by
  simp [headF]

@[simp] lemma headF_eq (ã : Fin kc → MvPolynomial (Fin (m + (kc + l))) ℤ) (i : Fin m) :
    headF ã (Fin.castAdd (kc + l) i) = 0 := by
  simp [headF]

/-- `evW` depends only on the heads. -/
lemma evW_congr {F F' : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ}
    (hh : ∀ i, F' (Fin.natAdd m (Fin.castAdd l i)) = F (Fin.natAdd m (Fin.castAdd l i)))
    (γ : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ) :
    evW G e F' γ w = evW G e F γ w := by
  unfold evW
  simp_rw [hh]

variable {GR : List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)}

lemma rename_gY_mem_of_mem (hGGR : ∀ g ∈ G, rename gY g ∈ GR)
    {p : MvPolynomial (Fin (m + (kc + l))) ℤ} (hp : p ∈ lspan G) : rename gY p ∈ lspan GR := by
  have h1 := rename_mem_lspan (gY (r := r)) hp
  refine (Ideal.span_le.2 ?_ : lspan (G.map (rename gY)) ≤ lspan GR) h1
  intro x hx
  simp only [Set.mem_ofPred_eq, List.mem_map] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  exact Ideal.subset_span (hGGR g hg)

/-- **Weighted rows transported between pieces with the same heads.** -/
lemma rowsW_mem_of_heads (hGGR : ∀ g ∈ G, rename gY g ∈ GR)
    {F F' : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ}
    (hF' : ∀ i : Fin m, F' (Fin.castAdd _ i) ∈ lspan G)
    (hh : ∀ i, F' (Fin.natAdd m (Fin.castAdd l i)) = F (Fin.natAdd m (Fin.castAdd l i)))
    (γ : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ)
    (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (β : MvPolynomial (Fin (m + (kc + l))) ℤ)
    (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)
    (hW : ∀ x ∈ rowsW F γ w P β Q, x ∈ GR) :
    ∀ x ∈ rowsW F' γ w P β Q, x ∈ lspan GR := by
  intro x hx
  simp only [rowsW, List.mem_append, List.mem_ofFn] at hx
  rcases hx with (⟨i, rfl⟩ | ⟨q, rfl⟩) | ⟨j, rfl⟩
  · exact rename_gY_mem_of_mem G hGGR (hF' i)
  · refine Ideal.subset_span (hW _ ?_)
    simp only [rowsW, List.mem_append, List.mem_ofFn]
    exact Or.inl (Or.inr ⟨q, by rw [hh]⟩)
  · refine Ideal.subset_span (hW _ ?_)
    simp only [rowsW, List.mem_append, List.mem_ofFn]
    exact Or.inr ⟨j, rfl⟩

/-- **Laurent rows transported between pieces** (only `F_eq` changes). -/
lemma rowsL_mem_of_eq (hGGR : ∀ g ∈ G, rename gY g ∈ GR)
    {F F' : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ}
    (hF' : ∀ i : Fin m, F' (Fin.castAdd _ i) ∈ lspan G) (d : ℕ)
    (εL : MvPolynomial (Fin (m + (kc + l))) ℤ) (Pt : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hL : ∀ x ∈ rowsL gZ δ F d εL Pt, x ∈ GR) :
    ∀ x ∈ rowsL gZ δ F' d εL Pt, x ∈ lspan GR := by
  intro x hx
  simp only [rowsL, List.mem_append, List.mem_ofFn, List.mem_singleton] at hx
  rcases hx with (⟨i, rfl⟩ | rfl) | ⟨j, rfl⟩
  · exact rename_gY_mem_of_mem G hGGR (hF' i)
  · refine Ideal.subset_span (hL _ ?_)
    simp [rowsL]
  · refine Ideal.subset_span (hL _ ?_)
    simp only [rowsL, List.mem_append, List.mem_ofFn, List.mem_singleton]
    exact Or.inr ⟨j, rfl⟩

/-- **The Laurent preimage of a head**: `s^{w−1} P̃` maps to `C(γ ã) T` when `P̃ ↦ C(γ ã) T^w`, `w ≥ 1`. -/
lemma laurPt_head (Ly : Fin r → A[T;T⁻¹]) (εL : MvPolynomial (Fin (m + (kc + l))) ℤ)
    (P : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) {w : ℕ} (hw : 0 < w)
    (hP : aeval (evG G e Ly) P = LaurentPolynomial.C (toAZ G e εL) * T w) :
    aeval (evG G e Ly) (X gS ^ (w - 1) * P) = LaurentPolynomial.C (toAZ G e εL) * T 1 := by
  rw [map_mul, map_pow, aeval_X, evG_gS, hP, T_pow, mul_left_comm, ← T_add]
  congr 2
  push_cast [Nat.cast_sub hw]
  ring

end BezoutCounterexample.Principalization
