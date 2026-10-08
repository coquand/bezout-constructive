import Mathlib
import BezoutCounterexample.Constructive.ChainLift

/-!
# Chain lifting along a tower (`~/COLL/bezout-direct.tex`, Lemma 2.2 for chains)

A tower `B₀ → B₁ → ⋯ → B_r` of steps, each with `ChainLift Ptᵢ Ptᵢ₊₁ πᵢ` and `πᵢ` Lipschitz and
bounded on boxes, lifts chains from `B₀` to `B_r` along the composite projection
(`TowerLift.chainLift`). The composition is `ChainLift.comp`, which needs the projection of the
earlier steps Lipschitz on boxes (`LipMap.comp`, using `BddMap` of the later step).

* `ChainLift.id`: a step that leaves the ring unchanged (HM's divisorial stage, `B₁ = B`).
* `lipMap_castAdd`, `bddMap_castAdd`: the coordinate projection `(Y, …) ↦ Y` of a torsor step.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

variable {N N' N'' : ℕ}

/-- Maps sending boxes into boxes. -/
def BddMap (f : (Fin N' → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ C, ∃ C', ∀ w, Bdd C w → Bdd C' (f w)

lemma lipMap_id : LipMap (id : (Fin N → ℝ) → (Fin N → ℝ)) :=
  fun _ => ⟨1, zero_le_one, fun w w' δ _ _ h k => by rw [one_mul]; exact h k⟩

lemma bddMap_id : BddMap (id : (Fin N → ℝ) → (Fin N → ℝ)) :=
  fun C => ⟨C, fun _ h => h⟩

lemma LipMap.comp {f : (Fin N' → ℝ) → (Fin N → ℝ)} {g : (Fin N'' → ℝ) → (Fin N' → ℝ)}
    (hf : LipMap f) (hg : LipMap g) (hgb : BddMap g) : LipMap (f ∘ g) := by
  intro C
  obtain ⟨C', hC'⟩ := hgb C
  obtain ⟨L₁, hL₁, h₁⟩ := hg C
  obtain ⟨L₂, hL₂, h₂⟩ := hf C'
  refine ⟨L₂ * L₁, mul_nonneg hL₂ hL₁, fun w w' δ hw hw' h k => ?_⟩
  have := h₂ _ _ _ (hC' w hw) (hC' w' hw') (h₁ w w' δ hw hw' h) k
  rwa [← mul_assoc] at this

lemma BddMap.comp {f : (Fin N' → ℝ) → (Fin N → ℝ)} {g : (Fin N'' → ℝ) → (Fin N' → ℝ)}
    (hf : BddMap f) (hg : BddMap g) : BddMap (f ∘ g) := by
  intro C
  obtain ⟨C', hC'⟩ := hg C
  obtain ⟨C'', hC''⟩ := hf C'
  exact ⟨C'', fun w hw => hC'' _ (hC' w hw)⟩

/-- The projection `(Y, …) ↦ Y` is `1`-Lipschitz. -/
lemma lipMap_castAdd (M : ℕ) : LipMap (fun (x : Fin (N + M) → ℝ) (k : Fin N) => x (Fin.castAdd M k)) :=
  fun _ => ⟨1, zero_le_one, fun w w' δ _ _ h k => by rw [one_mul]; exact h _⟩

lemma bddMap_castAdd (M : ℕ) : BddMap (fun (x : Fin (N + M) → ℝ) (k : Fin N) => x (Fin.castAdd M k)) :=
  fun C => ⟨C, fun _ h k => h _⟩

/-- **A step leaving the ring unchanged** (HM's divisorial stage). -/
protected theorem ChainLift.id {Pt : (Fin N → ℝ) → Prop} : ChainLift Pt Pt id :=
  ChainLift.of_section _root_.id (fun _ h => ⟨h, rfl⟩) (fun C => ⟨C, fun _ h => h⟩) lipMap_id

/-- A tower of chain-lifting steps from `Pt`, with projections Lipschitz and bounded on boxes. -/
inductive TowerLift {N : ℕ} (Pt : (Fin N → ℝ) → Prop) :
    {N' : ℕ} → ((Fin N' → ℝ) → Prop) → ((Fin N' → ℝ) → (Fin N → ℝ)) → Prop
  | refl : TowerLift Pt Pt _root_.id
  | step {N' N'' : ℕ} {Pt' : (Fin N' → ℝ) → Prop} {Pt'' : (Fin N'' → ℝ) → Prop}
      {π : (Fin N' → ℝ) → (Fin N → ℝ)} {π' : (Fin N'' → ℝ) → (Fin N' → ℝ)} :
      TowerLift Pt Pt' π → ChainLift Pt' Pt'' π' → LipMap π' → BddMap π' →
      TowerLift Pt Pt'' (π ∘ π')

/-- **Chain lifting along a tower** (backwards composition, `ChainLift.comp`). -/
theorem TowerLift.chainLift {Pt : (Fin N → ℝ) → Prop} {Pt' : (Fin N' → ℝ) → Prop}
    {π : (Fin N' → ℝ) → (Fin N → ℝ)} (h : TowerLift Pt Pt' π) :
    ChainLift Pt Pt' π ∧ LipMap π ∧ BddMap π := by
  induction h with
  | refl => exact ⟨ChainLift.id, lipMap_id, bddMap_id⟩
  | step _ hc hl hb ih =>
    exact ⟨ih.1.comp hc ih.2.1, ih.2.1.comp hl hb, ih.2.2.comp hb⟩

/-- **Concatenating two towers.** -/
theorem TowerLift.trans {Pt : (Fin N → ℝ) → Prop} {Pt' : (Fin N' → ℝ) → Prop}
    {Pt'' : (Fin N'' → ℝ) → Prop} {π : (Fin N' → ℝ) → (Fin N → ℝ)}
    {π' : (Fin N'' → ℝ) → (Fin N' → ℝ)} (h : TowerLift Pt Pt' π) (h' : TowerLift Pt' Pt'' π') :
    TowerLift Pt Pt'' (π ∘ π') := by
  induction h' with
  | refl => exact h
  | step _ hc hl hb ih => exact ih.step hc hl hb

/-- Appending a torsor step whose projection is `(Y, …) ↦ Y`. -/
theorem TowerLift.proj {Pt : (Fin N → ℝ) → Prop} {Pt' : (Fin N' → ℝ) → Prop}
    {π : (Fin N' → ℝ) → (Fin N → ℝ)} {M : ℕ} {Pt'' : (Fin (N' + M) → ℝ) → Prop}
    (h : TowerLift Pt Pt' π) (hc : ChainLift Pt' Pt'' (fun x k => x (Fin.castAdd M k))) :
    TowerLift Pt Pt'' (π ∘ fun x k => x (Fin.castAdd M k)) :=
  h.step hc (lipMap_castAdd M) (bddMap_castAdd M)

end BezoutCounterexample.Constructive
