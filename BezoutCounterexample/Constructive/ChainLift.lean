import Mathlib
import BezoutCounterexample.Constructive.ChainLiftOff
import BezoutCounterexample.Constructive.ChainLiftPush

/-!
# Chain lifting for a step of the tower (`~/COLL/bezout-direct.tex`, Prop. 2.2)

`ChainLift Pt Pt' π`: for every box `C` there is a box `C'` such that for every `ε > 0` some
`δ > 0` works: every closed `δ`-chain of real points of `B` in the box `C` lifts to a closed
`ε`-chain of real points of `B'` in the box `C'`, with an index map `ι` (`IsReindex`) such that
the projection of the `j`-th new point is `ε`-close to the `ι j`-th old point. The box `C'` does
not depend on `ε`; this is what makes the backwards composition along the tower work
(`ChainLift.comp`).

* `ChainLift.of_section`: steps with a Lipschitz section (Laurent step `w = (z, c = 1, c' = 0)`;
  gcd extraction, divisorial and trivial steps, where `B' = B`).
* `ChainLift.torsor`: a torsor step, from the push-off (`PushData.push_off`, §2.3) followed by
  the explicit lift over `{ν ≥ ρ}` (`OffStep.lift_chain`, §2.1).
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

variable {N N' N'' : ℕ}

/-- The chain lifting property of a step `B → B'` with projection `π` on real points. -/
def ChainLift (Pt : (Fin N → ℝ) → Prop) (Pt' : (Fin N' → ℝ) → Prop)
    (π : (Fin N' → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ C, ∃ C', ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ m z, IsChain Pt C δ m z →
    ∃ m' w ι, IsChain Pt' C' ε m' w ∧ IsReindex m m' ι ∧ ∀ j ≤ m', Close ε (π (w j)) (z (ι j))

/-- Lipschitz on boxes, for maps between real points. -/
def LipMap (f : (Fin N' → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ C, ∃ L, 0 ≤ L ∧ ∀ w w' δ, Bdd C w → Bdd C w' → Close δ w w' → Close (L * δ) (f w) (f w')

lemma IsChain.mono {Pt : (Fin N → ℝ) → Prop} {C δ δ' : ℝ} {m : ℕ} {z : ℕ → Fin N → ℝ}
    (h : IsChain Pt C δ m z) (hδ : δ ≤ δ') : IsChain Pt C δ' m z :=
  ⟨h.closed, h.mem, h.bdd, fun i hi => (h.step i hi).mono hδ⟩

/-- **Composition** of chain lifts (backwards choice of the meshes). -/
theorem ChainLift.comp {Pt : (Fin N → ℝ) → Prop} {Pt' : (Fin N' → ℝ) → Prop}
    {Pt'' : (Fin N'' → ℝ) → Prop} {π : (Fin N' → ℝ) → (Fin N → ℝ)}
    {π' : (Fin N'' → ℝ) → (Fin N' → ℝ)} (h : ChainLift Pt Pt' π) (h' : ChainLift Pt' Pt'' π')
    (hπ : LipMap π) : ChainLift Pt Pt'' (π ∘ π') := by
  intro C
  obtain ⟨C₁, h₁⟩ := h C
  obtain ⟨C₂, h₂⟩ := h' C₁
  refine ⟨C₂, fun ε hε => ?_⟩
  obtain ⟨L, hL0, hL⟩ := hπ (C₁ + 1)
  -- the second lift: closeness `ε₂`
  obtain ⟨εh, hεh, hεh2⟩ := exists_pos_mul_le hε 2
  obtain ⟨ε₂, hε₂, hε₂L, hε₂1⟩ := exists_pos_mul_le₂ hεh one_pos L 1
  obtain ⟨ε₂', hε₂', hε₂'a, hε₂'b⟩ := exists_pos_mul_le₂ hε₂ hε 1 1
  rw [one_mul] at hε₂1 hε₂'a hε₂'b
  obtain ⟨δ₂, hδ₂, hlift₂⟩ := h₂ ε₂' hε₂'
  -- the first lift: closeness `ε₁ ≤ ε/2`, and mesh `ε₁ ≤ δ₂` for the second
  obtain ⟨ε₁, hε₁, hε₁a, hε₁b⟩ := exists_pos_mul_le₂ hεh hδ₂ 1 1
  rw [one_mul] at hε₁a hε₁b
  obtain ⟨δ₁, hδ₁, hlift₁⟩ := h₁ ε₁ hε₁
  refine ⟨δ₁, hδ₁, fun m z hz => ?_⟩
  obtain ⟨m₁, z₁, ι₁, hz₁, hι₁, hc₁⟩ := hlift₁ m z hz
  obtain ⟨m₂, z₂, ι₂, hz₂, hι₂, hc₂⟩ := hlift₂ m₁ z₁ (hz₁.mono hε₁b)
  refine ⟨m₂, z₂, ι₁ ∘ ι₂, hz₂.mono hε₂'b, hι₁.comp hι₂, fun j hj => ?_⟩
  have hi := hι₂.le j hj
  -- `π' (z₂ j)` is `ε₂'`-close to `z₁ (ι₂ j)`, so both lie in the box `C₁ + 1`
  have hb₁ : Bdd (C₁ + 1) (z₁ (ι₂ j)) := (hz₁.bdd _ hi).mono (by linarith)
  have hb₂ : Bdd (C₁ + 1) (π' (z₂ j)) :=
    ((hz₁.bdd _ hi).of_close (hc₂ j hj)).mono (by linarith)
  have h1 := hL _ _ _ hb₂ hb₁ (hc₂ j hj)
  have h2 := hc₁ (ι₂ j) hi
  have h3 : L * ε₂' ≤ εh := (mul_le_mul_of_nonneg_left hε₂'a hL0).trans hε₂L
  exact ((h1.trans h2).mono (by linarith) : Close ε _ _)

/-- **Steps with a Lipschitz section** (Laurent, gcd extraction, divisorial, trivial). -/
theorem ChainLift.of_section {Pt : (Fin N → ℝ) → Prop} {Pt' : (Fin N' → ℝ) → Prop}
    {π : (Fin N' → ℝ) → (Fin N → ℝ)} (s : (Fin N → ℝ) → (Fin N' → ℝ))
    (hs : ∀ z, Pt z → Pt' (s z) ∧ π (s z) = z)
    (hsb : ∀ C, ∃ C', ∀ z, Bdd C z → Bdd C' (s z)) (hsl : LipMap s) :
    ChainLift Pt Pt' π := by
  intro C
  obtain ⟨C', hC'⟩ := hsb C
  refine ⟨C', fun ε hε => ?_⟩
  obtain ⟨L, hL0, hL⟩ := hsl C
  obtain ⟨δ, hδ, hδL⟩ := exists_pos_mul_le hε L
  refine ⟨δ, hδ, fun m z hz => ⟨m, s ∘ z, id, ⟨by simp [hz.closed], fun i hi => (hs _ (hz.mem i hi)).1,
    fun i hi => hC' _ (hz.bdd i hi), fun i hi => ?_⟩, IsReindex.id m, fun j hj => ?_⟩⟩
  · exact (hL _ _ _ (hz.bdd i hi.le) (hz.bdd _ hi) (hz.step i hi)).mono hδL
  · simp only [Function.comp, id, (hs _ (hz.mem j hj)).2]
    exact close_refl hε.le _

/-- **The torsor step** (Prop. 2.2): push off the centre, then lift explicitly. -/
theorem ChainLift.torsor {ι : Type*} [Fintype ι] (T : OffStep N N' ι)
    (PD : ∀ C, PushData N T.Pt T.nu C) : ChainLift T.Pt T.Pt' T.π := by
  intro C
  obtain ⟨C', hC'⟩ := T.lift_chain (C + 1)
  refine ⟨C', fun ε hε => ?_⟩
  obtain ⟨ρ, hρ, hpush⟩ := (PD C).push_off ε hε
  obtain ⟨δ₁, hδ₁, hlift⟩ := hC' ρ hρ ε hε
  obtain ⟨δ, hδ, hpush'⟩ := hpush δ₁ hδ₁
  refine ⟨δ, hδ, fun m z hz => ?_⟩
  obtain ⟨m', w, ι', hw, hν, hι, hcl⟩ := hpush' m z hz
  obtain ⟨u, hu, hπ⟩ := hlift m' w hw hν
  exact ⟨m', u, ι', hu, hι, fun j hj => by rw [hπ j hj]; exact hcl j hj⟩

end BezoutCounterexample.Constructive
