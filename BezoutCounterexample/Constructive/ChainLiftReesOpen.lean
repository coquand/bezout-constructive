import Mathlib
import BezoutCounterexample.Constructive.ChainLiftReesModel

/-!
# The weighted-chart open in the global presentation (Task B, Rees layer S6b)

Packaging of `exists_reesChart` for a global presentation `GR` of the Rees algebra in its natural
layout `(Y, s, y)` (`Fin ((m + (kc + l)) + (1 + r))`, as produced by `exists_reesPres`), where `Y`
are the variables of the `A`-piece `F`. Given the head preimages `P q` (`u'_q ↦ P q`):

* `reesφ` (global → model: `Y ↦ Y`, `s ↦ s`, `y ↦ y`) and `reesψ` (model → global: `Y ↦ Y`,
  `s ↦ s`, `u' ↦ P`, `y ↦ y`); `reesψφ`: `ψ ∘ φ = id` on the global variables (`hround` exactly);
* `aeval_reesψ_sysEq`: the `ψ`-images of the model equations are the rows `F_eq`,
  `γ x̃_q − s^{w_q} P_q`, `β yⱼ − Qⱼ(s, P, Y)`;
* `exists_reesChart_open`: chart data and conormal injectivity of `GR` (renamed along any
  `ε : Fin ((m + (kc + l)) + (1 + r)) ≃ Fin ((m + r) + ((1 + kc) + l))`) from (a) the three row
  families in `(GR)` (over `ℤ`: append them with `exists_reesKer_ext`), (b) L3 for `GR` (`hφ`) and for
  the head coordinates (`hu`). The coordinates `s` and `x̃_rest` need nothing.
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {m kc l r : ℕ}

/-- `aeval (X ∘ f) = rename f`. -/
lemma aeval_X_comp {σ τ : Type*} (f : σ → τ) (p : MvPolynomial σ ℤ) :
    aeval (X ∘ f : σ → MvPolynomial τ ℤ) p = rename f p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p v hp => rw [map_mul, map_mul, hp, aeval_X, rename_X]; rfl

/-- Renaming after `aeval`. -/
lemma aeval_rename_comp {σ τ τ' : Type*} (ε : τ → τ') (ψ : σ → MvPolynomial τ ℤ)
    (h : MvPolynomial σ ℤ) : aeval (fun i => rename ε (ψ i)) h = rename ε (aeval ψ h) := by
  show _ = ((rename ε).comp (aeval ψ)) h
  rw [comp_aeval]

/-! ### Global variables -/

/-- `Y`. -/
def gY (v : Fin (m + (kc + l))) : Fin ((m + (kc + l)) + (1 + r)) := Fin.castAdd (1 + r) v
/-- `s`. -/
def gS : Fin ((m + (kc + l)) + (1 + r)) := Fin.natAdd (m + (kc + l)) (Fin.castAdd r 0)
/-- `y`. -/
def gYr (j : Fin r) : Fin ((m + (kc + l)) + (1 + r)) := Fin.natAdd (m + (kc + l)) (Fin.natAdd 1 j)

section Maps

variable (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)

/-- `ψ` on the variables `W = (s, u', Y)`. -/
def reesψW : Fin ((1 + kc) + (m + (kc + l))) → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ :=
  Fin.addCases (Fin.addCases (fun _ => X (gS (l := l) (r := r))) P) (fun v => X (gY v))

/-- `ψ` in block layout. -/
def reesψB : Fin (((1 + kc) + (m + (kc + l))) + r) →
    MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ :=
  Fin.addCases (reesψW P) (fun j => X (gYr j))

/-- **`ψ` (model → global)**: `Y ↦ Y`, `s ↦ s`, `u' ↦ P`, `y ↦ y`. -/
def reesψ (i : Fin (((m + kc) + r) + ((1 + kc) + l))) : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ :=
  reesψB P (reesPerm i)

/-- **`φ` (global → model)**: `Y ↦ Y`, `s ↦ s`, `y ↦ y`. -/
def reesφ : Fin ((m + (kc + l)) + (1 + r)) → MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ :=
  Fin.addCases (fun v => X (varY v)) (Fin.addCases (fun _ => X varS) (fun j => X (varYr j)))

lemma aeval_reesψ_rename_perm (p : MvPolynomial (Fin (((1 + kc) + (m + (kc + l))) + r)) ℤ) :
    aeval (reesψ P) (rename reesPerm.symm p) = aeval (reesψB P) p := by
  rw [aeval_rename]
  have : reesψ P ∘ reesPerm.symm = reesψB P := by funext v; simp [reesψ]
  rw [this]

lemma aeval_reesψ_varY (f : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    aeval (reesψ (r := r) P) (rename varY f) = rename gY f := by
  rw [show (rename varY f : MvPolynomial _ ℤ) = rename reesPerm.symm (rename (ιY (r := r)) f) by
    rw [rename_rename]; rfl, aeval_reesψ_rename_perm, aeval_rename]
  have : reesψB P ∘ ιY (r := r) = X ∘ gY := by funext v; simp [reesψB, reesψW, ιY]
  rw [this]; exact aeval_X_comp _ _

lemma aeval_reesψ_varW (q : MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ) :
    aeval (reesψ (r := r) P) (rename varW q) = aeval (reesψW P) q := by
  rw [show (rename varW q : MvPolynomial _ ℤ) = rename reesPerm.symm (rename (Fin.castAdd r) q) by
    rw [rename_rename]; rfl, aeval_reesψ_rename_perm, aeval_rename]
  have : reesψB P ∘ Fin.castAdd r = reesψW P := by funext v; simp [reesψB]
  rw [this]

lemma reesψ_varS : reesψ (m := m) (l := l) (r := r) P varS = X gS := by
  simp [reesψ, varS_eq, reesψB, reesψW]

lemma reesψ_varU (q : Fin kc) : reesψ (m := m) (l := l) (r := r) P (varU q) = P q := by
  simp [reesψ, varU_eq, reesψB, reesψW]

lemma reesψ_varYr (j : Fin r) : reesψ (m := m) (kc := kc) (l := l) P (varYr j) = X (gYr j) := by
  simp [reesψ, varYr_eq, reesψB]

lemma reesψ_varY (v : Fin (m + (kc + l))) : reesψ (r := r) P (varY v) = X (gY v) := by
  simp [reesψ, varY, ιY, reesψB, reesψW]

lemma reesφ_Y (v : Fin (m + (kc + l))) : reesφ (r := r) (gY v) = X (varY v) := by
  simp [reesφ, gY]

lemma reesφ_S : reesφ (m := m) (kc := kc) (l := l) (r := r) gS = X varS := by
  simp [reesφ, gS]

lemma reesφ_y (j : Fin r) : reesφ (m := m) (kc := kc) (l := l) (gYr j) = X (varYr j) := by
  simp [reesφ, gYr]

lemma varW_Y (v : Fin (m + (kc + l))) : varW (r := r) (Fin.natAdd (1 + kc) v) = varY v := rfl

lemma varW_s (o : Fin 1) :
    varW (m := m) (l := l) (r := r) (Fin.castAdd _ (Fin.castAdd kc o)) = varS := by
  rw [varW_su, Subsingleton.elim o 0]; rfl

lemma varW_u (i : Fin kc) :
    varW (m := m) (l := l) (r := r) (Fin.castAdd _ (Fin.natAdd 1 i)) = varU i := by
  rw [varW_su]; rfl

/-- **`ψ ∘ φ = id`** on the global variables. -/
lemma reesψφ (v : Fin ((m + (kc + l)) + (1 + r))) : aeval (reesψ P) (reesφ v) = X v := by
  refine Fin.addCases (fun v => ?_) (fun v => Fin.addCases (fun a => ?_) (fun j => ?_) v) v
  · simp only [reesφ, Fin.addCases_left, aeval_X]; rw [reesψ_varY]; rfl
  · simp only [reesφ, Fin.addCases_right, Fin.addCases_left, aeval_X]
    rw [reesψ_varS, Subsingleton.elim a 0]; rfl
  · simp only [reesφ, Fin.addCases_right, aeval_X]; rw [reesψ_varYr]; rfl

lemma aeval_reesφ_gY (f : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    aeval (reesφ (r := r)) (rename gY f) = rename varY f := by
  rw [aeval_rename]
  have : (reesφ (m := m) (kc := kc) (l := l) (r := r) ∘ gY) =
      X ∘ varY (m := m) (kc := kc) (l := l) (r := r) := by
    funext v; simp [reesφ, gY]
  rw [this]; exact aeval_X_comp _ _

end Maps

/-! ### The equations under `ψ` -/

variable (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (γ β : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ)
  (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)
  (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)

/-- **The `ψ`-images of the model equations.** -/
lemma aeval_reesψ_sysEq (h : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ)
    (hh : h ∈ sysEq (reesSys F γ β w Q)) :
    (∃ i : Fin m, aeval (reesψ P) h = rename gY (F (Fin.castAdd _ i))) ∨
    (∃ q : Fin kc, aeval (reesψ P) h =
      rename gY (γ * F (Fin.natAdd m (Fin.castAdd l q))) - X gS ^ w q * P q) ∨
    (∃ j : Fin r, aeval (reesψ P) h =
      rename gY β * X (gYr j) - aeval (reesψW P) (Q j)) := by
  simp only [sysEq, List.mem_ofFn] at hh
  obtain ⟨i, rfl⟩ := hh
  refine Fin.addCases ?_ ?_ i
  · intro t
    refine Fin.addCases ?_ ?_ t
    · intro i
      left; refine ⟨i, ?_⟩
      rw [reesSys_eq, aeval_reesψ_varY]
    · intro q
      right; left; refine ⟨q, ?_⟩
      rw [reesSys_head, map_sub, aeval_reesψ_varY]
      simp only [map_mul, map_pow, aeval_X, reesψ_varS, reesψ_varU]
  · intro j
    right; right; refine ⟨j, ?_⟩
    rw [reesSys_y, map_sub, map_mul, aeval_X, aeval_reesψ_varY, reesψ_varYr, aeval_reesψ_varW]
  /-
    rw [reesSys_eq, aeval_reesψ_varY]
  · right; left; refine ⟨q, ?_⟩
    rw [reesSys_head, map_sub, map_mul, map_pow, aeval_X, aeval_X, aeval_reesψ_varY, reesψ_varS,
      reesψ_varU]
  · right; right; refine ⟨j, ?_⟩
    rw [reesSys_y, map_sub, map_mul, aeval_X, aeval_reesψ_varY, reesψ_varYr, aeval_reesψ_varW] -/

/-! ### Renaming and the packaged theorem -/

lemma rename_mem_lspan {N N' : ℕ} (ε : Fin N → Fin N') {L : List (MvPolynomial (Fin N) ℤ)}
    {x : MvPolynomial (Fin N) ℤ} (hx : x ∈ lspan L) : rename ε x ∈ lspan (L.map (rename ε)) := by
  have := Ideal.mem_map_of_mem (rename ε : MvPolynomial (Fin N) ℤ →ₐ[ℤ] _).toRingHom hx
  rw [lspan, Ideal.map_span] at this
  convert this using 2
  ext p
  simp [Set.mem_image]

/-- **The weighted-chart open of the Rees algebra** in a global presentation `GR` (natural layout
`(Y, s, y)`, renamed along `ε` to the certificate layout). -/
theorem exists_reesChart_open (GR : List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ))
    (ε : Fin ((m + (kc + l)) + (1 + r)) ≃ Fin ((m + r) + ((1 + kc) + l)))
    (hFeq : ∀ i : Fin m, rename gY (F (Fin.castAdd _ i)) ∈ lspan GR)
    (hhead : ∀ q : Fin kc,
      rename gY (γ * F (Fin.natAdd m (Fin.castAdd l q))) - X gS ^ w q * P q ∈ lspan GR)
    (hyrow : ∀ j : Fin r, rename gY β * X (gYr j) - aeval (reesψW P) (Q j) ∈ lspan GR)
    (dW : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ)
    (hφ : ∀ g ∈ GR, dW * aeval reesφ g ∈ lspan (sysEq (reesSys F γ β w Q)))
    (b : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ)
    (hu : ∀ q : Fin kc, b * (aeval reesφ (P q) - X (varU q)) ∈ lspan (sysEq (reesSys F γ β w Q))) :
    let GR' := GR.map (rename ε)
    let ψ' := fun i => rename ε (reesψ P i)
    (∃ T : ChartData GR', T.x = (fun i => rename ε (Fin.addCases (Fin.addCases
        (fun _ => X gS) P) (fun z => rename gY (F (Fin.natAdd m (Fin.natAdd kc z)))) i)) ∧
      T.c = aeval ψ' (dW ^ 2 * (b ^ 2 * (jacPoly (reesSys F γ β w Q)).det))) ∧
    ConormalInj GR' (aeval ψ' ((jacPoly (reesSys F γ β w Q)).det * dW ^ 2)) := by
  intro GR' ψ'
  have hψ'eq : ∀ h, aeval ψ' h = rename ε (aeval (reesψ P) h) := fun h =>
    aeval_rename_comp ε (reesψ P) h
  set xT : Fin ((1 + kc) + l) → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ :=
    Fin.addCases (Fin.addCases (fun _ => X gS) P) (fun z => rename gY (F (Fin.natAdd m (Fin.natAdd kc z))))
  have hφ'eq : ∀ g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ, aeval (fun v => reesφ (ε.symm v)) (rename ε g) = aeval reesφ g := fun g => by
    rw [aeval_rename]
    have : (fun v => reesφ (ε.symm v)) ∘ ε = reesφ (m := m) (kc := kc) (l := l) (r := r) := by
      funext v; simp
    rw [this]
  refine exists_reesChart F γ β w Q GR' (fun v => reesφ (ε.symm v)) ψ' dW ?_ ?_ ?_
    (fun i => rename ε (xT i)) b ?_
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    rw [hφ'eq]; exact hφ g0 hg0
  · intro h hh
    rw [hψ'eq]
    refine rename_mem_lspan ε ?_
    rcases aeval_reesψ_sysEq F γ β w Q P h hh with ⟨i, hi⟩ | ⟨q, hq⟩ | ⟨j, hj⟩
    · rw [hi]; exact hFeq i
    · rw [hq]; exact hhead q
    · rw [hj]; exact hyrow j
  · intro v
    rw [← ε.apply_symm_apply v]
    set v0 := ε.symm v
    rw [ε.symm_apply_apply, hψ'eq, reesψφ, rename_X, sub_self]
    exact zero_mem _
  · intro i
    rw [hφ'eq]
    set J := lspan (sysEq (reesSys F γ β w Q))
    refine Fin.addCases (motive := fun i =>
      b * (aeval reesφ (xT i) - reesSys F γ β w Q (Fin.natAdd _ i)) ∈ J) ?_ ?_ i
    · intro a
      refine Fin.addCases (motive := fun a =>
        b * (aeval reesφ (xT (Fin.castAdd l a)) -
          reesSys F γ β w Q (Fin.natAdd _ (Fin.castAdd l a))) ∈ J) ?_ ?_ a
      · intro o
        have hx : xT (Fin.castAdd l (Fin.castAdd kc o)) = X gS := by simp [xT]
        have hφs : aeval (reesφ (m := m) (kc := kc) (l := l) (r := r)) (X gS : MvPolynomial _ ℤ) =
            (X varS : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ) := by
          rw [aeval_X]; simp [reesφ, gS]
        rw [hx, hφs, reesSys_su, Subsingleton.elim o 0, ← varS, sub_self, mul_zero]
        exact zero_mem _
      · intro q
        have hx : xT (Fin.castAdd l (Fin.natAdd 1 q)) = P q := by simp [xT]
        rw [hx, reesSys_su, ← varU]
        exact hu q
    · intro z
      have hx : xT (Fin.natAdd (1 + kc) z) = rename gY (F (Fin.natAdd m (Fin.natAdd kc z))) := by
        simp [xT]
      rw [hx, reesSys_rest, aeval_reesφ_gY, sub_self, mul_zero]
      exact zero_mem _

end BezoutCounterexample.Constructive
