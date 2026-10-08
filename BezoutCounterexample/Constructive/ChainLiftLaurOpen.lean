import Mathlib
import BezoutCounterexample.Constructive.ChainLiftReesOpen

/-!
# The Laurent opens in the global presentation (Task B, Rees layer S6b, Laurent part)

As `ChainLiftReesOpen`, for the Laurent model `laurSys F ε β Q` (rows `F_eq`, `s t − ε`,
`β yⱼ − Qⱼ(Y, s, t)`; coordinates `s`, the `A`-coordinates). Global layout `(Y, s, y)`;
`Pt` is a global preimage of `t = εT`.

* `laurφ` (global → model), `laurψ` (model → global, `t ↦ Pt`), `laurψφ` (`hround` exactly);
* `aeval_laurψ_sysEq`: the `ψ`-images of the model equations;
* `exists_laurChart_open`: chart data and conormal injectivity of `GR` renamed along `ε'`. All
  coordinates (`s`, heads, rest) agree exactly, so only `hφ` (L3, the Laurent case) is needed.
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {m kc l r : ℕ}

section Maps

variable (Pt : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)

/-- `ψ` on `W = (Y, s, t)`. -/
def laurψW : Fin ((m + (kc + l)) + (1 + 1)) → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ :=
  Fin.addCases (fun v => X (gY v)) (Fin.addCases (fun _ => X (gS (l := l) (r := r))) (fun _ => Pt))

/-- `ψ` in block layout. -/
def laurψB : Fin (((m + (kc + l)) + (1 + 1)) + r) →
    MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ :=
  Fin.addCases (laurψW Pt) (fun j => X (gYr j))

/-- **`ψ` (model → global)**: `Y ↦ Y`, `s ↦ s`, `t ↦ Pt`, `y ↦ y`. -/
def laurψ (i : Fin (((m + 1) + r) + ((1 + kc) + l))) : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ :=
  laurψB Pt (laurPerm i)

/-- **`φ` (global → model)**. -/
def laurφ : Fin ((m + (kc + l)) + (1 + r)) → MvPolynomial (Fin (((m + 1) + r) + ((1 + kc) + l))) ℤ :=
  Fin.addCases (fun v => X (lvarY v)) (Fin.addCases (fun _ => X lvarS) (fun j => X (lvarYr j)))

lemma aeval_laurψ_rename_perm (p : MvPolynomial (Fin (((m + (kc + l)) + (1 + 1)) + r)) ℤ) :
    aeval (laurψ Pt) (rename laurPerm.symm p) = aeval (laurψB Pt) p := by
  rw [aeval_rename]
  have : laurψ Pt ∘ laurPerm.symm = laurψB Pt := by funext v; simp [laurψ]
  rw [this]

lemma aeval_laurψ_lvarY (f : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    aeval (laurψ (r := r) Pt) (rename lvarY f) = rename gY f := by
  rw [show (rename lvarY f : MvPolynomial _ ℤ) = rename laurPerm.symm (rename (ιYL (r := r)) f) by
    rw [rename_rename]; rfl, aeval_laurψ_rename_perm, aeval_rename]
  have : laurψB Pt ∘ ιYL (r := r) = X ∘ gY := by funext v; simp [laurψB, laurψW, ιYL]
  rw [this]; exact aeval_X_comp _ _

lemma aeval_laurψ_lvarW (q : MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ) :
    aeval (laurψ (r := r) Pt) (rename lvarW q) = aeval (laurψW Pt) q := by
  rw [show (rename lvarW q : MvPolynomial _ ℤ) = rename laurPerm.symm (rename (Fin.castAdd r) q) by
    rw [rename_rename]; rfl, aeval_laurψ_rename_perm, aeval_rename]
  have : laurψB Pt ∘ Fin.castAdd r = laurψW Pt := by funext v; simp [laurψB]
  rw [this]

lemma laurψ_lvarS : laurψ (m := m) (kc := kc) (l := l) (r := r) Pt lvarS = X gS := by
  simp only [laurψ, lvarS_eq, Equiv.apply_symm_apply, laurψB, laurψW, Fin.addCases_left,
    Fin.addCases_right]

lemma laurψ_lvarT : laurψ (m := m) (kc := kc) (l := l) (r := r) Pt lvarT = Pt := by
  simp only [laurψ, lvarT_eq, Equiv.apply_symm_apply, laurψB, laurψW, Fin.addCases_left,
    Fin.addCases_right]

lemma laurψ_lvarYr (j : Fin r) : laurψ (m := m) (kc := kc) (l := l) Pt (lvarYr j) = X (gYr j) := by
  simp [laurψ, lvarYr_eq, laurψB]

lemma laurψ_lvarY (v : Fin (m + (kc + l))) : laurψ (r := r) Pt (lvarY v) = X (gY v) := by
  simp [laurψ, lvarY, ιYL, laurψB, laurψW]

/-- **`ψ ∘ φ = id`** on the global variables. -/
lemma laurψφ (v : Fin ((m + (kc + l)) + (1 + r))) : aeval (laurψ Pt) (laurφ v) = X v := by
  refine Fin.addCases ?_ ?_ v
  · intro v; simp only [laurφ, Fin.addCases_left, aeval_X]; rw [laurψ_lvarY]; rfl
  intro v
  refine Fin.addCases ?_ ?_ v
  · intro a
    simp only [laurφ, Fin.addCases_right, Fin.addCases_left, aeval_X]
    rw [laurψ_lvarS, Subsingleton.elim a 0]; rfl
  · intro j; simp only [laurφ, Fin.addCases_right, aeval_X]; rw [laurψ_lvarYr]; rfl

lemma aeval_laurφ_gY (f : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    aeval (laurφ (r := r)) (rename gY f) = rename lvarY f := by
  rw [aeval_rename]
  have : (laurφ (m := m) (kc := kc) (l := l) (r := r) ∘ gY) =
      X ∘ lvarY (m := m) (kc := kc) (l := l) (r := r) := by
    funext v; simp [laurφ, gY]
  rw [this]; exact aeval_X_comp _ _

lemma laurφ_gS : laurφ (m := m) (kc := kc) (l := l) (r := r) gS = X lvarS := by
  simp [laurφ, gS]

lemma laurφ_Y (v : Fin (m + (kc + l))) : laurφ (r := r) (gY v) = X (lvarY v) := by
  simp [laurφ, gY]

lemma laurφ_y (j : Fin r) : laurφ (m := m) (kc := kc) (l := l) (gYr j) = X (lvarYr j) := by
  simp [laurφ, gYr]

lemma lvarW_Y (v : Fin (m + (kc + l))) : lvarW (kc := kc) (r := r) (Fin.castAdd (1 + 1) v) = lvarY v :=
  rfl

lemma lvarW_s (o : Fin 1) :
    lvarW (m := m) (kc := kc) (l := l) (r := r) (Fin.natAdd _ (Fin.castAdd 1 o)) = lvarS := by
  rw [lvarS_eq, Subsingleton.elim o 0]; rfl

lemma lvarW_t (o : Fin 1) :
    lvarW (m := m) (kc := kc) (l := l) (r := r) (Fin.natAdd _ (Fin.natAdd 1 o)) = lvarT := by
  rw [lvarT_eq, Subsingleton.elim o 0]; rfl

end Maps

/-! ### The equations under `ψ` -/

variable (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (ε β : MvPolynomial (Fin (m + (kc + l))) ℤ)
  (Q : Fin r → MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ)
  (Pt : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)

/-- **The `ψ`-images of the Laurent model equations.** -/
lemma aeval_laurψ_sysEq (h : MvPolynomial (Fin (((m + 1) + r) + ((1 + kc) + l))) ℤ)
    (hh : h ∈ sysEq (laurSys F ε β Q)) :
    (∃ i : Fin m, aeval (laurψ Pt) h = rename gY (F (Fin.castAdd _ i))) ∨
    aeval (laurψ Pt) h = X gS * Pt - rename gY ε ∨
    (∃ j : Fin r, aeval (laurψ Pt) h = rename gY β * X (gYr j) - aeval (laurψW Pt) (Q j)) := by
  simp only [sysEq, List.mem_ofFn] at hh
  obtain ⟨i, rfl⟩ := hh
  refine Fin.addCases ?_ ?_ i
  · intro t
    refine Fin.addCases ?_ ?_ t
    · intro i
      left; refine ⟨i, ?_⟩
      rw [laurSys_eq, aeval_laurψ_lvarY]
    · intro o
      right; left
      rw [Subsingleton.elim o 0, laurSys_t, map_sub, map_mul, aeval_X, aeval_X, laurψ_lvarS,
        laurψ_lvarT, aeval_laurψ_lvarY]
  · intro j
    right; right; refine ⟨j, ?_⟩
    rw [laurSys_y, map_sub, map_mul, aeval_X, aeval_laurψ_lvarY, laurψ_lvarYr, aeval_laurψ_lvarW]

/-- **A Laurent open of the Rees algebra** in a global presentation `GR` (natural layout, renamed
along `ε'`). All model coordinates agree exactly with the global ones (`b = 1`). -/
theorem exists_laurChart_open (GR : List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ))
    (ε' : Fin ((m + (kc + l)) + (1 + r)) ≃ Fin ((m + r) + ((1 + kc) + l)))
    (hFeq : ∀ i : Fin m, rename gY (F (Fin.castAdd _ i)) ∈ lspan GR)
    (ht : X gS * Pt - rename gY ε ∈ lspan GR)
    (hyrow : ∀ j : Fin r, rename gY β * X (gYr j) - aeval (laurψW Pt) (Q j) ∈ lspan GR)
    (dW : MvPolynomial (Fin (((m + 1) + r) + ((1 + kc) + l))) ℤ)
    (hφ : ∀ g ∈ GR, dW * aeval laurφ g ∈ lspan (sysEq (laurSys F ε β Q))) :
    let GR' := GR.map (rename ε')
    let ψ' := fun i => rename ε' (laurψ Pt i)
    (∃ T : ChartData GR', T.x = (fun i => rename ε' (Fin.addCases (Fin.addCases
        (fun _ => X gS) (fun q => rename gY (F (Fin.natAdd m (Fin.castAdd l q)))))
        (fun z => rename gY (F (Fin.natAdd m (Fin.natAdd kc z)))) i)) ∧
      T.c = aeval ψ' (dW ^ 2 * (1 ^ 2 * (jacPoly (laurSys F ε β Q)).det))) ∧
    ConormalInj GR' (aeval ψ' ((jacPoly (laurSys F ε β Q)).det * dW ^ 2)) := by
  intro GR' ψ'
  have hψ'eq : ∀ h, aeval ψ' h = rename ε' (aeval (laurψ Pt) h) := fun h =>
    aeval_rename_comp ε' (laurψ Pt) h
  set xT : Fin ((1 + kc) + l) → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ :=
    Fin.addCases (Fin.addCases (fun _ => X gS) (fun q => rename gY (F (Fin.natAdd m (Fin.castAdd l q)))))
      (fun z => rename gY (F (Fin.natAdd m (Fin.natAdd kc z))))
  have hφ'eq : ∀ g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ,
      aeval (fun v => laurφ (ε'.symm v)) (rename ε' g) = aeval laurφ g := fun g => by
    rw [aeval_rename]
    have : (fun v => laurφ (ε'.symm v)) ∘ ε' = laurφ (m := m) (kc := kc) (l := l) (r := r) := by
      funext v; simp
    rw [this]
  refine exists_laurChart F ε β Q GR' (fun v => laurφ (ε'.symm v)) ψ' dW ?_ ?_ ?_
    (fun i => rename ε' (xT i)) 1 ?_
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    rw [hφ'eq]; exact hφ g0 hg0
  · intro h hh
    rw [hψ'eq]
    refine rename_mem_lspan ε' ?_
    rcases aeval_laurψ_sysEq F ε β Q Pt h hh with ⟨i, hi⟩ | hi | ⟨j, hj⟩
    · rw [hi]; exact hFeq i
    · rw [hi]; exact ht
    · rw [hj]; exact hyrow j
  · intro v
    rw [← ε'.apply_symm_apply v, ε'.symm_apply_apply, hψ'eq, laurψφ, rename_X, sub_self]
    exact zero_mem _
  · intro i
    rw [hφ'eq, one_mul]
    set J := lspan (sysEq (laurSys F ε β Q))
    refine Fin.addCases (motive := fun i =>
      aeval laurφ (xT i) - laurSys F ε β Q (Fin.natAdd _ i) ∈ J) ?_ ?_ i
    · intro a
      refine Fin.addCases (motive := fun a =>
        aeval laurφ (xT (Fin.castAdd l a)) -
          laurSys F ε β Q (Fin.natAdd _ (Fin.castAdd l a)) ∈ J) ?_ ?_ a
      · intro o
        have hx : xT (Fin.castAdd l (Fin.castAdd kc o)) = X gS := by simp [xT]
        rw [hx, aeval_X, laurφ_gS, Subsingleton.elim o 0, laurSys_s, sub_self]
        exact zero_mem _
      · intro q
        have hx : xT (Fin.castAdd l (Fin.natAdd 1 q)) =
            rename gY (F (Fin.natAdd m (Fin.castAdd l q))) := by simp [xT]
        rw [hx, laurSys_head, aeval_laurφ_gY, sub_self]
        exact zero_mem _
    · intro z
      have hx : xT (Fin.natAdd (1 + kc) z) = rename gY (F (Fin.natAdd m (Fin.natAdd kc z))) := by
        simp [xT]
      rw [hx, laurSys_rest, aeval_laurφ_gY, sub_self]
      exact zero_mem _

end BezoutCounterexample.Constructive
