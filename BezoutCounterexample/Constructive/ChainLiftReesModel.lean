import Mathlib
import BezoutCounterexample.Constructive.ChainLiftChartCongr
import BezoutCounterexample.Constructive.ChainLiftSystem

/-!
# The Rees model square system (Task B, Rees layer S4b)

Part 1: three determinant lemmas used for the Jacobian of the model.

* `det_sub_mem_of_congr`: determinants respect entrywise congruence modulo an ideal;
* `det_sub_prod_mul_mem`: if `Aᵢⱼ ≡ dᵢ Bᵢⱼ` modulo an ideal, then `det A ≡ (∏ dᵢ) det B`;
* `det_fin_lower`: a matrix on `Fin (p + q)` whose upper right block vanishes has determinant
  `det(upper left) · det(lower right)`.

Part 2: the two local models of `R = ReesAlg Φ` as square systems, for an `A`-piece `F` with `m`
equations and coordinates `heads (kc) ++ rest (l)`.

* Weighted chart (open `D(c_τ g_k)`): `reesSys F γ β w Q` in `(Y, s, u', y)`, equations
  `F_eq`, `γ x̃_q - s^{w_q} u'_q`, `β yⱼ - Qⱼ(s, u', Y)`, coordinates `s, u', x̃_rest`.
  `det_reesSys`: `det = ren(det ∂(hd·F) · β^r)`; `det_reesSys_sub_mem`: `det ≡ ren(γ^kc β^r det ∂F)`
  modulo the heads (the complementary opens `D(x̃_q)` are Laurent).
* Laurent (opens `D(x̃_q)`, `D(i)`, `i ∈ 𝔭`): `laurSys F ε β Q` in `(Y, s, t, y)`, equations `F_eq`,
  `s t - ε`, `β yⱼ - Qⱼ(Y, s, t)`, coordinates `s, x̃`; `det_laurSys`: `det = ren(det ∂F) · s · ren(β)^r`
  (`ε ∈ A` makes `t ↦ P̃` with `s P̃ = ε` polynomial: `ε = γ x̃_q`, resp. `i^N`).
* Both are built in block layout (`reesModel`, `laurModel`: block lower-triangular Jacobians) and
  reindexed equations-first by one permutation of rows and variables (`reesPerm`, `laurPerm`;
  `det_jacPoly_perm`), with row lemmas `reesSys_eq/head/y/su/rest`, `laurSys_eq/t/y/s/head/rest`.
* `exists_reesChart`, `exists_laurChart`: chart data (coordinates changed modulo the model by
  `exists_coordCongr`) and conormal injectivity of a global presentation `GR`, by the transport lemmas
  (`exists_chartData_transport`, `conormalRet_transport`); then `exists_minor_cover` gives pieces.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial Matrix

section Det

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Determinants respect congruence** modulo an ideal. -/
lemma det_sub_mem_of_congr (J : Ideal R) {A A' : Matrix ι ι R} (h : ∀ i j, A i j - A' i j ∈ J) :
    A.det - A'.det ∈ J := by
  rw [← Ideal.Quotient.eq]
  have hm : A.map (Ideal.Quotient.mk J) = A'.map (Ideal.Quotient.mk J) := by
    ext i j; exact Ideal.Quotient.eq.2 (h i j)
  rw [RingHom.map_det, RingHom.map_det]
  exact congrArg Matrix.det hm

/-- **Diagonal rescaling** modulo an ideal: `Aᵢⱼ ≡ dᵢ Bᵢⱼ` gives `det A ≡ (∏ dᵢ) det B`. -/
lemma det_sub_prod_mul_mem (J : Ideal R) {A B : Matrix ι ι R} (d : ι → R)
    (h : ∀ i j, A i j - d i * B i j ∈ J) : A.det - (∏ i, d i) * B.det ∈ J := by
  have := det_sub_mem_of_congr J (A' := Matrix.diagonal d * B) fun i j => by
    rw [Matrix.diagonal_mul]; exact h i j
  rwa [Matrix.det_mul, Matrix.det_diagonal] at this

end Det

/-- **Block lower-triangular determinant** on `Fin (p + q)`. -/
lemma det_fin_lower {R : Type*} [CommRing R] {p q : ℕ} (M : Matrix (Fin (p + q)) (Fin (p + q)) R)
    (h0 : ∀ (i : Fin p) (j : Fin q), M (Fin.castAdd q i) (Fin.natAdd p j) = 0) :
    M.det = (M.submatrix (Fin.castAdd q) (Fin.castAdd q)).det *
      (M.submatrix (Fin.natAdd p) (Fin.natAdd p)).det := by
  rw [← Matrix.det_reindex_self finSumFinEquiv.symm M,
    ← Matrix.fromBlocks_toBlocks (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M)]
  have hz : (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M).toBlocks₁₂ = 0 := by
    ext i j; simpa [Matrix.toBlocks₁₂] using h0 i j
  rw [hz, Matrix.det_fromBlocks_zero₁₂]
  rfl

section Model

/-! ### Part 2: the model square system

Variables, in block layout: `W = (1 + kc) + (m + (kc + l))` (`s`, `u'₀ … u'_{kc-1}` | the `Y` of an
`A`-piece with `m` equations and coordinates `heads (kc) ++ rest (l)`), then `r` variables `y`.
Rows: `X s`, `X u'` | the `A`-rows `F`, with the head coordinate rows replaced by `γ·F_q - s^{w_q} u'_q`
| `β yⱼ - Qⱼ(s, u', Y)`. The Jacobian is block lower-triangular, so
`det = ren(det ∂(hd·F)) · (ren β)^r`, and `det ∂(hd·F) ≡ γ^kc det ∂F` modulo the heads. -/

variable {m kc l r : ℕ}

/-- The derivative along a variable outside the image of a renaming vanishes. -/
lemma pderiv_rename_eq_zero {σ τ R : Type*} [CommSemiring R] (f : σ → τ) {v : τ}
    (hv : ∀ x, f x ≠ v) (p : MvPolynomial σ R) : pderiv v (rename f p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a h =>
    rw [map_mul, rename_X, Derivation.leibniz, h, pderiv_X_of_ne (hv a), smul_zero, smul_zero,
      add_zero]

lemma castAdd_ne_natAdd {p q : ℕ} (i : Fin p) (j : Fin q) : Fin.castAdd q i ≠ Fin.natAdd p j := by
  intro e; have h1 := congrArg Fin.val e; have h2 := i.isLt
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h1; omega

/-- Head multipliers: `γ` on the head coordinate rows, `1` elsewhere. -/
noncomputable def headMul (γ : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ :=
  Fin.addCases (fun _ => 1) (Fin.addCases (fun _ => γ) (fun _ => 1))

/-- Head corrections `s^{w_q} u'_q` (in the variables `s, u'`), `0` elsewhere. -/
noncomputable def headCorr (w : Fin kc → ℕ) :
    Fin (m + (kc + l)) → MvPolynomial (Fin (1 + kc)) ℤ :=
  Fin.addCases (fun _ => 0)
    (Fin.addCases (fun q => X (Fin.castAdd kc 0) ^ w q * X (Fin.natAdd 1 q)) (fun _ => 0))

variable (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (γ β : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ)
  (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)

/-- The `A`-rows with multipliers. -/
noncomputable def headRows : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ :=
  fun v => headMul γ v * F v

/-- The `Y`-rows of the model: `hd·F - corr`. -/
noncomputable def reesRowY (v : Fin (m + (kc + l))) :
    MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ :=
  rename (Fin.natAdd (1 + kc)) (headRows F γ v) - rename (Fin.castAdd (m + (kc + l))) (headCorr w v)

/-- The rows over `W`: coordinates `X s, X u'`, then the `Y`-rows. -/
noncomputable def reesRowW :
    Fin ((1 + kc) + (m + (kc + l))) → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ :=
  Fin.addCases (fun i => X (Fin.castAdd (m + (kc + l)) i)) (reesRowY F γ w)

/-- The renaming of `Y` into the model variables. -/
def ιY : Fin (m + (kc + l)) → Fin (((1 + kc) + (m + (kc + l))) + r) :=
  fun v => Fin.castAdd r (Fin.natAdd (1 + kc) v)

/-- **The Rees model square system** (block layout). -/
noncomputable def reesModel :
    Fin (((1 + kc) + (m + (kc + l))) + r) → MvPolynomial (Fin (((1 + kc) + (m + (kc + l))) + r)) ℤ :=
  Fin.addCases (fun a => rename (Fin.castAdd r) (reesRowW F γ w a))
    (fun j => rename (ιY (r := r)) β * X (Fin.natAdd _ j) - rename (Fin.castAdd r) (Q j))

/-- **The determinant of the multiplied rows** modulo the heads. -/
lemma det_headRows_sub_mem :
    (jacPoly (headRows F γ)).det - γ ^ kc * (jacPoly F).det ∈
      Ideal.span (Set.range fun q : Fin kc => F (Fin.natAdd m (Fin.castAdd l q))) := by
  have hprod : ∏ v, headMul (m := m) (l := l) γ v = γ ^ kc := by
    simp [Fin.prod_univ_add, headMul]
  rw [← hprod]
  refine det_sub_prod_mul_mem _ _ fun v j => ?_
  simp only [jacPoly, Matrix.of_apply, headRows, Derivation.leibniz, smul_eq_mul]
  rw [add_sub_cancel_left]
  refine Fin.addCases (fun i => ?_) (fun t => Fin.addCases (fun q => ?_) (fun z => ?_) t) v
  · simp [headMul]
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨q, rfl⟩)
  · simp [headMul]

lemma det_reesRowW :
    (jacPoly (reesRowW F γ w)).det = rename (Fin.natAdd (1 + kc)) (jacPoly (headRows F γ)).det := by
  rw [det_fin_lower _ fun i j => ?_]
  · have h1 : ((jacPoly (reesRowW F γ w)).submatrix (Fin.castAdd _) (Fin.castAdd _)) = 1 := by
      ext i j
      simp only [jacPoly, reesRowW, Matrix.submatrix_apply, Matrix.of_apply, Fin.addCases_left,
        pderiv_X, Pi.single_apply, Matrix.one_apply, (Fin.castAdd_injective _ _).eq_iff]
    have h2 : ((jacPoly (reesRowW F γ w)).submatrix (Fin.natAdd _) (Fin.natAdd _)) =
        (jacPoly (headRows F γ)).map (rename (Fin.natAdd (1 + kc))) := by
      ext v v'
      simp only [jacPoly, reesRowW, reesRowY, Matrix.submatrix_apply, Matrix.of_apply,
        Matrix.map_apply, Fin.addCases_right, map_sub]
      rw [pderiv_rename (Fin.natAdd_injective _ _),
        pderiv_rename_eq_zero _ (fun x => castAdd_ne_natAdd x v'), sub_zero]
    rw [h1, h2, Matrix.det_one, one_mul]
    exact (AlgHom.map_det (rename (Fin.natAdd (1 + kc))) _).symm
  · simp only [jacPoly, reesRowW, Matrix.of_apply, Fin.addCases_left]
    exact pderiv_X_of_ne (castAdd_ne_natAdd i j)

/-- **The determinant of the Rees model**: `det = ren(det ∂(hd·F)) · (ren β)^r`. -/
lemma det_reesModel :
    (jacPoly (reesModel F γ β w Q)).det =
      rename (ιY (r := r)) (jacPoly (headRows F γ)).det * rename (ιY (r := r)) β ^ r := by
  rw [det_fin_lower _ fun a j => ?_]
  · have h1 : ((jacPoly (reesModel F γ β w Q)).submatrix (Fin.castAdd r) (Fin.castAdd r)) =
        (jacPoly (reesRowW F γ w)).map (rename (Fin.castAdd r)) := by
      ext a b
      simp only [jacPoly, reesModel, Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply,
        Fin.addCases_left]
      rw [pderiv_rename (Fin.castAdd_injective _ _)]
    have h2 : ((jacPoly (reesModel F γ β w Q)).submatrix (Fin.natAdd _) (Fin.natAdd _)) =
        Matrix.diagonal fun _ => rename (ιY (r := r)) β := by
      refine Matrix.ext fun j j' => ?_
      simp only [jacPoly, reesModel, Matrix.submatrix_apply, Matrix.of_apply, Fin.addCases_right,
        map_sub, Derivation.leibniz, smul_eq_mul, Matrix.diagonal_apply, pderiv_X, Pi.single_apply,
        (Fin.natAdd_injective _ _).eq_iff]
      rw [pderiv_rename_eq_zero ιY (fun x => castAdd_ne_natAdd _ j'),
        pderiv_rename_eq_zero _ (fun x => castAdd_ne_natAdd x j')]
      by_cases h : j = j'
      · simp [h]
      · simp [h]
    have h3 := AlgHom.map_det (rename (Fin.castAdd r)) (jacPoly (reesRowW F γ w))
    rw [AlgHom.mapMatrix_apply] at h3
    rw [h1, h2, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← h3, det_reesRowW, rename_rename]
    rfl
  · simp only [jacPoly, reesModel, Matrix.of_apply, Fin.addCases_left]
    exact pderiv_rename_eq_zero _ (fun x => castAdd_ne_natAdd x j) _

end Model

section Reindex

/-! ### Equations first

The model as a square system on `Fin (((m + kc) + r) + ((1 + kc) + l))`: equations (`A`-equations,
heads, `y`-rows), then coordinates (`s, u'`, the non-head `A`-coordinates). Rows and variables are
reindexed by the same permutation `reesPerm`, so the Jacobian determinant is only renamed. -/

variable {m kc l r : ℕ}

/-- The block permutation, on sums. -/
def reesSumEquiv :
    ((Fin m ⊕ Fin kc) ⊕ Fin r) ⊕ (Fin (1 + kc) ⊕ Fin l) ≃
      (Fin (1 + kc) ⊕ (Fin m ⊕ (Fin kc ⊕ Fin l))) ⊕ Fin r where
  toFun
    | .inl (.inl (.inl i)) => .inl (.inr (.inl i))
    | .inl (.inl (.inr q)) => .inl (.inr (.inr (.inl q)))
    | .inl (.inr j) => .inr j
    | .inr (.inl a) => .inl (.inl a)
    | .inr (.inr z) => .inl (.inr (.inr (.inr z)))
  invFun
    | .inl (.inr (.inl i)) => .inl (.inl (.inl i))
    | .inl (.inr (.inr (.inl q))) => .inl (.inl (.inr q))
    | .inr j => .inl (.inr j)
    | .inl (.inl a) => .inr (.inl a)
    | .inl (.inr (.inr (.inr z))) => .inr (.inr z)
  left_inv := by rintro (((i | q) | j) | (a | z)) <;> rfl
  right_inv := by rintro ((a | (i | (q | z))) | j) <;> rfl

/-- **The row and variable permutation**: equations-first layout → block layout. -/
def reesPerm : Fin (((m + kc) + r) + ((1 + kc) + l)) ≃ Fin (((1 + kc) + (m + (kc + l))) + r) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)))
    finSumFinEquiv.symm)).trans
  (reesSumEquiv.trans (finSumFinEquiv.symm.trans (Equiv.sumCongr
    (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _)
      (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm))))
    (Equiv.refl _))).symm)

lemma reesPerm_eq (i : Fin m) :
    reesPerm (kc := kc) (l := l) (r := r) (Fin.castAdd _ (Fin.castAdd r (Fin.castAdd kc i))) =
      Fin.castAdd r (Fin.natAdd (1 + kc) (Fin.castAdd (kc + l) i)) := by
  simp [reesPerm, reesSumEquiv]

lemma reesPerm_head (q : Fin kc) :
    reesPerm (m := m) (l := l) (r := r) (Fin.castAdd _ (Fin.castAdd r (Fin.natAdd m q))) =
      Fin.castAdd r (Fin.natAdd (1 + kc) (Fin.natAdd m (Fin.castAdd l q))) := by
  simp [reesPerm, reesSumEquiv]

lemma reesPerm_y (j : Fin r) :
    reesPerm (m := m) (kc := kc) (l := l) (Fin.castAdd _ (Fin.natAdd (m + kc) j)) =
      Fin.natAdd _ j := by
  simp [reesPerm, reesSumEquiv]

lemma reesPerm_su (a : Fin (1 + kc)) :
    reesPerm (m := m) (l := l) (r := r) (Fin.natAdd _ (Fin.castAdd l a)) =
      Fin.castAdd r (Fin.castAdd (m + (kc + l)) a) := by
  simp [reesPerm, reesSumEquiv]

lemma reesPerm_rest (z : Fin l) :
    reesPerm (m := m) (kc := kc) (r := r) (Fin.natAdd _ (Fin.natAdd (1 + kc) z)) =
      Fin.castAdd r (Fin.natAdd (1 + kc) (Fin.natAdd m (Fin.natAdd kc z))) := by
  simp [reesPerm, reesSumEquiv]

/-- A square system reindexed along one permutation of rows and variables. -/
lemma det_jacPoly_perm {N N' : ℕ} (M : Fin N' → MvPolynomial (Fin N') ℤ) (e : Fin N ≃ Fin N') :
    (jacPoly fun i => rename e.symm (M (e i))).det = rename e.symm (jacPoly M).det := by
  have h : jacPoly (fun i => rename e.symm (M (e i))) =
      ((jacPoly M).submatrix e e).map (rename e.symm) := by
    refine Matrix.ext fun i k => ?_
    simp only [jacPoly, Matrix.of_apply, Matrix.map_apply, Matrix.submatrix_apply]
    conv_lhs => rw [← e.symm_apply_apply k]
    exact pderiv_rename e.symm.injective _ _
  rw [h, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det, Matrix.det_submatrix_equiv_self]

end Reindex

section System

variable {m kc l r : ℕ} (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (γ β : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ)
  (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)

/-- **The Rees model square system** (equations first): `A`-equations, heads, `y`-rows; coordinates
`s, u'`, non-head `A`-coordinates. -/
noncomputable def reesSys :
    Fin (((m + kc) + r) + ((1 + kc) + l)) → MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ :=
  fun i => rename reesPerm.symm (reesModel F γ β w Q (reesPerm i))

/-- The model variables `Y`. -/
def varY (v : Fin (m + (kc + l))) : Fin (((m + kc) + r) + ((1 + kc) + l)) :=
  reesPerm.symm (ιY v)

/-- The model variables `(s, u', Y)`. -/
def varW (a : Fin ((1 + kc) + (m + (kc + l)))) : Fin (((m + kc) + r) + ((1 + kc) + l)) :=
  reesPerm.symm (Fin.castAdd r a)

/-- The model variables `y`. -/
def varYr (j : Fin r) : Fin (((m + kc) + r) + ((1 + kc) + l)) :=
  Fin.castAdd _ (Fin.natAdd (m + kc) j)

/-- The model variable `s`. -/
def varS : Fin (((m + kc) + r) + ((1 + kc) + l)) := Fin.natAdd _ (Fin.castAdd l (Fin.castAdd kc 0))

/-- The model variables `u'`. -/
def varU (q : Fin kc) : Fin (((m + kc) + r) + ((1 + kc) + l)) :=
  Fin.natAdd _ (Fin.castAdd l (Fin.natAdd 1 q))

lemma varW_su (a : Fin (1 + kc)) :
    varW (m := m) (l := l) (r := r) (Fin.castAdd _ a) = Fin.natAdd _ (Fin.castAdd l a) := by
  rw [varW, ← reesPerm_su, Equiv.symm_apply_apply]

lemma varS_eq : varS (m := m) (kc := kc) (l := l) (r := r) =
    reesPerm.symm (Fin.castAdd r (Fin.castAdd _ (Fin.castAdd kc 0))) := (varW_su _).symm

lemma varU_eq (q : Fin kc) : varU (m := m) (l := l) (r := r) q =
    reesPerm.symm (Fin.castAdd r (Fin.castAdd _ (Fin.natAdd 1 q))) := (varW_su _).symm

lemma varYr_eq (j : Fin r) :
    varYr (m := m) (kc := kc) (l := l) j = reesPerm.symm (Fin.natAdd _ j) := by
  rw [varYr, ← reesPerm_y, Equiv.symm_apply_apply]

lemma reesSys_eq (i : Fin m) :
    reesSys F γ β w Q (Fin.castAdd _ (Fin.castAdd r (Fin.castAdd kc i))) =
      rename varY (F (Fin.castAdd _ i)) := by
  simp only [reesSys, reesPerm_eq, reesModel, Fin.addCases_left, reesRowW, Fin.addCases_right,
    reesRowY, headRows, headMul, headCorr, one_mul, map_zero, sub_zero, rename_rename]
  rfl

lemma reesSys_head (q : Fin kc) :
    reesSys F γ β w Q (Fin.castAdd _ (Fin.castAdd r (Fin.natAdd m q))) =
      rename varY (γ * F (Fin.natAdd m (Fin.castAdd l q))) - X varS ^ w q * X (varU q) := by
  simp only [reesSys, reesPerm_head, reesModel, Fin.addCases_left, reesRowW, Fin.addCases_right,
    reesRowY, headRows, headMul, headCorr, map_sub, rename_rename, map_mul, map_pow, rename_X]
  rw [varS_eq, varU_eq]
  rfl

lemma reesSys_y (j : Fin r) :
    reesSys F γ β w Q (Fin.castAdd _ (Fin.natAdd (m + kc) j)) =
      rename varY β * X (varYr j) - rename varW (Q j) := by
  simp only [reesSys, reesPerm_y, reesModel, Fin.addCases_right, map_sub, map_mul, rename_rename,
    rename_X, varYr_eq]
  rfl

lemma reesSys_su (a : Fin (1 + kc)) :
    reesSys F γ β w Q (Fin.natAdd _ (Fin.castAdd l a)) = X (Fin.natAdd _ (Fin.castAdd l a)) := by
  simp only [reesSys, reesPerm_su, reesModel, Fin.addCases_left, reesRowW, rename_X]
  rw [← reesPerm_su, Equiv.symm_apply_apply]

lemma reesSys_rest (z : Fin l) :
    reesSys F γ β w Q (Fin.natAdd _ (Fin.natAdd (1 + kc) z)) =
      rename varY (F (Fin.natAdd m (Fin.natAdd kc z))) := by
  simp only [reesSys, reesPerm_rest, reesModel, Fin.addCases_left, reesRowW, Fin.addCases_right,
    reesRowY, headRows, headMul, headCorr, one_mul, map_zero, sub_zero, rename_rename]
  rfl

/-- **The Jacobian determinant of the Rees model**, exactly. -/
lemma det_reesSys :
    (jacPoly (reesSys F γ β w Q)).det = rename varY ((jacPoly (headRows F γ)).det * β ^ r) := by
  show (jacPoly fun i => rename reesPerm.symm (reesModel F γ β w Q (reesPerm i))).det = _
  rw [det_jacPoly_perm, det_reesModel, map_mul, map_mul, map_pow, map_pow, rename_rename,
    rename_rename]
  rfl

/-- **The Jacobian determinant of the Rees model modulo the heads**:
`det ≡ ren(γ^kc β^r det ∂F)`. -/
lemma det_reesSys_sub_mem :
    (jacPoly (reesSys F γ β w Q)).det - rename varY (γ ^ kc * β ^ r * (jacPoly F).det) ∈
      Ideal.span (Set.range fun q : Fin kc =>
        rename (varY (r := r)) (F (Fin.natAdd m (Fin.castAdd l q)))) := by
  have h1 := Ideal.mul_mem_right (β ^ r) _ (det_headRows_sub_mem F γ)
  have h2 := Ideal.mem_map_of_mem (rename (varY (r := r)) :
    MvPolynomial (Fin (m + (kc + l))) ℤ →ₐ[ℤ] MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ) h1
  rw [Ideal.map_span, ← Set.range_comp] at h2
  have e : (jacPoly (reesSys F γ β w Q)).det - rename varY (γ ^ kc * β ^ r * (jacPoly F).det) =
      rename varY (((jacPoly (headRows F γ)).det - γ ^ kc * (jacPoly F).det) * β ^ r) := by
    simp only [det_reesSys, map_mul, map_sub, map_pow]
    ring
  rw [e]
  exact h2

end System

section Transport

variable {m kc l r : ℕ} (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (γ β : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ)
  (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)

/-- **Chart data and conormal injectivity of a global presentation from the Rees model.**
`GR` is presented in `mR + ((1 + kc) + l)` variables; `φ` (global → model), `ψ` (model → global) and
`dW` satisfy the hypotheses of the transport lemmas, and the target coordinates `xT` pulled back by
`φ` agree with the model coordinates (`s`, `u'`, the non-head `A`-coordinates) up to `b` modulo the
model equations. Multipliers: `ψ(dW² b² det)` for the chart data, `ψ(det dW²)` for conormal
injectivity, where `det` is the model's Jacobian determinant (`det_reesSys`, `det_reesSys_sub_mem`). -/
theorem exists_reesChart {mR : ℕ} (GR : List (MvPolynomial (Fin (mR + ((1 + kc) + l))) ℤ))
    (φ : Fin (mR + ((1 + kc) + l)) → MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ)
    (ψ : Fin (((m + kc) + r) + ((1 + kc) + l)) → MvPolynomial (Fin (mR + ((1 + kc) + l))) ℤ)
    (dW : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ)
    (hφ : ∀ g ∈ GR, dW * aeval φ g ∈ lspan (sysEq (reesSys F γ β w Q)))
    (hψ : ∀ h ∈ sysEq (reesSys F γ β w Q), aeval ψ h ∈ lspan GR)
    (hround : ∀ v, X v - aeval ψ (φ v) ∈ lspan GR)
    (xT : Fin ((1 + kc) + l) → MvPolynomial (Fin (mR + ((1 + kc) + l))) ℤ)
    (b : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ)
    (hx : ∀ i, b * (aeval φ (xT i) - reesSys F γ β w Q (Fin.natAdd _ i)) ∈
      lspan (sysEq (reesSys F γ β w Q))) :
    (∃ T : ChartData GR, T.x = xT ∧
      T.c = aeval ψ (dW ^ 2 * (b ^ 2 * (jacPoly (reesSys F γ β w Q)).det))) ∧
    ConormalInj GR (aeval ψ ((jacPoly (reesSys F γ β w Q)).det * dW ^ 2)) := by
  obtain ⟨T', hx', hc'⟩ :=
    (ChartData.ofSystem (reesSys F γ β w Q)).exists_coordCongr (fun i => aeval φ (xT i)) b hx
  obtain ⟨T, hT1, hT2, -⟩ := exists_chartData_transport (hψ := hψ) (hround := hround) hφ T' xT
    (fun i => by rw [hx'])
  refine ⟨⟨T, hT1, by rw [hT2, hc']; rfl⟩, ?_⟩
  obtain ⟨a, ha⟩ := exists_conormalRet_system (reesSys F γ β w Q) (by omega)
  exact conormalInj_of_ret (conormalRet_transport GR _ φ ψ dW hφ hψ hround ha)

end Transport

section Laurent

/-! ### The Laurent model (opens `D(x̃_q)`, `D(i)`, `i ∈ 𝔭`)

There `R_ε = A_ε[s, t]/(st - ε)` with `ε ∈ A` (`ε = γ x̃_q`, resp. `i^N`): `t ↦ P̃(Y, y)` with
`s P̃ = ε` in `R`, so both substitutions are polynomial. Block layout
`((m + (kc + l)) + (1 + 1)) + r` (`Y` | `s, t` | `y`); rows `F` | `X s`, `s t - ε` | `β yⱼ - Qⱼ(Y, s, t)`
(`t = εT`, so `yⱼ = gⱼ T^{δⱼ}` needs the multiplier `β = ε^{max δ}`). `det = ren(det ∂F) · ren(s) · ren(β)^r`. Equations first: `A`-equations, `s t - ε`, `y`-rows; coordinates
`s`, then the `A`-coordinates (`kc + l`; the coordinate block is `(1 + kc) + l` as for the weighted
model). -/

variable {m kc l r : ℕ} (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (ε β : MvPolynomial (Fin (m + (kc + l))) ℤ)
  (Q : Fin r → MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ)

/-- The `(s, t)`-rows: `X s`, `s t - ε`. -/
noncomputable def laurRowST : Fin (1 + 1) → MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ :=
  Fin.addCases (fun _ => X (Fin.natAdd _ (Fin.castAdd 1 0)))
    (fun _ => X (Fin.natAdd _ (Fin.castAdd 1 0)) * X (Fin.natAdd _ (Fin.natAdd 1 0)) -
      rename (Fin.castAdd (1 + 1)) ε)

/-- The rows over `W = (Y, s, t)`. -/
noncomputable def laurRowW :
    Fin ((m + (kc + l)) + (1 + 1)) → MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ :=
  Fin.addCases (fun v => rename (Fin.castAdd (1 + 1)) (F v)) (laurRowST ε)

/-- The renaming of `Y` into the Laurent model's block layout. -/
def ιYL : Fin (m + (kc + l)) → Fin (((m + (kc + l)) + (1 + 1)) + r) :=
  fun v => Fin.castAdd r (Fin.castAdd (1 + 1) v)

/-- **The Laurent model** (block layout). -/
noncomputable def laurModel :
    Fin (((m + (kc + l)) + (1 + 1)) + r) → MvPolynomial (Fin (((m + (kc + l)) + (1 + 1)) + r)) ℤ :=
  Fin.addCases (fun a => rename (Fin.castAdd r) (laurRowW F ε a))
    (fun j => rename (ιYL (r := r)) β * X (Fin.natAdd _ j) - rename (Fin.castAdd r) (Q j))

lemma det_laurRowST_block :
    ((jacPoly (laurRowW F ε)).submatrix (Fin.natAdd (m + (kc + l))) (Fin.natAdd _)).det =
      X (Fin.natAdd (m + (kc + l)) (Fin.castAdd 1 0)) := by
  rw [det_fin_lower _ fun i j => ?_]
  · have h1 : ((jacPoly (laurRowW F ε)).submatrix (Fin.natAdd (m + (kc + l))) (Fin.natAdd _)).submatrix
        (Fin.castAdd 1) (Fin.castAdd 1) = 1 := by
      refine Matrix.ext fun i j => ?_
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp only [jacPoly, laurRowW, laurRowST, Matrix.submatrix_apply, Matrix.of_apply,
        Fin.addCases_right, Fin.addCases_left, pderiv_X_self, Matrix.one_apply_eq]
    have h2 : ((jacPoly (laurRowW F ε)).submatrix (Fin.natAdd (m + (kc + l))) (Fin.natAdd _)).submatrix
        (Fin.natAdd 1) (Fin.natAdd 1) = Matrix.of fun _ _ => X (Fin.natAdd (m + (kc + l)) (Fin.castAdd 1 0)) := by
      refine Matrix.ext fun i j => ?_
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp only [jacPoly, laurRowW, laurRowST, Matrix.submatrix_apply, Matrix.of_apply,
        Fin.addCases_right, map_sub, Derivation.leibniz, smul_eq_mul, pderiv_X_self, mul_one]
      rw [pderiv_X_of_ne (fun e => castAdd_ne_natAdd (0 : Fin 1) (0 : Fin 1)
          ((Fin.natAdd_injective _ _) e)),
        pderiv_rename_eq_zero _ (fun x => castAdd_ne_natAdd x _), mul_zero, add_zero, sub_zero]
    rw [h1, h2, Matrix.det_one, one_mul, Matrix.det_unique]
    rfl
  · simp only [jacPoly, laurRowW, laurRowST, Matrix.submatrix_apply, Matrix.of_apply,
      Fin.addCases_right, Fin.addCases_left]
    exact pderiv_X_of_ne (fun e => castAdd_ne_natAdd (0 : Fin 1) j ((Fin.natAdd_injective _ _) e))

lemma det_laurRowW :
    (jacPoly (laurRowW F ε)).det =
      rename (Fin.castAdd (1 + 1)) (jacPoly F).det * X (Fin.natAdd (m + (kc + l)) (Fin.castAdd 1 0)) := by
  rw [det_fin_lower _ fun v j => ?_, det_laurRowST_block]
  · have h1 : ((jacPoly (laurRowW F ε)).submatrix (Fin.castAdd _) (Fin.castAdd _)) =
        (jacPoly F).map (rename (Fin.castAdd (1 + 1))) := by
      refine Matrix.ext fun a b => ?_
      simp only [jacPoly, laurRowW, Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply,
        Fin.addCases_left]
      rw [pderiv_rename (Fin.castAdd_injective _ _)]
    have h3 := AlgHom.map_det (rename (Fin.castAdd (1 + 1))) (jacPoly F)
    rw [AlgHom.mapMatrix_apply] at h3
    rw [h1, ← h3]
  · simp only [jacPoly, laurRowW, Matrix.of_apply, Fin.addCases_left]
    exact pderiv_rename_eq_zero _ (fun x => castAdd_ne_natAdd x j) _

/-- **The determinant of the Laurent model**: `ren(det ∂F) · s · ren(β)^r`. -/
lemma det_laurModel :
    (jacPoly (laurModel F ε β Q)).det =
      rename (ιYL (r := r)) (jacPoly F).det *
        X (Fin.castAdd r (Fin.natAdd (m + (kc + l)) (Fin.castAdd 1 0))) * rename (ιYL (r := r)) β ^ r := by
  rw [det_fin_lower _ fun a j => ?_]
  · have h1 : ((jacPoly (laurModel F ε β Q)).submatrix (Fin.castAdd r) (Fin.castAdd r)) =
        (jacPoly (laurRowW F ε)).map (rename (Fin.castAdd r)) := by
      refine Matrix.ext fun a b => ?_
      simp only [jacPoly, laurModel, Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply,
        Fin.addCases_left]
      rw [pderiv_rename (Fin.castAdd_injective _ _)]
    have h2 : ((jacPoly (laurModel F ε β Q)).submatrix (Fin.natAdd _) (Fin.natAdd _)) =
        Matrix.diagonal fun _ => rename (ιYL (r := r)) β := by
      refine Matrix.ext fun j j' => ?_
      simp only [jacPoly, laurModel, Matrix.submatrix_apply, Matrix.of_apply, Fin.addCases_right,
        map_sub, Derivation.leibniz, smul_eq_mul, Matrix.diagonal_apply, pderiv_X, Pi.single_apply,
        (Fin.natAdd_injective _ _).eq_iff]
      rw [pderiv_rename_eq_zero ιYL (fun x => castAdd_ne_natAdd _ j'),
        pderiv_rename_eq_zero _ (fun x => castAdd_ne_natAdd x j')]
      by_cases h : j = j'
      · simp [h]
      · simp [h]
    have h3 := AlgHom.map_det (rename (Fin.castAdd r)) (jacPoly (laurRowW F ε))
    rw [AlgHom.mapMatrix_apply] at h3
    rw [h1, h2, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← h3,
      det_laurRowW, map_mul, rename_rename, rename_X]
    rfl
  · simp only [jacPoly, laurModel, Matrix.of_apply, Fin.addCases_left]
    exact pderiv_rename_eq_zero _ (fun x => castAdd_ne_natAdd x j) _

/-- The Laurent block permutation, on sums. -/
def laurSumEquiv :
    ((Fin m ⊕ Fin 1) ⊕ Fin r) ⊕ ((Fin 1 ⊕ Fin kc) ⊕ Fin l) ≃
      ((Fin m ⊕ (Fin kc ⊕ Fin l)) ⊕ (Fin 1 ⊕ Fin 1)) ⊕ Fin r where
  toFun
    | .inl (.inl (.inl i)) => .inl (.inl (.inl i))
    | .inl (.inl (.inr t)) => .inl (.inr (.inr t))
    | .inl (.inr j) => .inr j
    | .inr (.inl (.inl a)) => .inl (.inr (.inl a))
    | .inr (.inl (.inr q)) => .inl (.inl (.inr (.inl q)))
    | .inr (.inr z) => .inl (.inl (.inr (.inr z)))
  invFun
    | .inl (.inl (.inl i)) => .inl (.inl (.inl i))
    | .inl (.inr (.inr t)) => .inl (.inl (.inr t))
    | .inr j => .inl (.inr j)
    | .inl (.inr (.inl a)) => .inr (.inl (.inl a))
    | .inl (.inl (.inr (.inl q))) => .inr (.inl (.inr q))
    | .inl (.inl (.inr (.inr z))) => .inr (.inr z)
  left_inv := by rintro (((i | t) | j) | ((a | q) | z)) <;> rfl
  right_inv := by rintro (((i | (q | z)) | (a | t)) | j) <;> rfl

/-- **The Laurent row and variable permutation**. -/
def laurPerm : Fin (((m + 1) + r) + ((1 + kc) + l)) ≃ Fin (((m + (kc + l)) + (1 + 1)) + r) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)))
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _))))).trans
  (laurSumEquiv.trans (finSumFinEquiv.symm.trans (Equiv.sumCongr
    (finSumFinEquiv.symm.trans (Equiv.sumCongr
      (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm))
      finSumFinEquiv.symm))
    (Equiv.refl _))).symm)

lemma laurPerm_eq (i : Fin m) :
    laurPerm (kc := kc) (l := l) (r := r) (Fin.castAdd _ (Fin.castAdd r (Fin.castAdd 1 i))) =
      Fin.castAdd r (Fin.castAdd (1 + 1) (Fin.castAdd (kc + l) i)) := by
  simp [laurPerm, laurSumEquiv]

lemma laurPerm_t :
    laurPerm (m := m) (kc := kc) (l := l) (r := r) (Fin.castAdd _ (Fin.castAdd r (Fin.natAdd m 0))) =
      Fin.castAdd r (Fin.natAdd (m + (kc + l)) (Fin.natAdd 1 0)) := by
  simp [laurPerm, laurSumEquiv]; rfl

lemma laurPerm_y (j : Fin r) :
    laurPerm (m := m) (kc := kc) (l := l) (Fin.castAdd _ (Fin.natAdd (m + 1) j)) = Fin.natAdd _ j := by
  simp [laurPerm, laurSumEquiv]

lemma laurPerm_s :
    laurPerm (m := m) (kc := kc) (l := l) (r := r) (Fin.natAdd _ (Fin.castAdd l (Fin.castAdd kc 0))) =
      Fin.castAdd r (Fin.natAdd (m + (kc + l)) (Fin.castAdd 1 0)) := by
  simp [laurPerm, laurSumEquiv]; rfl

lemma laurPerm_head (q : Fin kc) :
    laurPerm (m := m) (l := l) (r := r) (Fin.natAdd _ (Fin.castAdd l (Fin.natAdd 1 q))) =
      Fin.castAdd r (Fin.castAdd (1 + 1) (Fin.natAdd m (Fin.castAdd l q))) := by
  simp [laurPerm, laurSumEquiv]

lemma laurPerm_rest (z : Fin l) :
    laurPerm (m := m) (kc := kc) (r := r) (Fin.natAdd _ (Fin.natAdd (1 + kc) z)) =
      Fin.castAdd r (Fin.castAdd (1 + 1) (Fin.natAdd m (Fin.natAdd kc z))) := by
  simp [laurPerm, laurSumEquiv]

/-- **The Laurent model as a square system** (equations first). -/
noncomputable def laurSys :
    Fin (((m + 1) + r) + ((1 + kc) + l)) → MvPolynomial (Fin (((m + 1) + r) + ((1 + kc) + l))) ℤ :=
  fun i => rename laurPerm.symm (laurModel F ε β Q (laurPerm i))

/-- The Laurent model variables `Y`. -/
def lvarY (v : Fin (m + (kc + l))) : Fin (((m + 1) + r) + ((1 + kc) + l)) := laurPerm.symm (ιYL v)

/-- The Laurent model variables `(Y, s, t)`. -/
def lvarW (a : Fin ((m + (kc + l)) + (1 + 1))) : Fin (((m + 1) + r) + ((1 + kc) + l)) :=
  laurPerm.symm (Fin.castAdd r a)

/-- The Laurent model variable `s`. -/
def lvarS : Fin (((m + 1) + r) + ((1 + kc) + l)) := Fin.natAdd _ (Fin.castAdd l (Fin.castAdd kc 0))

/-- The Laurent model variable `t` (`s t = ε`). -/
def lvarT : Fin (((m + 1) + r) + ((1 + kc) + l)) := Fin.castAdd _ (Fin.castAdd r (Fin.natAdd m 0))

/-- The Laurent model variables `y`. -/
def lvarYr (j : Fin r) : Fin (((m + 1) + r) + ((1 + kc) + l)) := Fin.castAdd _ (Fin.natAdd (m + 1) j)

lemma lvarS_eq : lvarS (m := m) (kc := kc) (l := l) (r := r) =
    laurPerm.symm (Fin.castAdd r (Fin.natAdd _ (Fin.castAdd 1 0))) := by
  rw [lvarS, ← laurPerm_s, Equiv.symm_apply_apply]

lemma lvarT_eq : lvarT (m := m) (kc := kc) (l := l) (r := r) =
    laurPerm.symm (Fin.castAdd r (Fin.natAdd _ (Fin.natAdd 1 0))) := by
  rw [lvarT, ← laurPerm_t, Equiv.symm_apply_apply]

lemma lvarYr_eq (j : Fin r) :
    lvarYr (m := m) (kc := kc) (l := l) j = laurPerm.symm (Fin.natAdd _ j) := by
  rw [lvarYr, ← laurPerm_y, Equiv.symm_apply_apply]

lemma laurSys_eq (i : Fin m) :
    laurSys F ε β Q (Fin.castAdd _ (Fin.castAdd r (Fin.castAdd 1 i))) =
      rename lvarY (F (Fin.castAdd _ i)) := by
  simp only [laurSys, laurPerm_eq, laurModel, Fin.addCases_left, laurRowW, rename_rename]
  rfl

lemma laurSys_t :
    laurSys F ε β Q (Fin.castAdd _ (Fin.castAdd r (Fin.natAdd m 0))) =
      X lvarS * X lvarT - rename lvarY ε := by
  simp only [laurSys, laurPerm_t, laurModel, Fin.addCases_left, laurRowW, laurRowST,
    Fin.addCases_right, map_sub, map_mul, rename_X, rename_rename]
  rw [lvarS_eq, lvarT_eq]
  rfl

lemma laurSys_y (j : Fin r) :
    laurSys F ε β Q (Fin.castAdd _ (Fin.natAdd (m + 1) j)) =
      rename lvarY β * X (lvarYr j) - rename lvarW (Q j) := by
  simp only [laurSys, laurPerm_y, laurModel, Fin.addCases_right, map_sub, map_mul, rename_rename,
    rename_X, lvarYr_eq]
  rfl

lemma laurSys_s :
    laurSys F ε β Q (Fin.natAdd _ (Fin.castAdd l (Fin.castAdd kc 0))) = X lvarS := by
  simp only [laurSys, laurPerm_s, laurModel, Fin.addCases_left, laurRowW, laurRowST,
    Fin.addCases_right, rename_X]
  rw [lvarS_eq]

lemma laurSys_head (q : Fin kc) :
    laurSys F ε β Q (Fin.natAdd _ (Fin.castAdd l (Fin.natAdd 1 q))) =
      rename lvarY (F (Fin.natAdd m (Fin.castAdd l q))) := by
  simp only [laurSys, laurPerm_head, laurModel, Fin.addCases_left, laurRowW, rename_rename]
  rfl

lemma laurSys_rest (z : Fin l) :
    laurSys F ε β Q (Fin.natAdd _ (Fin.natAdd (1 + kc) z)) =
      rename lvarY (F (Fin.natAdd m (Fin.natAdd kc z))) := by
  simp only [laurSys, laurPerm_rest, laurModel, Fin.addCases_left, laurRowW, rename_rename]
  rfl

/-- **The Jacobian determinant of the Laurent model**: `ren(det ∂F) · s · ren(β)^r`. -/
lemma det_laurSys :
    (jacPoly (laurSys F ε β Q)).det = rename lvarY (jacPoly F).det * X lvarS * rename lvarY β ^ r := by
  show (jacPoly fun i => rename laurPerm.symm (laurModel F ε β Q (laurPerm i))).det = _
  rw [det_jacPoly_perm, det_laurModel, map_mul, map_mul, map_pow, rename_X, rename_rename,
    rename_rename, lvarS_eq]
  rfl

end Laurent

/-- **Chart data and conormal injectivity of a global presentation from the Laurent model**
(as `exists_reesChart`; model determinant `ren(det ∂F) · s · ren(β)^r`, `det_laurSys`). -/
theorem exists_laurChart {m kc l r mR : ℕ}
    (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
    (ε β : MvPolynomial (Fin (m + (kc + l))) ℤ)
    (Q : Fin r → MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ)
    (GR : List (MvPolynomial (Fin (mR + ((1 + kc) + l))) ℤ))
    (φ : Fin (mR + ((1 + kc) + l)) → MvPolynomial (Fin (((m + 1) + r) + ((1 + kc) + l))) ℤ)
    (ψ : Fin (((m + 1) + r) + ((1 + kc) + l)) → MvPolynomial (Fin (mR + ((1 + kc) + l))) ℤ)
    (dW : MvPolynomial (Fin (((m + 1) + r) + ((1 + kc) + l))) ℤ)
    (hφ : ∀ g ∈ GR, dW * aeval φ g ∈ lspan (sysEq (laurSys F ε β Q)))
    (hψ : ∀ h ∈ sysEq (laurSys F ε β Q), aeval ψ h ∈ lspan GR)
    (hround : ∀ v, X v - aeval ψ (φ v) ∈ lspan GR)
    (xT : Fin ((1 + kc) + l) → MvPolynomial (Fin (mR + ((1 + kc) + l))) ℤ)
    (b : MvPolynomial (Fin (((m + 1) + r) + ((1 + kc) + l))) ℤ)
    (hx : ∀ i, b * (aeval φ (xT i) - laurSys F ε β Q (Fin.natAdd _ i)) ∈
      lspan (sysEq (laurSys F ε β Q))) :
    (∃ T : ChartData GR, T.x = xT ∧
      T.c = aeval ψ (dW ^ 2 * (b ^ 2 * (jacPoly (laurSys F ε β Q)).det))) ∧
    ConormalInj GR (aeval ψ ((jacPoly (laurSys F ε β Q)).det * dW ^ 2)) := by
  obtain ⟨T', hx', hc'⟩ :=
    (ChartData.ofSystem (laurSys F ε β Q)).exists_coordCongr (fun i => aeval φ (xT i)) b hx
  obtain ⟨T, hT1, hT2, -⟩ := exists_chartData_transport (hψ := hψ) (hround := hround) hφ T' xT
    (fun i => by rw [hx'])
  refine ⟨⟨T, hT1, by rw [hT2, hc']; rfl⟩, ?_⟩
  obtain ⟨a, ha⟩ := exists_conormalRet_system (laurSys F ε β Q) (by omega)
  exact conormalInj_of_ret (conormalRet_transport GR _ φ ψ dW hφ hψ hround ha)

section Rename

/-! ### Renaming a presentation

The certificate of `R` is built in a layout `Fin (mR + ((1 + kc) + l))`; the natural presentation
of `R` lives in another `Fin N`. `ChartDim` is existential in the presentation, so it suffices that
renaming the variables along an equivalence gives an isomorphic presented algebra. -/

/-- The presented algebra is unchanged by renaming the variables along an equivalence. -/
noncomputable def quotRenameEquiv {N N' : ℕ} (G : List (MvPolynomial (Fin N) ℤ)) (e : Fin N ≃ Fin N') :
    MvPolynomial (Fin N) ℚ ⧸ lspan (G.map toQZ) ≃+*
      MvPolynomial (Fin N') ℚ ⧸ lspan ((G.map (rename e)).map toQZ) :=
  Ideal.quotientEquiv _ _ (renameEquiv ℚ e).toRingEquiv (by
    rw [lspan, lspan, Ideal.map_span]
    congr 1
    ext p
    simp only [List.map_map, List.mem_map, Set.mem_ofPred_eq, Set.mem_image, Function.comp_apply,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      renameEquiv_apply]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨toQZ g, ⟨g, hg, rfl⟩, by rw [map_rename]⟩
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, by rw [map_rename]⟩)

end Rename

end BezoutCounterexample.Constructive
