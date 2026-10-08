import Mathlib
import BezoutCounterexample.Principalization.ChainLiftSmoothChart

/-!
# The standard-smooth presentation of a square piece (hR4b, PresentationCert)

A certified square piece `S : SquarePiece m n G` gives a submersive presentation of
`D(h) = (ℚ[Y]/(G))[1/h]` (`S.Loc`) over `ℚ`, with variables `Y_{m+n}`, `Z_n`, `t` and relations

* `F_i(Y)` for the first `m` rows (`F_eq`), `F_{m+j}(Y) − Z_j` for the `n` coordinates,
* `h(Y) · t − 1`,

each relation `i` paired with the variable `Y_i`, the last with `t`. The Jacobian is block
triangular, `det = det (∂F/∂Y) · h`, a unit on `D(h)` (`detc`). The ring of the presentation
`ℚ[Y,Z,t]/(rel)` (`T`) is identified with `S.Loc` by two explicit inverse maps (`S.equivT`): `(G)`
vanishes in `T` by `genc` (`h^f · G ⊆ (F_eq)`, `h` invertible), so no kernel is computed.

* `SquarePiece.equivT : S.T ≃+* S.Loc`;
* `SquarePiece.isStandardSmooth_T`, **`SquarePiece.smooth_loc : Algebra.Smooth ℚ S.Loc`**.

The only classical step is the section of `ℚ[Y,Z,t] → T` required by Mathlib's `Generators` (the
data `σ'`, irrelevant to the presentation), taken from `Function.Surjective.hasRightInverse` inside
a proof of a `Prop`; standard smooth ⇒ smooth is Mathlib's (Newton lifting, invertible Jacobian).
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}

/-- A ring map out of `ℚ[X]` is `aeval` of its values on the variables. -/
lemma aeval_X_ringHom {σ B : Type*} [CommRing B] [Algebra ℚ B] (f : MvPolynomial σ ℚ →+* B)
    (p : MvPolynomial σ ℚ) : aeval (fun i => f (X i)) p = f p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [aeval_C]; exact RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ B) (f.comp C)) a
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

namespace SquarePiece

variable (S : SquarePiece m n G)

/-- The variables `Y_{m+n}`, `Z_n`, `t`. -/
abbrev V (m n : ℕ) : Type := Fin (m + n) ⊕ (Fin n ⊕ Unit)

/-- The relations: one for each `Y_i`, and one for `t`. -/
abbrev Rl (m n : ℕ) : Type := Fin (m + n) ⊕ Unit

/-- An integer polynomial in `Y` as a rational polynomial in `Y, Z, t`. -/
abbrev yQ (p : MvPolynomial (Fin (m + n)) ℤ) : MvPolynomial (V m n) ℚ :=
  rename Sum.inl (toQZ p)

/-- The `Z`-part of the relation of row `i`: `0` on `F_eq`, `Z_j` on the coordinate `m + j`. -/
def zPart (i : Fin (m + n)) : MvPolynomial (V m n) ℚ :=
  Fin.addCases (fun _ => 0) (fun j => X (Sum.inr (Sum.inl j))) i

/-- The relations. -/
def rel : Rl m n → MvPolynomial (V m n) ℚ
  | Sum.inl i => yQ (S.F i) - zPart i
  | Sum.inr _ => yQ S.h * X (Sum.inr (Sum.inr ())) - 1

/-- The variable paired with a relation. -/
def amap : Rl m n → V m n
  | Sum.inl i => Sum.inl i
  | Sum.inr _ => Sum.inr (Sum.inr ())

lemma amap_injective : Function.Injective (amap (m := m) (n := n)) := by
  rintro (i | ⟨⟩) (j | ⟨⟩) h <;> simp_all [amap]

/-- The ring of the presentation. -/
abbrev T : Type := MvPolynomial (V m n) ℚ ⧸ Ideal.span (Set.range S.rel)

/-- The quotient map. -/
abbrev mkT : MvPolynomial (V m n) ℚ →+* S.T := Ideal.Quotient.mk _

lemma mkT_rel (r : Rl m n) : S.mkT (S.rel r) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨r, rfl⟩)

lemma mkT_ht : S.mkT (yQ S.h) * S.mkT (X (Sum.inr (Sum.inr ()))) = 1 := by
  have h := S.mkT_rel (Sum.inr ())
  rw [rel, map_sub, map_mul, map_one, sub_eq_zero] at h
  exact h

lemma isUnit_mkT_h : IsUnit (S.mkT (yQ S.h)) := IsUnit.of_mul_eq_one _ S.mkT_ht

lemma mkT_F_eq (a : Fin m) : S.mkT (yQ (S.F (Fin.castAdd n a))) = 0 := by
  have h := S.mkT_rel (Sum.inl (Fin.castAdd n a))
  rwa [rel, zPart, Fin.addCases_left, sub_zero] at h

lemma mkT_F_coord (j : Fin n) :
    S.mkT (yQ (S.F (Fin.natAdd m j))) = S.mkT (X (Sum.inr (Sum.inl j))) := by
  have h := S.mkT_rel (Sum.inl (Fin.natAdd m j))
  rwa [rel, zPart, Fin.addCases_right, map_sub, sub_eq_zero] at h

/-- `ℤ[Y] → T`. -/
abbrev yT : MvPolynomial (Fin (m + n)) ℤ →+* S.T :=
  S.mkT.comp ((rename Sum.inl).toRingHom.comp toQZ)

lemma yT_apply (p : MvPolynomial (Fin (m + n)) ℤ) : S.yT p = S.mkT (yQ p) := rfl

/-- `(G)` vanishes in `T`: `h^f · g ∈ (F_eq)` and `h` is invertible. -/
lemma yT_eq_zero {p : MvPolynomial (Fin (m + n)) ℤ} (hp : p ∈ lspan G) : S.yT p = 0 := by
  have hle : lspan G ≤ RingHom.ker S.yT := by
    rw [lspan, Ideal.span_le]
    intro g hg
    have hFe : lspan (List.ofFn fun i : Fin m => S.F (Fin.castAdd n i)) ≤ RingHom.ker S.yT := by
      rw [lspan, Ideal.span_le]
      intro x hx
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
      exact RingHom.mem_ker.2 (S.mkT_F_eq a)
    have h0 := RingHom.mem_ker.1 (hFe (S.genc g hg))
    rw [map_mul, map_pow] at h0
    exact RingHom.mem_ker.2 ((S.isUnit_mkT_h.pow S.f).mul_right_eq_zero.1 h0)
  exact RingHom.mem_ker.1 (hle hp)

/-- `ℚ[Y] → T`. -/
abbrev yTQ : MvPolynomial (Fin (m + n)) ℚ →+* S.T := S.mkT.comp (rename Sum.inl).toRingHom

lemma aeval_yTQ (p : MvPolynomial (Fin (m + n)) ℚ) :
    aeval (fun i => S.mkT (X (Sum.inl i))) p = S.yTQ p := by
  rw [← aeval_X_ringHom S.yTQ p]
  simp

/-- `ℚ[Y]/(G) → T`. -/
def qbT : SmoothCert.QB G →+* S.T :=
  Ideal.Quotient.lift _ S.yTQ (by
    have hle : lspan (G.map toQZ) ≤ RingHom.ker S.yTQ := by
      rw [lspan, Ideal.span_le]
      intro x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
      exact RingHom.mem_ker.2 (S.yT_eq_zero (Ideal.subset_span hg))
    exact fun a ha => RingHom.mem_ker.1 (hle ha))

lemma qbT_mkQ (p : MvPolynomial (Fin (m + n)) ℤ) : S.qbT (mkQ G p) = S.yT p := by
  rw [qbT, Ideal.Quotient.lift_mk]; rfl

lemma qbT_mk (p : MvPolynomial (Fin (m + n)) ℚ) :
    S.qbT (Ideal.Quotient.mk _ p) = S.mkT (rename Sum.inl p) := by
  rw [qbT, Ideal.Quotient.lift_mk]; rfl

/-- `D(h) → T`. -/
def locT : S.Loc →+* S.T :=
  IsLocalization.Away.lift (mkQ G S.h) (g := S.qbT) (by rw [qbT_mkQ]; exact S.isUnit_mkT_h)

lemma locT_algebraMap (x : SmoothCert.QB G) : S.locT (algebraMap _ S.Loc x) = S.qbT x :=
  IsLocalization.Away.lift_eq _ _ x

/-- The values of the variables in `D(h)`. -/
def val : V m n → S.Loc
  | Sum.inl i => S.img (X i)
  | Sum.inr (Sum.inl j) => S.φ (S.F (Fin.natAdd m j))
  | Sum.inr (Sum.inr _) => IsLocalization.Away.invSelf (mkQ G S.h)

lemma aeval_val_inl (p : MvPolynomial (Fin (m + n)) ℚ) :
    aeval S.val (rename Sum.inl p) = S.img p := by
  rw [aeval_rename, ← aeval_X_ringHom S.img p]; rfl

lemma aeval_yQ (p : MvPolynomial (Fin (m + n)) ℤ) : aeval S.val (yQ p) = S.φ p := by
  rw [yQ, aeval_val_inl]; rfl

/-- `T → D(h)`. -/
def tLoc : S.T →+* S.Loc :=
  Ideal.Quotient.lift _ (aeval S.val).toRingHom (by
    have hle : Ideal.span (Set.range S.rel) ≤ RingHom.ker (aeval S.val).toRingHom := by
      rw [Ideal.span_le]
      rintro _ ⟨r, rfl⟩
      refine RingHom.mem_ker.2 ?_
      rcases r with i | ⟨⟩
      · rw [rel, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, aeval_yQ, sub_eq_zero]
        refine Fin.addCases (fun a => ?_) (fun j => ?_) i
        · rw [zPart, Fin.addCases_left, map_zero]
          exact S.φ_eq_zero (S.eqmem a)
        · rw [zPart, Fin.addCases_right, aeval_X]; rfl
      · rw [rel, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_mul, aeval_yQ, aeval_X,
          map_one, sub_eq_zero]
        exact IsLocalization.Away.mul_invSelf (mkQ G S.h)
    exact fun a ha => RingHom.mem_ker.1 (hle ha))

lemma tLoc_mkT (p : MvPolynomial (V m n) ℚ) : S.tLoc (S.mkT p) = aeval S.val p := by
  rw [tLoc, Ideal.Quotient.lift_mk]; rfl

lemma tLoc_locT : S.tLoc.comp S.locT = RingHom.id _ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (mkQ G S.h)) ?_
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [locT_algebraMap, qbT_mk, tLoc_mkT, aeval_val_inl]; rfl

lemma locT_tLoc : S.locT.comp S.tLoc = RingHom.id _ := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_))
  · exact RingHom.congr_fun (RingHom.ext_rat ((S.locT.comp S.tLoc).comp (S.mkT.comp C))
      ((RingHom.id _).comp (S.mkT.comp C))) r
  · simp only [RingHom.comp_apply, RingHom.id_apply, tLoc_mkT, aeval_X]
    rcases v with i | j | ⟨⟩
    · rw [val, img, RingHom.comp_apply, locT_algebraMap, qbT_mk, rename_X]
    · rw [val, φ, img, RingHom.comp_apply, RingHom.comp_apply, locT_algebraMap]
      exact (S.qbT_mkQ _).trans (S.mkT_F_coord j)
    · rw [val]
      have hu : S.locT (algebraMap _ S.Loc (mkQ G S.h)) *
          S.locT (IsLocalization.Away.invSelf (mkQ G S.h)) = 1 := by
        rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      rw [locT_algebraMap, qbT_mkQ, yT_apply] at hu
      exact (S.isUnit_mkT_h.mul_left_cancel (hu.trans S.mkT_ht.symm))

/-- **`T ≅ D(h)`.** -/
def equivT : S.T ≃+* S.Loc :=
  RingEquiv.ofRingHom S.tLoc S.locT S.tLoc_locT S.locT_tLoc

lemma equivT_mkT_yQ (p : MvPolynomial (Fin (m + n)) ℤ) : S.equivT (S.mkT (yQ p)) = S.φ p := by
  change S.tLoc (S.mkT (yQ p)) = S.φ p
  rw [tLoc_mkT, aeval_yQ]

/-- The Jacobian of the relations is `det (∂F/∂Y) · h`, at the polynomial level. -/
lemma pderiv_yQ_inl (i : Fin (m + n)) (p : MvPolynomial (Fin (m + n)) ℤ) :
    pderiv (Sum.inl i : V m n) (yQ p) = yQ (pderiv i p) := by
  rw [yQ, yQ, pderiv_rename Sum.inl_injective]
  congr 1
  exact pderiv_map (φ := Int.castRingHom ℚ) (f := p) (i := i)

lemma pderiv_inr_rename (v : Fin n ⊕ Unit) (p : MvPolynomial (Fin (m + n)) ℚ) :
    pderiv (Sum.inr v : V m n) (rename Sum.inl p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, pderiv_X]

lemma pderiv_inl_zPart (i j : Fin (m + n)) : pderiv (Sum.inl i : V m n) (zPart j) = 0 := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j
  · rw [zPart, Fin.addCases_left, map_zero]
  · rw [zPart, Fin.addCases_right]; simp [pderiv_X]

lemma pderiv_inr_zPart (j : Fin (m + n)) : pderiv (Sum.inr (Sum.inr ()) : V m n) (zPart j) = 0 := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j
  · rw [zPart, Fin.addCases_left, map_zero]
  · rw [zPart, Fin.addCases_right]; simp [pderiv_X]

/-- `ℤ[Y] → ℚ[Y, Z, t]`, as a ring map. -/
abbrev yQh : MvPolynomial (Fin (m + n)) ℤ →+* MvPolynomial (V m n) ℚ :=
  (rename Sum.inl).toRingHom.comp toQZ

/-- The Jacobian matrix of the relations against their paired variables. -/
def J : Matrix (Rl m n) (Rl m n) (MvPolynomial (V m n) ℚ) :=
  fun i j => pderiv (amap i) (S.rel j)

/-- **The Jacobian is `det (∂F/∂Y) · h`** (block triangular). -/
lemma det_J : S.J.det = yQ ((jacPoly S.F).det * S.h) := by
  have h21 : S.J.toBlocks₂₁ = 0 := by
    refine Matrix.ext fun u j => ?_
    cases u
    simp only [Matrix.toBlocks₂₁, J, amap, rel, Matrix.of_apply, Matrix.zero_apply, map_sub,
      pderiv_inr_zPart, sub_zero]
    exact pderiv_inr_rename _ _
  have h11 : S.J.toBlocks₁₁ = Matrix.transpose ((jacPoly S.F).map yQh) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.toBlocks₁₁, J, amap, rel, Matrix.of_apply, map_sub, pderiv_inl_zPart,
      sub_zero, pderiv_yQ_inl, Matrix.transpose_apply, Matrix.map_apply, jacPoly]
    rfl
  have h22 : S.J.toBlocks₂₂.det = yQ S.h := by
    rw [Matrix.det_unique]
    simp only [Matrix.toBlocks₂₂, J, amap, rel, Matrix.of_apply, map_sub, Derivation.leibniz,
      pderiv_X, Pi.single_apply, ite_true, smul_eq_mul]
    rw [yQ, pderiv_inr_rename, Derivation.map_one_eq_zero]
    ring
  have hd : yQh (jacPoly S.F).det = ((jacPoly S.F).map yQh).det := RingHom.map_det _ _
  rw [← Matrix.fromBlocks_toBlocks S.J, h21, Matrix.det_fromBlocks_zero₂₁, h11, h22,
    Matrix.det_transpose, ← hd, yQ, yQ, map_mul toQZ, map_mul (rename _)]
  rfl

lemma isUnit_mkT_det : IsUnit (S.mkT (yQ ((jacPoly S.F).det * S.h))) := by
  rw [← isUnit_map_iff S.equivT, equivT_mkT_yQ, map_mul]
  refine IsUnit.mul ?_ S.isUnit_φ_h
  have h := S.dinv_mul
  have hd : S.φ (jacPoly S.F).det = ((jacPoly S.F).map S.φ).det := RingHom.map_det _ _
  rw [JS, ← hd] at h
  exact IsUnit.of_mul_eq_one_right _ h

/-- **`T` is standard smooth over `ℚ`**: the naive presentation is submersive. The section of
`ℚ[Y,Z,t] → T` (Mathlib's `Generators.σ'`) comes from `hasRightInverse`, inside the proof. -/
theorem isStandardSmooth_T : Algebra.IsStandardSmooth ℚ S.T := by
  obtain ⟨s, hs⟩ := (Ideal.Quotient.mk_surjective (I := Ideal.span (Set.range S.rel))).hasRightInverse
  let P := Algebra.PreSubmersivePresentation.naive (v := S.rel) amap amap_injective s hs
  have hJ : P.jacobian = S.mkT (yQ ((jacPoly S.F).det * S.h)) := by
    rw [P.jacobian_eq_jacobiMatrix_det, ← det_J]
    have hm : P.jacobiMatrix = S.J := by
      ext i j
      rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive]; rfl
    rw [hm, Algebra.Generators.algebraMap_apply]
    exact aeval_X_ringHom S.mkT _
  exact Algebra.SubmersivePresentation.isStandardSmooth
    { toPreSubmersivePresentation := P, jacobian_isUnit := hJ ▸ S.isUnit_mkT_det }

/-- **`D(h)` is smooth over `ℚ`.** -/
theorem smooth_loc : Algebra.Smooth ℚ S.Loc := by
  have := S.isStandardSmooth_T
  exact Algebra.Smooth.of_equiv S.equivT.toRatAlgEquiv

end SquarePiece

end BezoutCounterexample.Constructive
