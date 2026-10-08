import Mathlib
import BezoutCounterexample.Principalization.ChainLiftLaurOpenPt

/-!
# Points of the Rees algebra and the multipliers of the opens (Task B, Rees layer S6, assembly)

`GR` is the global presentation of the Rees algebra (kernel of `reesVec`) and `GR' = GR.map (rename ε)` its
certificate layout. A point `P` of `QB GR'` restricts to a point `ptR P` of `A` (`Y ↦ Y`).
The multipliers `e = T.c · d` of the opens are evaluated at `P` through `ptR P`:

* `ptR`, `ptR_z`: the restriction and its values on `A`;
* `val_weighted_ne`: the weighted open's `e` is nonzero at `P` when `S.h`, `β`, `γ`, `g̃` are nonzero at
  `ptR P` and all heads of `S` vanish there (`det_reesSys_sub_mem`, `S.detc`);
* `val_laurent_ne`: the Laurent open's `e` is nonzero at `P` when `S.h` and `ε` are nonzero at `ptR P`
  (`det_laurSys`; `s(P) ≠ 0` from the row `s·Pt − ε`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

set_option linter.unusedSectionVars false

variable {A : Type} [CommRing A] [Algebra ℚ A] {m kc l r : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (gZ : Fin r → MvPolynomial (Fin (m + (kc + l))) ℤ) (δ : Fin r → ℕ)
  (GR : List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ))
  (hGR : ∀ h, aeval (reesVec G e gZ δ) h = 0 ↔ h ∈ lspan (GR.map toQZ))
  (ε : Fin ((m + (kc + l)) + (1 + r)) ≃ Fin ((m + r) + ((1 + kc) + l)))

/-- The presented ring in the certificate layout. -/
abbrev QR := MvPolynomial (Fin ((m + r) + ((1 + kc) + l))) ℚ ⧸ lspan ((GR.map (rename ε)).map toQZ)

lemma toQZ_rename_mem {N N' : ℕ} (σ : Fin N → Fin N') {L : List (MvPolynomial (Fin N) ℤ)}
    {x : MvPolynomial (Fin N) ℚ} (hx : x ∈ lspan (L.map toQZ)) :
    rename σ x ∈ lspan ((L.map (rename σ)).map toQZ) := by
  have := Ideal.mem_map_of_mem (rename σ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] _).toRingHom hx
  rw [lspan, Ideal.map_span] at this
  convert this using 2
  ext p
  simp only [List.map_map, Set.mem_ofPred_eq, List.mem_map, Function.comp_apply, Set.mem_image,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨toQZ g, ⟨g, hg, rfl⟩, by rw [map_rename]⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, by rw [map_rename]⟩

include hGR in
lemma rename_gY_mem (g : MvPolynomial (Fin (m + (kc + l))) ℤ) (hg : g ∈ lspan G) :
    toQZ (rename ε (rename gY g)) ∈ lspan ((GR.map (rename ε)).map toQZ) := by
  rw [map_rename]
  refine toQZ_rename_mem ε ((hGR _).1 ?_)
  rw [map_rename, show (gY : Fin (m + (kc + l)) → _) = Fin.castAdd (1 + r) from rfl,
    aeval_reesVec_rename]
  have : toAq G e (toQZ g) = toAZ G e g := rfl
  rw [this, toAZ_eq_zero_of_mem G e hg, map_zero]

/-- The inclusion `A → QR` (`Y ↦ Y`). -/
def inclR : A →+* QR GR ε :=
  (Ideal.Quotient.lift (lspan (G.map toQZ))
    ((Ideal.Quotient.mk _).comp (rename (fun v => ε (gY v))).toRingHom) (by
      intro x hx
      refine (Ideal.span_le.2 ?_ : _ ≤ RingHom.ker _) hx
      intro y hy
      simp only [Set.mem_ofPred_eq, List.mem_map] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      have := rename_gY_mem G e gZ δ GR hGR ε g (Ideal.subset_span hg)
      rwa [map_rename, map_rename, rename_rename] at this)).comp e.symm.toRingHom

lemma inclR_toAZ (p : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    inclR G e gZ δ GR hGR ε (toAZ G e p) =
      Ideal.Quotient.mk _ (toQZ (rename ε (rename gY p))) := by
  simp only [inclR, toAZ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [map_rename, map_rename, rename_rename]
  rfl

/-- **The restriction of a point of `R` to `A`.** -/
@[reducible] def ptR (P : Pt (QR GR ε)) : Pt A where
  L := P.L
  z := ((P.z : QR GR ε →+* P.L).comp (inclR G e gZ δ GR hGR ε)).toRatAlgHom
  dec := P.dec

lemma ptR_z (P : Pt (QR GR ε)) (p : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    (ptR G e gZ δ GR hGR ε P).z (toAZ G e p) =
      P.z (Ideal.Quotient.mk _ (toQZ (rename ε (rename gY p)))) := by
  show P.z (inclR G e gZ δ GR hGR ε (toAZ G e p)) = _
  rw [inclR_toAZ]

/-- The value at `P` of an integer polynomial in the certificate layout. -/
def valR (P : Pt (QR GR ε)) : MvPolynomial (Fin ((m + r) + ((1 + kc) + l))) ℤ →+* P.L :=
  (P.z : QR GR ε →+* P.L).comp ((Ideal.Quotient.mk _).comp toQZ)

lemma valR_rename_gY (P : Pt (QR GR ε)) (p : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    valR GR ε P (rename ε (rename gY p)) = (ptR G e gZ δ GR hGR ε P).z (toAZ G e p) := by
  rw [ptR_z]; rfl

lemma valR_mem (P : Pt (QR GR ε)) {x : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ}
    (hx : x ∈ lspan GR) : valR GR ε P (rename ε x) = 0 := by
  have h1 := rename_mem_lspan ε hx
  have h2 := toQZ_mem_lspan_map h1
  simp only [valR, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 h2, map_zero]

lemma valR_natCast_ne (P : Pt (QR GR ε)) {n : ℕ} (hn : n ≠ 0) :
    valR GR ε P (n : MvPolynomial _ ℤ) ≠ 0 := by
  have := algebraRat.charZero P.L
  rw [map_natCast]
  exact Nat.cast_ne_zero.2 hn

/-- `p ↦ q(p)` for a point `q` of `A`, as a ring hom on `ℤ[Y]`. -/
def qHom (q : Pt A) : MvPolynomial (Fin (m + (kc + l))) ℤ →+* q.L :=
  (q.z : A →+* q.L).comp (e.toRingHom.comp ((Ideal.Quotient.mk _).comp toQZ))

lemma qHom_apply (q : Pt A) (p : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    qHom G e q p = q.z (toAZ G e p) := rfl

lemma qHom_det_ne (q : Pt A) (S : SquarePiece m (kc + l) G) (hh : qHom G e q S.h ≠ 0) :
    qHom G e q (jacPoly S.F).det ≠ 0 := by
  intro h0
  have h1 : qHom G e q ((jacPoly S.F).det * S.U - S.h ^ S.e) = 0 := by
    rw [qHom_apply, toAZ_eq_zero_of_mem G e S.detc, map_zero]
  rw [map_sub, map_mul, h0, zero_mul, zero_sub, neg_eq_zero, map_pow] at h1
  exact hh (pow_eq_zero_iff'.1 h1).1

lemma ne_of_dW_det {R K : Type*} [CommRing R] [Field K] (ν : R →+* K) (dW det : R)
    (hdW : ν dW ≠ 0) (hdet : ν det ≠ 0) :
    ν (dW ^ 2 * (dW ^ 2 * det)) * ν (det * dW ^ 2) ≠ 0 := by
  simp only [map_mul, map_pow]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hdW) (mul_ne_zero (pow_ne_zero _ hdW) hdet))
    (mul_ne_zero hdet (pow_ne_zero _ hdW))

lemma ne_of_dW_det' {R K : Type*} [CommRing R] [Field K] (ν : R →+* K) (dW det : R)
    (hdW : ν dW ≠ 0) (hdet : ν det ≠ 0) :
    ν (dW ^ 2 * det) * ν (det * dW ^ 2) ≠ 0 := by
  simp only [map_mul, map_pow]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hdW) hdet) (mul_ne_zero hdet (pow_ne_zero _ hdW))

/-- The valuation through `ψ'` (the weighted model). -/
def νW (P : Pt (QR GR ε)) (Pp : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) :
    MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ →+* P.L :=
  (valR GR ε P).comp (aeval (R := ℤ) fun i => rename ε (reesψ Pp i)).toRingHom

lemma νW_varY (P : Pt (QR GR ε)) (Pp : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (f : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    νW GR ε P Pp (rename varY f) = qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε P) f := by
  simp only [νW, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [aeval_rename_comp ε (reesψ Pp), aeval_reesψ_varY, valR_rename_gY G e gZ δ GR hGR ε P, qHom_apply]

/-- **The weighted open's multiplier is nonzero at `P`** when `S.h β γ g̃` is nonzero and all heads
of `S` vanish at the restriction `q`. -/
theorem val_weighted_ne (P : Pt (QR GR ε)) (S : SquarePiece m (kc + l) G)
    (γ β gt : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ)
    (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)
    (Pp : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) (n : ℕ)
    (hne : qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε P) (S.h * (β * (γ * gt))) ≠ 0)
    (hheads : ∀ i, qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε P) (S.F (Fin.natAdd m (Fin.castAdd l i))) = 0) :
    νW GR ε P Pp
        ((((n.factorial : ℕ) : MvPolynomial _ ℤ) * rename varY (S.h * (β * (γ * gt))) ^ n) ^ 2 *
        ((((n.factorial : ℕ) : MvPolynomial _ ℤ) * rename varY (S.h * (β * (γ * gt))) ^ n) ^ 2 *
          (jacPoly (reesSys S.F γ β w Q)).det)) *
      νW GR ε P Pp ((jacPoly (reesSys S.F γ β w Q)).det *
        (((n.factorial : ℕ) : MvPolynomial _ ℤ) * rename varY (S.h * (β * (γ * gt))) ^ n) ^ 2) ≠ 0 := by
  refine ne_of_dW_det (νW GR ε P Pp) _ _ ?_ ?_
  · rw [map_mul, map_pow, νW_varY G e gZ δ GR hGR ε P Pp, map_natCast]
    refine mul_ne_zero ?_ (pow_ne_zero _ hne)
    have := valR_natCast_ne GR ε P (Nat.factorial_ne_zero n)
    rwa [map_natCast] at this
  · obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (det_reesSys_sub_mem S.F γ β w Q)
    rw [← sub_add_cancel (jacPoly (reesSys S.F γ β w Q)).det
      (rename varY (γ ^ kc * β ^ r * (jacPoly S.F).det)), ← hc, map_add, map_sum]
    simp only [map_mul, νW_varY G e gZ δ GR hGR ε P Pp, map_pow]
    simp only [hheads, mul_zero, Finset.sum_const_zero, zero_add]
    have hne' := hne
    simp only [map_mul] at hne'
    have h3 := qHom_det_ne G e (ptR G e gZ δ GR hGR ε P) S (left_ne_zero_of_mul hne')
    have hβ : qHom G e (ptR G e gZ δ GR hGR ε P) β ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hne')
    have hγ : qHom G e (ptR G e gZ δ GR hGR ε P) γ ≠ 0 :=
      left_ne_zero_of_mul (right_ne_zero_of_mul (right_ne_zero_of_mul hne'))
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hγ) (pow_ne_zero _ hβ)) h3

/-- The valuation through `ψ'` (the Laurent model). -/
def νL (P : Pt (QR GR ε)) (Pt' : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) :
    MvPolynomial (Fin (((m + 1) + r) + ((1 + kc) + l))) ℤ →+* P.L :=
  (valR GR ε P).comp (aeval (R := ℤ) fun i => rename ε (laurψ Pt' i)).toRingHom

lemma νL_varY (P : Pt (QR GR ε)) (Pt' : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (f : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    νL GR ε P Pt' (rename lvarY f) = qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε P) f := by
  simp only [νL, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [aeval_rename_comp ε (laurψ Pt'), aeval_laurψ_lvarY, valR_rename_gY G e gZ δ GR hGR ε P, qHom_apply]

lemma νL_S (P : Pt (QR GR ε)) (Pt' : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) :
    νL GR ε P Pt' (X lvarS) = valR GR ε P (rename ε (X gS)) := by
  simp only [νL, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
    laurψ_lvarS]

/-- **The Laurent open's multiplier is nonzero at `P`** when `S.h` and `εL` are nonzero at `q` and
the row `s·Pt − εL` lies in `GR`. -/
theorem val_laurent_ne (P : Pt (QR GR ε)) (S : SquarePiece m (kc + l) G) (d : ℕ)
    (εL : MvPolynomial (Fin (m + (kc + l))) ℤ) (Pt' : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (Q : Fin r → MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ) (n : ℕ)
    (hrow : X gS * Pt' - rename gY εL ∈ lspan GR)
    (hne : qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε P) (S.h * εL) ≠ 0) :
    νL GR ε P Pt'
        ((((n.factorial : ℕ) : MvPolynomial _ ℤ) * rename lvarY (S.h * (εL ^ d * εL)) ^ n) ^ 2 *
        (1 ^ 2 * (jacPoly (laurSys S.F εL (εL ^ d) Q)).det)) *
      νL GR ε P Pt' ((jacPoly (laurSys S.F εL (εL ^ d) Q)).det *
        (((n.factorial : ℕ) : MvPolynomial _ ℤ) * rename lvarY (S.h * (εL ^ d * εL)) ^ n) ^ 2) ≠ 0 := by
  set q := ptR G e gZ δ GR hGR ε P
  have hne' := hne
  rw [map_mul] at hne'
  have hh := left_ne_zero_of_mul hne'
  have hε := right_ne_zero_of_mul hne'
  have hs : νL GR ε P Pt' (X lvarS) ≠ 0 := by
    have h0 := valR_mem GR ε P hrow
    rw [map_sub, map_mul, map_sub, map_mul, valR_rename_gY G e gZ δ GR hGR ε P, ← qHom_apply] at h0
    replace h0 := sub_eq_zero.1 h0
    rw [νL_S]
    intro hz
    apply hε
    rw [← h0, hz, zero_mul]
  rw [one_pow, one_mul]
  refine ne_of_dW_det' (νL GR ε P Pt') _ _ ?_ ?_
  · rw [map_mul, map_pow, νL_varY G e gZ δ GR hGR ε P Pt', map_natCast]
    refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
    · have := valR_natCast_ne GR ε P (Nat.factorial_ne_zero n)
      rwa [map_natCast] at this
    · simp only [map_mul, map_pow]
      exact mul_ne_zero hh (mul_ne_zero (pow_ne_zero _ hε) hε)
  · rw [det_laurSys, map_mul, map_mul, map_pow, νL_varY G e gZ δ GR hGR ε P Pt', νL_varY G e gZ δ GR hGR ε P Pt']
    exact mul_ne_zero (mul_ne_zero (qHom_det_ne G e q S hh) hs) (pow_ne_zero _ (by
      rw [map_pow]; exact pow_ne_zero _ hε))

end BezoutCounterexample.Principalization
