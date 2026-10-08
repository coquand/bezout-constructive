import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesL3
import BezoutCounterexample.Constructive.ChainLiftReesOpen

/-!
# L3 assembly: the local kernel equality of the weighted-chart model (Task B, S5c, L3-b/L3-d)

Plan: `docs/pending/rees-cert-design.md` §11. The model ring is `MR = ℚ[W] ⧸ (sysEq Sys)`,
`Sys = reesSys F γ β w Q`. The `A`-piece `F` presents `A ≅ ℚ[Y] ⧸ (G)` near `D(h)` (`h^f G ⊆ (F_eq)`).

* L3-b `ptAQ`: a point of `MR` where `h` does not vanish gives a point of `A` (`ζ_A = ζ ∘ Y`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] [Algebra ℚ A] {m kc l r : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (γ β : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ)
  (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)

/-- The model ring `ℚ[W] ⧸ (sysEq Sys)`. -/
abbrev MR := SmoothCert.QB (sysEq (reesSys F γ β w Q))

/-- The model image of a rational polynomial in `Y`. -/
def mYq (p : MvPolynomial (Fin (m + (kc + l))) ℚ) : MR F γ β w Q :=
  Ideal.Quotient.mk _ (rename (varY (r := r)) p)

lemma mYq_hom : (fun p => mYq F γ β w Q p) =
    ((Ideal.Quotient.mk _).comp (rename (varY (r := r))).toRingHom : _ →+* MR F γ β w Q) := rfl

omit [Algebra ℚ A] in
/-- `toQZ` maps the integer ideal into the rational one. -/
lemma toQZ_mem_lspan_map {σ : Type*} {L : List (MvPolynomial σ ℤ)} {x : MvPolynomial σ ℤ}
    (hx : x ∈ lspan L) : toQZ x ∈ lspan (L.map toQZ) := by
  have h2 := Ideal.mem_map_of_mem (toQZ (σ := σ)) hx
  rw [lspan, Ideal.map_span] at h2
  convert h2 using 2
  ext y; simp

/-- The `A`-equations of the piece vanish in the model ring. -/
lemma mYq_feq (p : MvPolynomial (Fin (m + (kc + l))) ℤ)
    (hp : p ∈ lspan (List.ofFn fun i : Fin m => F (Fin.castAdd (kc + l) i))) :
    mYq F γ β w Q (toQZ p) = 0 := by
  rw [mYq, Ideal.Quotient.eq_zero_iff_mem, toQZ, ← map_rename]
  refine toQZ_mem_lspan_map ?_
  have := rename_mem_lspan (varY (r := r)) hp
  refine (Ideal.span_le.2 ?_) this
  intro x hx
  simp only [List.map_ofFn, Set.mem_ofPred_eq, List.mem_ofFn, Function.comp_apply] at hx
  obtain ⟨i, rfl⟩ := hx
  refine Ideal.subset_span ?_
  show _ ∈ sysEq (reesSys F γ β w Q)
  rw [← reesSys_eq F γ β w Q i]
  exact List.mem_ofFn.2 ⟨Fin.castAdd r (Fin.castAdd kc i), rfl⟩

section PtA

variable (h : MvPolynomial (Fin (m + (kc + l))) ℤ) (f : ℕ)
  (hgen : ∀ g ∈ G, h ^ f * g ∈ lspan (List.ofFn fun i : Fin m => F (Fin.castAdd (kc + l) i)))
  (P : Pt (MR F γ β w Q)) (hh : P.z (mYq F γ β w Q (toQZ h)) ≠ 0)

/-- The ring map `A → κ(P)` of L3-b. -/
def ptAHom : A →+* P.L :=
  (Ideal.Quotient.lift (lspan (G.map toQZ))
      ((P.z : MR F γ β w Q →+* P.L).comp
        ((Ideal.Quotient.mk _).comp (rename (varY (r := r))).toRingHom)) (by
      intro x hx
      refine (Ideal.span_le.2 ?_ : _ ≤ RingHom.ker _) hx
      intro y hy
      simp only [Set.mem_ofPred_eq, List.mem_map] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have h0 := congrArg P.z (mYq_feq F γ β w Q _ (hgen g hg))
      show P.z (mYq F γ β w Q (toQZ g)) = 0
      simp only [mYq, map_mul, map_pow, map_zero] at h0 hh ⊢
      exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hh))).comp
    e.symm.toRingHom

lemma ptAHom_apply (p : MvPolynomial (Fin (m + (kc + l))) ℚ) :
    ptAHom G e F γ β w Q h f hgen P hh (e (Ideal.Quotient.mk _ p)) = P.z (mYq F γ β w Q p) := by
  simp only [ptAHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
  rfl

/-- **L3-b: a point of the model ring off `V(h)` gives a point of `A`.** -/
def ptAQ : Pt A where
  L := P.L
  z := (ptAHom G e F γ β w Q h f hgen P hh).toRatAlgHom
  dec := P.dec

lemma ptA_z (p : MvPolynomial (Fin (m + (kc + l))) ℚ) :
    (ptAQ G e F γ β w Q h f hgen P hh).z (e (Ideal.Quotient.mk _ p)) = P.z (mYq F γ β w Q p) :=
  ptAHom_apply G e F γ β w Q h f hgen P hh p

end PtA

/-! ### L3-d: the localisation chain at a point -/

section Chain

variable (h : MvPolynomial (Fin (m + (kc + l))) ℤ) (f : ℕ)
  (hgen : ∀ g ∈ G, h ^ f * g ∈ lspan (List.ofFn fun i : Fin m => F (Fin.castAdd (kc + l) i)))
  (dA ch : MvPolynomial (Fin (m + (kc + l))) ℤ) (hdh : dA = h * ch)

/-- `A`'s element of an integer polynomial. -/
def toAZ (p : MvPolynomial (Fin (m + (kc + l))) ℤ) : A := e (Ideal.Quotient.mk _ (toQZ p))

/-- The model image of `d`. -/
abbrev dM : MR F γ β w Q := mYq F γ β w Q (toQZ dA)

/-- `MR[1/d]`. -/
abbrev Md := Localization.Away (dM F γ β w Q dA)

include hdh in
lemma isUnit_h_Md : IsUnit (algebraMap (MR F γ β w Q) (Md F γ β w Q dA) (mYq F γ β w Q (toQZ h))) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Md F γ β w Q dA) (dM F γ β w Q dA)
  have hd : dM F γ β w Q dA = mYq F γ β w Q (toQZ h) * mYq F γ β w Q (toQZ ch) := by
    simp only [dM, mYq, hdh, map_mul]
  have h2 : algebraMap (MR F γ β w Q) (Md F γ β w Q dA) (dM F γ β w Q dA) =
      algebraMap _ (Md F γ β w Q dA) (mYq F γ β w Q (toQZ h)) *
        algebraMap _ (Md F γ β w Q dA) (mYq F γ β w Q (toQZ ch)) := by rw [← map_mul, ← hd]
  rw [h2] at hu
  exact isUnit_of_mul_isUnit_left hu

include hgen hdh in
/-- `A → MR[1/d]` (the piece presents `A` on `D(h)`). -/
def φAd : A →+* Md F γ β w Q dA :=
  (Ideal.Quotient.lift (lspan (G.map toQZ))
      ((algebraMap (MR F γ β w Q) (Md F γ β w Q dA)).comp
        ((Ideal.Quotient.mk _).comp (rename (varY (r := r))).toRingHom)) (by
      intro x hx
      refine (Ideal.span_le.2 ?_ : _ ≤ RingHom.ker _) hx
      intro y hy
      simp only [Set.mem_ofPred_eq, List.mem_map] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have h0 := congrArg (algebraMap (MR F γ β w Q) (Md F γ β w Q dA))
        (mYq_feq F γ β w Q _ (hgen g hg))
      have hu := isUnit_h_Md F γ β w Q h dA ch hdh
      show algebraMap _ _ (mYq F γ β w Q (toQZ g)) = 0
      simp only [mYq, map_mul, map_pow, map_zero] at h0 hu ⊢
      exact (hu.pow f).mul_right_eq_zero.1 h0)).comp
    e.symm.toRingHom

lemma φAd_apply (p : MvPolynomial (Fin (m + (kc + l))) ℚ) :
    φAd G e F γ β w Q h f hgen dA ch hdh (e (Ideal.Quotient.mk _ p)) =
      algebraMap _ (Md F γ β w Q dA) (mYq F γ β w Q p) := by
  simp only [φAd, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
  rfl

variable (q : Pt A)

/-- `MR[1/d]` localised at the image of `A ∖ q`. -/
abbrev NN := Localization ((q.ker.primeCompl).map (φAd G e F γ β w Q h f hgen dA ch hdh))

/-- `A_q → N`. -/
def ιN : Localization.AtPrime q.ker →+* NN G e F γ β w Q h f hgen dA ch hdh q :=
  IsLocalization.lift (M := q.ker.primeCompl)
    (g := (algebraMap _ (NN G e F γ β w Q h f hgen dA ch hdh q)).comp (φAd G e F γ β w Q h f hgen dA ch hdh))
    fun a => IsLocalization.map_units (NN G e F γ β w Q h f hgen dA ch hdh q)
      (⟨φAd G e F γ β w Q h f hgen dA ch hdh a, Submonoid.mem_map_of_mem _ a.2⟩ :
        (q.ker.primeCompl).map (φAd G e F γ β w Q h f hgen dA ch hdh))

/-- `ℚ[W] → N`. -/
def ΘN : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℚ →+* NN G e F γ β w Q h f hgen dA ch hdh q :=
  (algebraMap (Md F γ β w Q dA) _).comp ((algebraMap (MR F γ β w Q) _).comp (Ideal.Quotient.mk _))

lemma ιN_alg (p : MvPolynomial (Fin (m + (kc + l))) ℚ) :
    ιN G e F γ β w Q h f hgen dA ch hdh q (algebraMap A _ (e (Ideal.Quotient.mk _ p))) =
      ΘN G e F γ β w Q h f hgen dA ch hdh q (rename varY p) := by
  rw [ιN, IsLocalization.lift_eq, RingHom.comp_apply, φAd_apply]
  rfl

lemma ΘN_sys {x : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ}
    (hx : x ∈ lspan (sysEq (reesSys F γ β w Q))) : ΘN G e F γ β w Q h f hgen dA ch hdh q (toQZ x) = 0 := by
  simp only [ΘN, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (toQZ_mem_lspan_map hx), map_zero]

lemma mem_sysEq (i : Fin ((m + kc) + r)) :
    reesSys F γ β w Q (Fin.castAdd _ i) ∈ lspan (sysEq (reesSys F γ β w Q)) :=
  Ideal.subset_span (List.mem_ofFn.2 ⟨i, rfl⟩)

/-- The heads of the model at `q`: `γ x̃ᵢ` in `A_q`. -/
def xq (i : Fin kc) : Localization.AtPrime q.ker :=
  algebraMap A _ (toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i))))

/-- `κ : A_q[s, u] → N`, `s ↦ s`, `uᵢ ↦ u'ᵢ`. -/
def κN : MvPolynomial (Option (Fin kc)) (Localization.AtPrime q.ker) →+* NN G e F γ β w Q h f hgen dA ch hdh q :=
  eval₂Hom (ιN G e F γ β w Q h f hgen dA ch hdh q) fun o =>
    o.elim (ΘN G e F γ β w Q h f hgen dA ch hdh q (X varS))
      (fun i => ΘN G e F γ β w Q h f hgen dA ch hdh q (X (varU i)))

/-- **K1**: `κ` kills the relations `γ x̃ᵢ − s^{wᵢ} uᵢ` (the head rows of the model). -/
lemma κN_lRel (i : Fin kc) :
    κN G e F γ β w Q h f hgen dA ch hdh q (lRel (xq G e F γ q) w i) = 0 := by
  have hrow := ΘN_sys G e F γ β w Q h f hgen dA ch hdh q
    (mem_sysEq F γ β w Q (Fin.castAdd r (Fin.natAdd m i)))
  rw [reesSys_head] at hrow
  simp only [map_sub, map_mul, map_pow, MvPolynomial.map_X, MvPolynomial.map_rename] at hrow
  simp only [κN, lRel, map_sub, map_mul, map_pow, eval₂Hom_C, eval₂Hom_X', Option.elim, xq, toAZ,
    ιN_alg]
  exact hrow

/-! #### K2: the substituted polynomial -/

variable (hβq : toAZ G e β ∉ q.ker)

/-- `β⁻¹` in `A_q`, explicitly. -/
def βinv : Localization.AtPrime q.ker :=
  IsLocalization.mk' (Localization.AtPrime q.ker) (1 : A)
    (⟨toAZ G e β, hβq⟩ : q.ker.primeCompl)

/-- `W = (s, u', Y) ↦ (s, u, Y)` over `A_q`. -/
def Wsub : Fin ((1 + kc) + (m + (kc + l))) → MvPolynomial (Option (Fin kc)) (Localization.AtPrime q.ker) :=
  Fin.addCases (Fin.addCases (fun _ => X none) (fun i => X (some i)))
    (fun v => C (algebraMap A _ (e (Ideal.Quotient.mk _ (X v)))))

/-- The global variables: `Y ↦ Y`, `s ↦ s`, `yⱼ ↦ β⁻¹ Qⱼ(s, u, Y)`. -/
def Gsub : Fin ((m + (kc + l)) + (1 + r)) → MvPolynomial (Option (Fin kc)) (Localization.AtPrime q.ker) :=
  Fin.addCases (fun v => C (algebraMap A _ (e (Ideal.Quotient.mk _ (X v)))))
    (Fin.addCases (fun _ => X none) (fun j => C (βinv G e β q hβq) * aeval (Wsub G e q) (Q j)))

/-- Ring homs out of integer polynomials agree on constants. -/
lemma intHom_C {σ R : Type*} [Ring R] (φ ψ : MvPolynomial σ ℤ →+* R) (n : ℤ) :
    φ (C n) = ψ (C n) :=
  RingHom.congr_fun (RingHom.ext_int (φ.comp C) (ψ.comp C)) n

lemma Wsub_s (o : Fin 1) : Wsub G e q (Fin.castAdd _ (Fin.castAdd kc o)) = X none := by
  simp [Wsub]
lemma Wsub_u (i : Fin kc) : Wsub G e q (Fin.castAdd _ (Fin.natAdd 1 i)) = X (some i) := by
  simp [Wsub]
lemma Wsub_Y (v : Fin (m + (kc + l))) : Wsub G e q (Fin.natAdd (1 + kc) v) =
    C (algebraMap A _ (e (Ideal.Quotient.mk _ (X v)))) := by
  simp [Wsub]
lemma Gsub_Y (v : Fin (m + (kc + l))) : Gsub G e β Q q hβq (Fin.castAdd (1 + r) v) =
    C (algebraMap A _ (e (Ideal.Quotient.mk _ (X v)))) := by
  simp [Gsub]
lemma Gsub_s (o : Fin 1) : Gsub G e β Q q hβq (Fin.natAdd _ (Fin.castAdd r o)) = X none := by
  simp [Gsub]
lemma Gsub_y (j : Fin r) : Gsub G e β Q q hβq (Fin.natAdd _ (Fin.natAdd 1 j)) =
    C (βinv G e β q hβq) * aeval (Wsub G e q) (Q j) := by
  simp [Gsub]

omit [Algebra ℚ A] in
lemma toQZ_rename {σ τ : Type*} (g : σ → τ) (p : MvPolynomial σ ℤ) :
    toQZ (rename g p) = rename g (toQZ p) := MvPolynomial.map_rename _ _ _

lemma κN_C (a : Localization.AtPrime q.ker) :
    κN G e F γ β w Q h f hgen dA ch hdh q (C a) = ιN G e F γ β w Q h f hgen dA ch hdh q a :=
  eval₂Hom_C _ _ _

lemma κN_s : κN G e F γ β w Q h f hgen dA ch hdh q (X none) =
    ΘN G e F γ β w Q h f hgen dA ch hdh q (X varS) := eval₂Hom_X' _ _ _

lemma κN_u (i : Fin kc) : κN G e F γ β w Q h f hgen dA ch hdh q (X (some i)) =
    ΘN G e F γ β w Q h f hgen dA ch hdh q (X (varU i)) := eval₂Hom_X' _ _ _

lemma κN_Wsub (P : MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ) :
    κN G e F γ β w Q h f hgen dA ch hdh q (aeval (Wsub G e q) P) =
      ΘN G e F γ β w Q h f hgen dA ch hdh q (toQZ (rename (varW (r := r)) P)) := by
  show ((κN G e F γ β w Q h f hgen dA ch hdh q).comp (aeval (Wsub G e q)).toRingHom) P =
    ((ΘN G e F γ β w Q h f hgen dA ch hdh q).comp (toQZ.comp (rename (varW (r := r))).toRingHom)) P
  congr 1
  refine MvPolynomial.ringHom_ext (fun n => intHom_C _ _ n) (fun v => ?_)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, rename_X,
    MvPolynomial.map_X]
  refine Fin.addCases ?_ ?_ v
  · intro a
    refine Fin.addCases ?_ ?_ a
    · intro o; rw [Wsub_s, κN_s, varW_s]
    · intro i; rw [Wsub_u, κN_u, varW_u]
  · intro v; rw [Wsub_Y, κN_C, ιN_alg, rename_X, varW_Y]

include hβq in
lemma ιN_βinv : ιN G e F γ β w Q h f hgen dA ch hdh q (βinv G e β q hβq) *
    ΘN G e F γ β w Q h f hgen dA ch hdh q (toQZ (rename varY β)) = 1 := by
  rw [toQZ_rename, ← ιN_alg, ← map_mul, βinv]
  rw [show (algebraMap A (Localization.AtPrime q.ker) (e (Ideal.Quotient.mk _ (toQZ β)))) =
    algebraMap A _ (toAZ G e β) from rfl, IsLocalization.mk'_spec, map_one, map_one]

include hβq in
/-- **K2**: `κ(p_q(g))` is the class of `g(Y, s, y)` in `N`. -/
lemma κN_Gsub (g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) :
    κN G e F γ β w Q h f hgen dA ch hdh q (aeval (Gsub G e β Q q hβq) g) =
      ΘN G e F γ β w Q h f hgen dA ch hdh q (toQZ (aeval reesφ g)) := by
  show ((κN G e F γ β w Q h f hgen dA ch hdh q).comp (aeval (Gsub G e β Q q hβq)).toRingHom) g =
    ((ΘN G e F γ β w Q h f hgen dA ch hdh q).comp (toQZ.comp (aeval reesφ).toRingHom)) g
  congr 1
  refine MvPolynomial.ringHom_ext (fun n => intHom_C _ _ n) (fun v => ?_)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  refine Fin.addCases ?_ ?_ v
  · intro v
    rw [Gsub_Y, κN_C, ιN_alg, rename_X, show (Fin.castAdd (1 + r) v : Fin ((m + (kc + l)) + (1 + r))) = gY v
      from rfl, reesφ_Y, MvPolynomial.map_X]
  intro v
  refine Fin.addCases ?_ ?_ v
  · intro o
    rw [Gsub_s, κN_s, show (Fin.natAdd (m + (kc + l)) (Fin.castAdd r o) : Fin ((m + (kc + l)) + (1 + r))) = gS
      by rw [Subsingleton.elim o 0]; rfl, reesφ_S, MvPolynomial.map_X]
  · intro j
    rw [Gsub_y, map_mul, κN_C, κN_Wsub]
    have hrow := ΘN_sys G e F γ β w Q h f hgen dA ch hdh q
      (mem_sysEq F γ β w Q (Fin.natAdd (m + kc) j))
    rw [reesSys_y, map_sub, map_sub, sub_eq_zero] at hrow
    rw [← hrow, map_mul, map_mul, ← mul_assoc, ιN_βinv, one_mul,
      show (Fin.natAdd (m + (kc + l)) (Fin.natAdd 1 j) : Fin ((m + (kc + l)) + (1 + r))) = gYr j
      from rfl, reesφ_y]

/-! #### K3: the Laurent image of the substituted polynomial -/

section K3

open LaurentPolynomial hiding C

variable (Ly : Fin r → A[T;T⁻¹])

/-- The global map `(Y, s, y) ↦ (Y, T⁻¹, Ly)` into `A[T^±]`. -/
def evG : Fin ((m + (kc + l)) + (1 + r)) → A[T;T⁻¹] :=
  Fin.addCases (fun v => LaurentPolynomial.C (e (Ideal.Quotient.mk _ (X v))))
    (Fin.addCases (fun _ => T (-1)) Ly)

/-- `(s, u', Y) ↦ (T⁻¹, C(γ x̃) T^w, Y)` into `A[T^±]`. -/
def evW : Fin ((1 + kc) + (m + (kc + l))) → A[T;T⁻¹] :=
  Fin.addCases (Fin.addCases (fun _ => T (-1))
      (fun i => LaurentPolynomial.C (toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i)))) * T (w i)))
    (fun v => LaurentPolynomial.C (e (Ideal.Quotient.mk _ (X v))))

/-- The unit `T` of `S[T^±]`. -/
def unitT (S : Type*) [CommRing S] : (S[T;T⁻¹])ˣ where
  val := T 1
  inv := T (-1)
  val_inv := by rw [← T_add]; simp
  inv_val := by rw [← T_add]; simp

/-- `A[T^±] → A_q[T^±]`. -/
def mapL : A[T;T⁻¹] →+* (Localization.AtPrime q.ker)[T;T⁻¹] :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp (algebraMap A _)) (unitT _)

lemma mapL_C (a : A) : mapL q (LaurentPolynomial.C a) = LaurentPolynomial.C (algebraMap A _ a) := by
  simp [mapL]

lemma mapL_T (n : ℤ) : mapL q (T n) = T n := by
  rw [mapL, LaurentPolynomial.eval₂_T]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add, zpow_one, Units.val_mul, ih, T_add]; rfl
  | pred n ih => rw [zpow_sub, zpow_one, Units.val_mul, ih, sub_eq_add_neg, T_add]; rfl

lemma lGen_Wsub (P : MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ) :
    aeval (lGen (xq G e F γ q) w) (aeval (Wsub G e q) P) = mapL q (aeval (evW G e F γ w) P) := by
  show ((aeval (lGen (xq G e F γ q) w)).toRingHom.comp (aeval (Wsub G e q)).toRingHom) P =
    ((mapL q).comp (aeval (evW G e F γ w)).toRingHom) P
  congr 1
  refine MvPolynomial.ringHom_ext (fun n => intHom_C _ _ n) (fun v => ?_)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  refine Fin.addCases ?_ ?_ v
  · intro a
    refine Fin.addCases ?_ ?_ a
    · intro o; rw [Wsub_s]; simp [evW, lGen, mapL_T]
    · intro i
      rw [Wsub_u]
      simp only [evW, Fin.addCases_left, Fin.addCases_right, aeval_X, lGen, Option.elim, map_mul,
        mapL_C, mapL_T, xq]
  · intro v
    rw [Wsub_Y]
    simp only [evW, Fin.addCases_right, aeval_C, mapL_C]
    rfl

include hβq in
/-- **K3**: the Laurent image of `p_q(g)` is the image of `g(Y, T⁻¹, Ly)`. -/
lemma lGen_Gsub (hy : ∀ j, LaurentPolynomial.C (toAZ G e β) * Ly j = aeval (evW G e F γ w) (Q j))
    (g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) :
    aeval (lGen (xq G e F γ q) w) (aeval (Gsub G e β Q q hβq) g) = mapL q (aeval (evG G e Ly) g) := by
  show ((aeval (lGen (xq G e F γ q) w)).toRingHom.comp (aeval (Gsub G e β Q q hβq)).toRingHom) g =
    ((mapL q).comp (aeval (evG G e Ly)).toRingHom) g
  congr 1
  refine MvPolynomial.ringHom_ext (fun n => intHom_C _ _ n) (fun v => ?_)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  refine Fin.addCases ?_ ?_ v
  · intro v
    rw [Gsub_Y]
    simp only [evG, Fin.addCases_left, aeval_C, mapL_C]
    rfl
  intro v
  refine Fin.addCases ?_ ?_ v
  · intro o; rw [Gsub_s]; simp [evG, lGen, mapL_T]
  · intro j
    rw [Gsub_y, map_mul, lGen_Wsub, ← hy, map_mul, mapL_C, aeval_C, ← mul_assoc]
    have h1 : (algebraMap (Localization.AtPrime q.ker) _ (βinv G e β q hβq)) *
        LaurentPolynomial.C (algebraMap A (Localization.AtPrime q.ker) (toAZ G e β)) = 1 := by
      rw [← LaurentPolynomial.C_eq_algebraMap, ← map_mul, βinv, IsLocalization.mk'_spec, map_one,
        map_one]
    rw [h1, one_mul]
    simp [evG]

end K3

end Chain

/-! ### K4 and the final statement -/

section Final

open LaurentPolynomial hiding C

variable (h : MvPolynomial (Fin (m + (kc + l))) ℤ) (f : ℕ)
  (hgen : ∀ g ∈ G, h ^ f * g ∈ lspan (List.ofFn fun i : Fin m => F (Fin.castAdd (kc + l) i)))
  (dA ch cb : MvPolynomial (Fin (m + (kc + l))) ℤ) (hdh : dA = h * ch) (hdb : dA = β * cb)
  (Ly : Fin r → A[T;T⁻¹])
  (hy : ∀ j, LaurentPolynomial.C (toAZ G e β) * Ly j = aeval (evW G e F γ w) (Q j))
  (Hloc : ∀ q : Pt A, toAZ G e dA ∉ q.ker →
    ∀ p : MvPolynomial (Option (Fin kc)) (Localization.AtPrime q.ker),
      aeval (lGen (xq G e F γ q) w) p = 0 → p ∈ Ideal.span (Set.range (lRel (xq G e F γ q) w)))

/-- The class of `g(Y, s, y)` in the model ring. -/
def zM (g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) : MR F γ β w Q :=
  Ideal.Quotient.mk _ (toQZ (aeval reesφ g))

include hgen hdh hdb Hloc in
/-- **K4, general form**: an element `x` of the model whose image in `N` comes, at every point, from a
polynomial over `A_q` with vanishing Laurent image, is killed near every point off `V(d)`. -/
theorem l3_point_gen (x : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ)
    (hx : ∀ (P : Pt (MR F γ β w Q)) (hh : P.z (mYq F γ β w Q (toQZ h)) ≠ 0)
      (hβq : toAZ G e β ∉ (ptAQ G e F γ β w Q h f hgen P hh).ker),
      ∃ p, aeval (lGen (xq G e F γ (ptAQ G e F γ β w Q h f hgen P hh)) w) p = 0 ∧
        κN G e F γ β w Q h f hgen dA ch hdh (ptAQ G e F γ β w Q h f hgen P hh) p =
          ΘN G e F γ β w Q h f hgen dA ch hdh (ptAQ G e F γ β w Q h f hgen P hh) (toQZ x))
    (P : Pt (MR F γ β w Q)) (hdP : dM F γ β w Q dA ∉ P.ker) :
    ∃ b, b ∉ P.ker ∧ b * Ideal.Quotient.mk _ (toQZ x) = 0 := by
  have hdP' : P.z (dM F γ β w Q dA) ≠ 0 := fun h0 => hdP (P.mem_ker.2 h0)
  have hsplit : ∀ c₁ c₂ : MvPolynomial (Fin (m + (kc + l))) ℤ, dA = c₁ * c₂ →
      P.z (mYq F γ β w Q (toQZ c₁)) ≠ 0 := by
    intro c₁ c₂ hc h0
    apply hdP'
    rw [dM, hc, map_mul, mYq, map_mul, map_mul, map_mul]
    exact mul_eq_zero_of_left (by simpa [mYq] using h0) _
  have hh := hsplit h ch hdh
  set q := ptAQ G e F γ β w Q h f hgen P hh
  have hq : ∀ p, q.z (e (Ideal.Quotient.mk _ p)) = P.z (mYq F γ β w Q p) :=
    ptA_z G e F γ β w Q h f hgen P hh
  have hdq : toAZ G e dA ∉ q.ker := fun hm => hdP' (by rw [← hq]; exact q.mem_ker.1 hm)
  have hβq : toAZ G e β ∉ q.ker := fun hm => hsplit β cb hdb (by rw [← hq]; exact q.mem_ker.1 hm)
  -- the local kernel statement
  obtain ⟨p, hp0, hpx⟩ := hx P hh hβq
  have hmem := Hloc q hdq _ hp0
  have hκ : κN G e F γ β w Q h f hgen dA ch hdh q p = 0 := by
    refine (Ideal.span_le.2 ?_ : _ ≤ RingHom.ker (κN G e F γ β w Q h f hgen dA ch hdh q)) hmem
    rintro _ ⟨i, rfl⟩
    exact κN_lRel G e F γ β w Q h f hgen dA ch hdh q i
  rw [hpx] at hκ
  -- first localisation: `N`
  have h1 : algebraMap (Md F γ β w Q dA) (NN G e F γ β w Q h f hgen dA ch hdh q)
      (algebraMap (MR F γ β w Q) _ (Ideal.Quotient.mk _ (toQZ x))) = 0 := hκ
  obtain ⟨⟨_, a, ha, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff
    ((q.ker.primeCompl).map (φAd G e F γ β w Q h f hgen dA ch hdh)) _ _).1 h1
  obtain ⟨y0, rfl⟩ := e.surjective a
  obtain ⟨pa, rfl⟩ := Ideal.Quotient.mk_surjective y0
  have hm' : φAd G e F γ β w Q h f hgen dA ch hdh (e (Ideal.Quotient.mk _ pa)) *
      algebraMap (MR F γ β w Q) (Md F γ β w Q dA) (Ideal.Quotient.mk _ (toQZ x)) = 0 := hm
  rw [φAd_apply, ← map_mul] at hm'
  -- second localisation: `MR[1/d]`
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (dM F γ β w Q dA))
    (Md F γ β w Q dA) _).1 hm'
  refine ⟨dM F γ β w Q dA ^ j * mYq F γ β w Q pa, fun hb => ?_, by rw [mul_assoc]; exact hj⟩
  rw [Pt.mem_ker, map_mul, map_pow] at hb
  rcases mul_eq_zero.1 hb with h0 | h0
  · exact hdP' (pow_eq_zero_iff'.1 h0).1
  · exact ha (q.mem_ker.2 (by rw [hq]; exact h0))

include hgen hdh hdb hy Hloc in
/-- **K4: at a point of the model ring off `V(d)`, the class of a global relation is killed by an
element outside the point.** -/
theorem l3_point (g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hg : aeval (evG G e Ly) g = 0) (P : Pt (MR F γ β w Q)) (hdP : dM F γ β w Q dA ∉ P.ker) :
    ∃ b, b ∉ P.ker ∧ b * zM F γ β w Q g = 0 :=
  l3_point_gen G e F γ β w Q h f hgen dA ch cb hdh hdb Hloc (aeval reesφ g)
    (fun P hh hβq => ⟨aeval (Gsub G e β Q _ hβq) g,
      by rw [lGen_Gsub G e F γ β w Q _ hβq Ly hy, hg, map_zero], κN_Gsub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩)
    P hdP

include hgen hdh hdb hy Hloc in
/-- **K4 for the head coordinates** (`hu`): `φ(P̃_q) − u'_q` is killed near every point off `V(d)`. -/
theorem l3_point_u (Ph : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) (i₀ : Fin kc)
    (hPh : aeval (evG G e Ly) (Ph i₀) =
      LaurentPolynomial.C (toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i₀)))) * T (w i₀))
    (P : Pt (MR F γ β w Q)) (hdP : dM F γ β w Q dA ∉ P.ker) :
    ∃ b, b ∉ P.ker ∧ b * Ideal.Quotient.mk _ (toQZ (aeval reesφ (Ph i₀) - X (varU i₀))) = 0 :=
  l3_point_gen G e F γ β w Q h f hgen dA ch cb hdh hdb Hloc _
    (fun P hh hβq => ⟨aeval (Gsub G e β Q _ hβq) (Ph i₀) - X (some i₀), by
      rw [map_sub, lGen_Gsub G e F γ β w Q _ hβq Ly hy, hPh, map_mul, mapL_C, mapL_T, aeval_X]
      simp [lGen, xq], by
      rw [map_sub, κN_Gsub, κN_u, map_sub, map_sub, MvPolynomial.map_X]⟩)
    P hdP

include hgen hdh hdb hy Hloc in
/-- **L3 (`hφ` of `exists_reesChart_open`)**: every global relation, pulled back to the model,
lies in the model ideal up to an integer and a power of `d`. -/
theorem l3_hφ (g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hg : aeval (evG G e Ly) g = 0) :
    ∃ (N D : ℕ), 0 < D ∧ (D : MvPolynomial _ ℤ) * (rename varY dA ^ N * aeval reesφ g) ∈
      lspan (sysEq (reesSys F γ β w Q)) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_eq_zero_of_pts (SmoothCert.hasPres _) (zM F γ β w Q g)
    (dM F γ β w Q dA) fun P hdP => l3_point G e F γ β w Q h f hgen dA ch cb hdh hdb Ly hy Hloc g hg P hdP
  have hmem : toQZ (rename varY dA ^ N * aeval reesφ g) ∈ lspan ((sysEq (reesSys F γ β w Q)).map toQZ) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, toQZ_rename, map_mul, map_pow]
    exact hN
  obtain ⟨D, hD, hDm⟩ := int_mem _ _ hmem
  exact ⟨N, D, hD, hDm⟩

include hgen hdh hdb hy Hloc in
/-- **L3 for the head coordinates (`hu` of `exists_reesChart_open`)**. -/
theorem l3_hu (Ph : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) (i₀ : Fin kc)
    (hPh : aeval (evG G e Ly) (Ph i₀) =
      LaurentPolynomial.C (toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i₀)))) * T (w i₀)) :
    ∃ (N D : ℕ), 0 < D ∧ (D : MvPolynomial _ ℤ) *
      (rename varY dA ^ N * (aeval reesφ (Ph i₀) - X (varU i₀))) ∈
      lspan (sysEq (reesSys F γ β w Q)) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_eq_zero_of_pts (SmoothCert.hasPres _)
    (Ideal.Quotient.mk _ (toQZ (aeval reesφ (Ph i₀) - X (varU i₀))) : MR F γ β w Q)
    (dM F γ β w Q dA) fun P hdP =>
      l3_point_u G e F γ β w Q h f hgen dA ch cb hdh hdb Ly hy Hloc Ph i₀ hPh P hdP
  have hmem : toQZ (rename varY dA ^ N * (aeval reesφ (Ph i₀) - X (varU i₀))) ∈
      lspan ((sysEq (reesSys F γ β w Q)).map toQZ) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, toQZ_rename, map_mul, map_pow]
    exact hN
  obtain ⟨D, hD, hDm⟩ := int_mem _ _ hmem
  exact ⟨N, D, hD, hDm⟩

end Final

/-! ### L3-e1: the local kernel statement from the centred case -/

section Split

/-- **L3-e1**: the per-point kernel statement `Hloc` of `l3_hφ` follows from its centred case (all
heads vanish at `q`). If some head `γ x̃_{i₀}` is not in `q.ker`, it is a unit of `A_q` with the
explicit inverse `mk' 1 ⟨γ x̃_{i₀}, _⟩` and the Laurent case `l3_ker_laurent` applies. The case split
is decided by the zero test of the point. -/
theorem hloc_of_cent (dA : MvPolynomial (Fin (m + (kc + l))) ℤ) (hw : ∀ i, 0 < w i)
    (Hcent : ∀ q : Pt A, toAZ G e dA ∉ q.ker →
      (∀ i, toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i))) ∈ q.ker) →
      ∀ p : MvPolynomial (Option (Fin kc)) (Localization.AtPrime q.ker),
        aeval (lGen (xq G e F γ q) w) p = 0 → p ∈ Ideal.span (Set.range (lRel (xq G e F γ q) w)))
    (q : Pt A) (hq : toAZ G e dA ∉ q.ker)
    (p : MvPolynomial (Option (Fin kc)) (Localization.AtPrime q.ker))
    (hp : aeval (lGen (xq G e F γ q) w) p = 0) :
    p ∈ Ideal.span (Set.range (lRel (xq G e F γ q) w)) := by
  rcases Constructive.fin_forall_or_exists
      (A := fun i => toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i))) ∈ q.ker)
      (B := fun i => toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i))) ∉ q.ker)
      (fun i => q.mem_ker_dec _) with hall | ⟨i₀, hi₀⟩
  · exact Hcent q hq hall p hp
  · refine l3_ker_laurent (xq G e F γ q) w
      (IsLocalization.mk' (Localization.AtPrime q.ker) (1 : A)
        (⟨_, hi₀⟩ : q.ker.primeCompl)) ?_ (hw i₀) p hp
    rw [xq, IsLocalization.mk'_spec, map_one]

end Split

end BezoutCounterexample.Principalization
