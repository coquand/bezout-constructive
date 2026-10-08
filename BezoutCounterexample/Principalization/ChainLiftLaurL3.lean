import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesL3d
import BezoutCounterexample.Constructive.ChainLiftLaurOpen

/-!
# L3 for the Laurent opens (Task B, S5c/S6, Laurent part)

As `ChainLiftReesL3d`, for the Laurent model `laurSys F ε β Q` (rows `F_eq`, `s t − ε`,
`β yⱼ − Qⱼ(Y, s, t)`). On `D(ε)` the head `ε` has an explicit inverse at every point, so the local
kernel statement is `l3_ker_laurent` (one head of weight `1`) and no centred case occurs.

* `l3L_hφ`: `hφ` of `exists_laurChart_open` for one global relation, from `d = h·c = β·c' = ε·c''`
  and the `y`-row semantics.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] [Algebra ℚ A] {m kc l r : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (ε β : MvPolynomial (Fin (m + (kc + l))) ℤ)
  (Q : Fin r → MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ)

/-- The Laurent model ring. -/
abbrev MRL := SmoothCert.QB (sysEq (laurSys F ε β Q))

/-- The model image of a rational polynomial in `Y`. -/
def mYqL (p : MvPolynomial (Fin (m + (kc + l))) ℚ) : MRL F ε β Q :=
  Ideal.Quotient.mk _ (rename (lvarY (r := r)) p)

lemma mYqL_feq (p : MvPolynomial (Fin (m + (kc + l))) ℤ)
    (hp : p ∈ lspan (List.ofFn fun i : Fin m => F (Fin.castAdd (kc + l) i))) :
    mYqL F ε β Q (toQZ p) = 0 := by
  rw [mYqL, Ideal.Quotient.eq_zero_iff_mem, toQZ, ← map_rename]
  refine toQZ_mem_lspan_map ?_
  have := rename_mem_lspan (lvarY (r := r)) hp
  refine (Ideal.span_le.2 ?_) this
  intro x hx
  simp only [List.map_ofFn, Set.mem_ofPred_eq, List.mem_ofFn, Function.comp_apply] at hx
  obtain ⟨i, rfl⟩ := hx
  refine Ideal.subset_span ?_
  show _ ∈ sysEq (laurSys F ε β Q)
  rw [← laurSys_eq F ε β Q i]
  exact List.mem_ofFn.2 ⟨Fin.castAdd r (Fin.castAdd 1 i), rfl⟩

section PtA

variable (h : MvPolynomial (Fin (m + (kc + l))) ℤ) (f : ℕ)
  (hgen : ∀ g ∈ G, h ^ f * g ∈ lspan (List.ofFn fun i : Fin m => F (Fin.castAdd (kc + l) i)))
  (P : Pt (MRL F ε β Q)) (hh : P.z (mYqL F ε β Q (toQZ h)) ≠ 0)

/-- `A → κ(P)`. -/
def ptAHomL : A →+* P.L :=
  (Ideal.Quotient.lift (lspan (G.map toQZ))
      ((P.z : MRL F ε β Q →+* P.L).comp
        ((Ideal.Quotient.mk _).comp (rename (lvarY (r := r))).toRingHom)) (by
      intro x hx
      refine (Ideal.span_le.2 ?_ : _ ≤ RingHom.ker _) hx
      intro y hy
      simp only [Set.mem_ofPred_eq, List.mem_map] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have h0 := congrArg P.z (mYqL_feq F ε β Q _ (hgen g hg))
      show P.z (mYqL F ε β Q (toQZ g)) = 0
      simp only [mYqL, map_mul, map_pow, map_zero] at h0 hh ⊢
      exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hh))).comp
    e.symm.toRingHom

lemma ptAHomL_apply (p : MvPolynomial (Fin (m + (kc + l))) ℚ) :
    ptAHomL G e F ε β Q h f hgen P hh (e (Ideal.Quotient.mk _ p)) = P.z (mYqL F ε β Q p) := by
  simp only [ptAHomL, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
  rfl

/-- A point of the Laurent model ring off `V(h)` gives a point of `A`. -/
def ptAL : Pt A where
  L := P.L
  z := (ptAHomL G e F ε β Q h f hgen P hh).toRatAlgHom
  dec := P.dec

lemma ptAL_z (p : MvPolynomial (Fin (m + (kc + l))) ℚ) :
    (ptAL G e F ε β Q h f hgen P hh).z (e (Ideal.Quotient.mk _ p)) = P.z (mYqL F ε β Q p) :=
  ptAHomL_apply G e F ε β Q h f hgen P hh p

end PtA

section Chain

variable (h : MvPolynomial (Fin (m + (kc + l))) ℤ) (f : ℕ)
  (hgen : ∀ g ∈ G, h ^ f * g ∈ lspan (List.ofFn fun i : Fin m => F (Fin.castAdd (kc + l) i)))
  (dA ch : MvPolynomial (Fin (m + (kc + l))) ℤ) (hdh : dA = h * ch)

/-- The model image of `d`. -/
abbrev dML : MRL F ε β Q := mYqL F ε β Q (toQZ dA)

/-- `MRL[1/d]`. -/
abbrev MdL := Localization.Away (dML F ε β Q dA)

include hdh in
lemma isUnit_h_MdL :
    IsUnit (algebraMap (MRL F ε β Q) (MdL F ε β Q dA) (mYqL F ε β Q (toQZ h))) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := MdL F ε β Q dA) (dML F ε β Q dA)
  have hd : dML F ε β Q dA = mYqL F ε β Q (toQZ h) * mYqL F ε β Q (toQZ ch) := by
    simp only [dML, mYqL, hdh, map_mul]
  have h2 : algebraMap (MRL F ε β Q) (MdL F ε β Q dA) (dML F ε β Q dA) =
      algebraMap _ (MdL F ε β Q dA) (mYqL F ε β Q (toQZ h)) *
        algebraMap _ (MdL F ε β Q dA) (mYqL F ε β Q (toQZ ch)) := by rw [← map_mul, ← hd]
  rw [h2] at hu
  exact isUnit_of_mul_isUnit_left hu

include hgen hdh in
/-- `A → MRL[1/d]`. -/
def φAL : A →+* MdL F ε β Q dA :=
  (Ideal.Quotient.lift (lspan (G.map toQZ))
      ((algebraMap (MRL F ε β Q) (MdL F ε β Q dA)).comp
        ((Ideal.Quotient.mk _).comp (rename (lvarY (r := r))).toRingHom)) (by
      intro x hx
      refine (Ideal.span_le.2 ?_ : _ ≤ RingHom.ker _) hx
      intro y hy
      simp only [Set.mem_ofPred_eq, List.mem_map] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have h0 := congrArg (algebraMap (MRL F ε β Q) (MdL F ε β Q dA))
        (mYqL_feq F ε β Q _ (hgen g hg))
      have hu := isUnit_h_MdL F ε β Q h dA ch hdh
      show algebraMap _ _ (mYqL F ε β Q (toQZ g)) = 0
      simp only [mYqL, map_mul, map_pow, map_zero] at h0 hu ⊢
      exact (hu.pow f).mul_right_eq_zero.1 h0)).comp
    e.symm.toRingHom

lemma φAL_apply (p : MvPolynomial (Fin (m + (kc + l))) ℚ) :
    φAL G e F ε β Q h f hgen dA ch hdh (e (Ideal.Quotient.mk _ p)) =
      algebraMap _ (MdL F ε β Q dA) (mYqL F ε β Q p) := by
  simp only [φAL, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
  rfl

variable (q : Pt A)

/-- `MRL[1/d]` localised at the image of `A ∖ q`. -/
abbrev NNL := Localization ((q.ker.primeCompl).map (φAL G e F ε β Q h f hgen dA ch hdh))

/-- `A_q → N`. -/
def ιNL : Localization.AtPrime q.ker →+* NNL G e F ε β Q h f hgen dA ch hdh q :=
  IsLocalization.lift (M := q.ker.primeCompl)
    (g := (algebraMap _ (NNL G e F ε β Q h f hgen dA ch hdh q)).comp (φAL G e F ε β Q h f hgen dA ch hdh))
    fun a => IsLocalization.map_units (NNL G e F ε β Q h f hgen dA ch hdh q)
      (⟨φAL G e F ε β Q h f hgen dA ch hdh a, Submonoid.mem_map_of_mem _ a.2⟩ :
        (q.ker.primeCompl).map (φAL G e F ε β Q h f hgen dA ch hdh))

/-- `ℚ[W] → N`. -/
def ΘNL : MvPolynomial (Fin (((m + 1) + r) + ((1 + kc) + l))) ℚ →+* NNL G e F ε β Q h f hgen dA ch hdh q :=
  (algebraMap (MdL F ε β Q dA) _).comp ((algebraMap (MRL F ε β Q) _).comp (Ideal.Quotient.mk _))

lemma ιNL_alg (p : MvPolynomial (Fin (m + (kc + l))) ℚ) :
    ιNL G e F ε β Q h f hgen dA ch hdh q (algebraMap A _ (e (Ideal.Quotient.mk _ p))) =
      ΘNL G e F ε β Q h f hgen dA ch hdh q (rename lvarY p) := by
  rw [ιNL, IsLocalization.lift_eq, RingHom.comp_apply, φAL_apply]
  rfl

lemma ΘNL_sys {x : MvPolynomial (Fin (((m + 1) + r) + ((1 + kc) + l))) ℤ}
    (hx : x ∈ lspan (sysEq (laurSys F ε β Q))) : ΘNL G e F ε β Q h f hgen dA ch hdh q (toQZ x) = 0 := by
  simp only [ΘNL, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (toQZ_mem_lspan_map hx), map_zero]

lemma mem_sysEqL (i : Fin ((m + 1) + r)) :
    laurSys F ε β Q (Fin.castAdd _ i) ∈ lspan (sysEq (laurSys F ε β Q)) :=
  Ideal.subset_span (List.mem_ofFn.2 ⟨i, rfl⟩)

/-- The single head `ε` at `q`. -/
def xqL : Fin 1 → Localization.AtPrime q.ker := fun _ => algebraMap A _ (toAZ G e ε)

/-- `κ : A_q[s, u] → N`, `s ↦ s`, `u ↦ t`. -/
def κNL : MvPolynomial (Option (Fin 1)) (Localization.AtPrime q.ker) →+* NNL G e F ε β Q h f hgen dA ch hdh q :=
  eval₂Hom (ιNL G e F ε β Q h f hgen dA ch hdh q) fun o =>
    o.elim (ΘNL G e F ε β Q h f hgen dA ch hdh q (X lvarS))
      (fun _ => ΘNL G e F ε β Q h f hgen dA ch hdh q (X lvarT))

lemma κNL_C (a : Localization.AtPrime q.ker) :
    κNL G e F ε β Q h f hgen dA ch hdh q (C a) = ιNL G e F ε β Q h f hgen dA ch hdh q a :=
  eval₂Hom_C _ _ _

lemma κNL_s : κNL G e F ε β Q h f hgen dA ch hdh q (X none) =
    ΘNL G e F ε β Q h f hgen dA ch hdh q (X lvarS) := eval₂Hom_X' _ _ _

lemma κNL_t (o : Fin 1) : κNL G e F ε β Q h f hgen dA ch hdh q (X (some o)) =
    ΘNL G e F ε β Q h f hgen dA ch hdh q (X lvarT) := eval₂Hom_X' _ _ _

/-- **K1**: `κ` kills `ε − s t`. -/
lemma κNL_lRel (o : Fin 1) :
    κNL G e F ε β Q h f hgen dA ch hdh q (lRel (xqL G e ε q) (fun _ => 1) o) = 0 := by
  have hrow := ΘNL_sys G e F ε β Q h f hgen dA ch hdh q
    (mem_sysEqL F ε β Q (Fin.castAdd r (Fin.natAdd m 0)))
  rw [laurSys_t] at hrow
  simp only [map_sub, map_mul, MvPolynomial.map_X, MvPolynomial.map_rename] at hrow
  simp only [lRel, map_sub, map_mul, pow_one, κNL_C, κNL_s, κNL_t, xqL, toAZ, ιNL_alg]
  rw [← neg_eq_zero, neg_sub]
  exact hrow

/-! #### K2 -/

variable (hβq : toAZ G e β ∉ q.ker)

/-- `β⁻¹` in `A_q`. -/
def βinvL : Localization.AtPrime q.ker :=
  IsLocalization.mk' (Localization.AtPrime q.ker) (1 : A) (⟨toAZ G e β, hβq⟩ : q.ker.primeCompl)

/-- `W = (Y, s, t) ↦ (Y, s, u)` over `A_q`. -/
def WsubL : Fin ((m + (kc + l)) + (1 + 1)) → MvPolynomial (Option (Fin 1)) (Localization.AtPrime q.ker) :=
  Fin.addCases (fun v => C (algebraMap A _ (e (Ideal.Quotient.mk _ (X v)))))
    (Fin.addCases (fun _ => X none) (fun o => X (some o)))

/-- The global variables: `Y ↦ Y`, `s ↦ s`, `yⱼ ↦ β⁻¹ Qⱼ(Y, s, u)`. -/
def GsubL : Fin ((m + (kc + l)) + (1 + r)) → MvPolynomial (Option (Fin 1)) (Localization.AtPrime q.ker) :=
  Fin.addCases (fun v => C (algebraMap A _ (e (Ideal.Quotient.mk _ (X v)))))
    (Fin.addCases (fun _ => X none) (fun j => C (βinvL G e β q hβq) * aeval (WsubL G e q) (Q j)))

lemma WsubL_Y (v : Fin (m + (kc + l))) : WsubL G e q (Fin.castAdd (1 + 1) v) =
    C (algebraMap A _ (e (Ideal.Quotient.mk _ (X v)))) := by simp [WsubL]
lemma WsubL_s (o : Fin 1) : WsubL G e q (Fin.natAdd _ (Fin.castAdd 1 o)) = X none := by simp [WsubL]
lemma WsubL_t (o : Fin 1) : WsubL G e q (Fin.natAdd _ (Fin.natAdd 1 o)) = X (some o) := by
  simp only [WsubL, Fin.addCases_right]
lemma GsubL_Y (v : Fin (m + (kc + l))) : GsubL G e β Q q hβq (Fin.castAdd (1 + r) v) =
    C (algebraMap A _ (e (Ideal.Quotient.mk _ (X v)))) := by simp [GsubL]
lemma GsubL_s (o : Fin 1) : GsubL G e β Q q hβq (Fin.natAdd _ (Fin.castAdd r o)) = X none := by
  simp [GsubL]
lemma GsubL_y (j : Fin r) : GsubL G e β Q q hβq (Fin.natAdd _ (Fin.natAdd 1 j)) =
    C (βinvL G e β q hβq) * aeval (WsubL G e q) (Q j) := by simp [GsubL]

lemma κNL_Wsub (P : MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ) :
    κNL G e F ε β Q h f hgen dA ch hdh q (aeval (WsubL G e q) P) =
      ΘNL G e F ε β Q h f hgen dA ch hdh q (toQZ (rename (lvarW (kc := kc) (r := r)) P)) := by
  show ((κNL G e F ε β Q h f hgen dA ch hdh q).comp (aeval (WsubL G e q)).toRingHom) P =
    ((ΘNL G e F ε β Q h f hgen dA ch hdh q).comp
      (toQZ.comp (rename (lvarW (kc := kc) (r := r))).toRingHom)) P
  congr 1
  refine MvPolynomial.ringHom_ext (fun n => intHom_C _ _ n) (fun v => ?_)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, rename_X,
    MvPolynomial.map_X]
  refine Fin.addCases ?_ ?_ v
  · intro v; rw [WsubL_Y, κNL_C, ιNL_alg, rename_X, lvarW_Y]
  · intro a
    refine Fin.addCases ?_ ?_ a
    · intro o; rw [WsubL_s, κNL_s, lvarW_s]
    · intro o; rw [WsubL_t, κNL_t, lvarW_t]

include hβq in
lemma ιNL_βinv : ιNL G e F ε β Q h f hgen dA ch hdh q (βinvL G e β q hβq) *
    ΘNL G e F ε β Q h f hgen dA ch hdh q (toQZ (rename lvarY β)) = 1 := by
  rw [toQZ_rename, ← ιNL_alg, ← map_mul, βinvL]
  rw [show (algebraMap A (Localization.AtPrime q.ker) (e (Ideal.Quotient.mk _ (toQZ β)))) =
    algebraMap A _ (toAZ G e β) from rfl, IsLocalization.mk'_spec, map_one, map_one]

include hβq in
/-- **K2**: `κ(p_q(g))` is the class of `g(Y, s, y)`. -/
lemma κNL_Gsub (g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) :
    κNL G e F ε β Q h f hgen dA ch hdh q (aeval (GsubL G e β Q q hβq) g) =
      ΘNL G e F ε β Q h f hgen dA ch hdh q (toQZ (aeval laurφ g)) := by
  show ((κNL G e F ε β Q h f hgen dA ch hdh q).comp (aeval (GsubL G e β Q q hβq)).toRingHom) g =
    ((ΘNL G e F ε β Q h f hgen dA ch hdh q).comp (toQZ.comp (aeval laurφ).toRingHom)) g
  congr 1
  refine MvPolynomial.ringHom_ext (fun n => intHom_C _ _ n) (fun v => ?_)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  refine Fin.addCases ?_ ?_ v
  · intro v
    rw [GsubL_Y, κNL_C, ιNL_alg, rename_X,
      show (Fin.castAdd (1 + r) v : Fin ((m + (kc + l)) + (1 + r))) = gY v from rfl, laurφ_Y,
      MvPolynomial.map_X]
  intro v
  refine Fin.addCases ?_ ?_ v
  · intro o
    rw [GsubL_s, κNL_s,
      show (Fin.natAdd (m + (kc + l)) (Fin.castAdd r o) : Fin ((m + (kc + l)) + (1 + r))) = gS
      by rw [Subsingleton.elim o 0]; rfl, laurφ_gS, MvPolynomial.map_X]
  · intro j
    rw [GsubL_y, map_mul, κNL_C, κNL_Wsub]
    have hrow := ΘNL_sys G e F ε β Q h f hgen dA ch hdh q
      (mem_sysEqL F ε β Q (Fin.natAdd (m + 1) j))
    rw [laurSys_y, map_sub, map_sub, sub_eq_zero] at hrow
    rw [← hrow, map_mul, map_mul, ← mul_assoc, ιNL_βinv, one_mul,
      show (Fin.natAdd (m + (kc + l)) (Fin.natAdd 1 j) : Fin ((m + (kc + l)) + (1 + r))) = gYr j
      from rfl, laurφ_y]

/-! #### K3 -/

section K3

open LaurentPolynomial hiding C

variable (Ly : Fin r → A[T;T⁻¹])

/-- `(Y, s, t) ↦ (Y, T⁻¹, C(ε) T)` into `A[T^±]`. -/
def evWL : Fin ((m + (kc + l)) + (1 + 1)) → A[T;T⁻¹] :=
  Fin.addCases (fun v => LaurentPolynomial.C (e (Ideal.Quotient.mk _ (X v))))
    (Fin.addCases (fun _ => T (-1)) (fun _ => LaurentPolynomial.C (toAZ G e ε) * T 1))

lemma lGenL_Wsub (P : MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ) :
    aeval (lGen (xqL G e ε q) (fun _ => 1)) (aeval (WsubL G e q) P) =
      mapL q (aeval (evWL G e ε) P) := by
  show ((aeval (lGen (xqL G e ε q) (fun _ => 1))).toRingHom.comp (aeval (WsubL G e q)).toRingHom) P =
    ((mapL q).comp (aeval (evWL G e ε)).toRingHom) P
  congr 1
  refine MvPolynomial.ringHom_ext (fun n => intHom_C _ _ n) (fun v => ?_)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  refine Fin.addCases ?_ ?_ v
  · intro v
    rw [WsubL_Y]
    simp only [evWL, Fin.addCases_left, aeval_C, mapL_C]
    rfl
  · intro a
    refine Fin.addCases ?_ ?_ a
    · intro o; rw [WsubL_s]; simp [evWL, lGen, mapL_T]
    · intro o
      rw [WsubL_t]
      simp only [evWL, Fin.addCases_right, aeval_X, lGen, Option.elim, map_mul, mapL_C, mapL_T, xqL,
        Nat.cast_one]

include hβq in
/-- **K3**: the Laurent image of `p_q(g)` is the image of `g(Y, T⁻¹, Ly)`. -/
lemma lGenL_Gsub (hy : ∀ j, LaurentPolynomial.C (toAZ G e β) * Ly j = aeval (evWL G e ε) (Q j))
    (g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) :
    aeval (lGen (xqL G e ε q) (fun _ => 1)) (aeval (GsubL G e β Q q hβq) g) =
      mapL q (aeval (evG G e Ly) g) := by
  show ((aeval (lGen (xqL G e ε q) (fun _ => 1))).toRingHom.comp
      (aeval (GsubL G e β Q q hβq)).toRingHom) g = ((mapL q).comp (aeval (evG G e Ly)).toRingHom) g
  congr 1
  refine MvPolynomial.ringHom_ext (fun n => intHom_C _ _ n) (fun v => ?_)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  refine Fin.addCases ?_ ?_ v
  · intro v
    rw [GsubL_Y]
    simp only [evG, Fin.addCases_left, aeval_C, mapL_C]
    rfl
  intro v
  refine Fin.addCases ?_ ?_ v
  · intro o; rw [GsubL_s]; simp [evG, lGen, mapL_T]
  · intro j
    rw [GsubL_y, map_mul, lGenL_Wsub, ← hy, map_mul, mapL_C, aeval_C, ← mul_assoc]
    have h1 : (algebraMap (Localization.AtPrime q.ker) _ (βinvL G e β q hβq)) *
        LaurentPolynomial.C (algebraMap A (Localization.AtPrime q.ker) (toAZ G e β)) = 1 := by
      rw [← LaurentPolynomial.C_eq_algebraMap, ← map_mul, βinvL, IsLocalization.mk'_spec, map_one,
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
  (dA ch cb ce : MvPolynomial (Fin (m + (kc + l))) ℤ) (hdh : dA = h * ch) (hdb : dA = β * cb)
  (hde : dA = ε * ce)
  (Ly : Fin r → A[T;T⁻¹])
  (hy : ∀ j, LaurentPolynomial.C (toAZ G e β) * Ly j = aeval (evWL G e ε) (Q j))

/-- The class of `g(Y, s, y)` in the Laurent model ring. -/
def zML (g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) : MRL F ε β Q :=
  Ideal.Quotient.mk _ (toQZ (aeval laurφ g))

include hgen hdh hdb hde hy in
/-- **K4 (Laurent)**: at a point of the model ring off `V(d)`, the class of a global relation is
killed by an element outside the point. -/
theorem l3L_point (g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hg : aeval (evG G e Ly) g = 0) (P : Pt (MRL F ε β Q)) (hdP : dML F ε β Q dA ∉ P.ker) :
    ∃ b, b ∉ P.ker ∧ b * zML F ε β Q g = 0 := by
  have hdP' : P.z (dML F ε β Q dA) ≠ 0 := fun h0 => hdP (P.mem_ker.2 h0)
  have hsplit : ∀ c₁ c₂ : MvPolynomial (Fin (m + (kc + l))) ℤ, dA = c₁ * c₂ →
      P.z (mYqL F ε β Q (toQZ c₁)) ≠ 0 := by
    intro c₁ c₂ hc h0
    apply hdP'
    rw [dML, hc, map_mul, mYqL, map_mul, map_mul, map_mul]
    exact mul_eq_zero_of_left (by simpa [mYqL] using h0) _
  have hh := hsplit h ch hdh
  set q := ptAL G e F ε β Q h f hgen P hh
  have hq : ∀ p, q.z (e (Ideal.Quotient.mk _ p)) = P.z (mYqL F ε β Q p) :=
    ptAL_z G e F ε β Q h f hgen P hh
  have hβq : toAZ G e β ∉ q.ker := fun hm => hsplit β cb hdb (by rw [← hq]; exact q.mem_ker.1 hm)
  have hεq : toAZ G e ε ∉ q.ker := fun hm => hsplit ε ce hde (by rw [← hq]; exact q.mem_ker.1 hm)
  -- the local kernel statement: the Laurent case
  have hp0 : aeval (lGen (xqL G e ε q) (fun _ => 1)) (aeval (GsubL G e β Q q hβq) g) = 0 := by
    rw [lGenL_Gsub G e ε β Q q hβq Ly hy, hg, map_zero]
  have hmem := l3_ker_laurent (xqL G e ε q) (fun _ => 1) (i₀ := 0)
    (IsLocalization.mk' (Localization.AtPrime q.ker) (1 : A) (⟨_, hεq⟩ : q.ker.primeCompl))
    (by rw [xqL, IsLocalization.mk'_spec, map_one]) Nat.one_pos _ hp0
  have hκ : κNL G e F ε β Q h f hgen dA ch hdh q (aeval (GsubL G e β Q q hβq) g) = 0 := by
    refine (Ideal.span_le.2 ?_ : _ ≤ RingHom.ker (κNL G e F ε β Q h f hgen dA ch hdh q)) hmem
    rintro _ ⟨o, rfl⟩
    exact κNL_lRel G e F ε β Q h f hgen dA ch hdh q o
  rw [κNL_Gsub] at hκ
  have h1 : algebraMap (MdL F ε β Q dA) (NNL G e F ε β Q h f hgen dA ch hdh q)
      (algebraMap (MRL F ε β Q) _ (zML F ε β Q g)) = 0 := hκ
  obtain ⟨⟨_, a, ha, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff
    ((q.ker.primeCompl).map (φAL G e F ε β Q h f hgen dA ch hdh)) _ _).1 h1
  obtain ⟨y0, rfl⟩ := e.surjective a
  obtain ⟨pa, rfl⟩ := Ideal.Quotient.mk_surjective y0
  have hm' : φAL G e F ε β Q h f hgen dA ch hdh (e (Ideal.Quotient.mk _ pa)) *
      algebraMap (MRL F ε β Q) (MdL F ε β Q dA) (zML F ε β Q g) = 0 := hm
  rw [φAL_apply, ← map_mul] at hm'
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (dML F ε β Q dA))
    (MdL F ε β Q dA) _).1 hm'
  refine ⟨dML F ε β Q dA ^ j * mYqL F ε β Q pa, fun hb => ?_, by rw [mul_assoc]; exact hj⟩
  rw [Pt.mem_ker, map_mul, map_pow] at hb
  rcases mul_eq_zero.1 hb with h0 | h0
  · exact hdP' (pow_eq_zero_iff'.1 h0).1
  · exact ha (q.mem_ker.2 (by rw [hq]; exact h0))

include hgen hdh hdb hde hy in
/-- **L3 for a Laurent open (`hφ` of `exists_laurChart_open`)**. -/
theorem l3L_hφ (g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hg : aeval (evG G e Ly) g = 0) :
    ∃ (N D : ℕ), 0 < D ∧ (D : MvPolynomial _ ℤ) * (rename lvarY dA ^ N * aeval laurφ g) ∈
      lspan (sysEq (laurSys F ε β Q)) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_eq_zero_of_pts (SmoothCert.hasPres _) (zML F ε β Q g)
    (dML F ε β Q dA) fun P hdP =>
      l3L_point G e F ε β Q h f hgen dA ch cb ce hdh hdb hde Ly hy g hg P hdP
  have hmem : toQZ (rename lvarY dA ^ N * aeval laurφ g) ∈
      lspan ((sysEq (laurSys F ε β Q)).map toQZ) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, toQZ_rename, map_mul, map_pow]
    exact hN
  obtain ⟨D, hD, hDm⟩ := int_mem _ _ hmem
  exact ⟨N, D, hD, hDm⟩

end Final

end BezoutCounterexample.Principalization
