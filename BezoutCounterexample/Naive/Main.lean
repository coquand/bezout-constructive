import BezoutCounterexample.Naive.ConstructionL
import BezoutCounterexample.Naive.Embed

/-!
# `R_naive` is a Bézout domain that is not an elementary divisor domain

* `RL.key_obstruction`: the five-element obstruction for the Laurent variant `RL` of the
  Hägg–Mörtberg ring (the proof of Lemma 5.3, unchanged).
* `RL.freshTarget`: `RL`, with the chain of subrings `A_n ⊆ RL`, is a fresh target: the two
  Laurent variables adjoined at stage `n + 1` are units, algebraically independent over `A_n`.
* `naive_main_theorem`: the naive Kronecker ring `RN` is a Bézout domain and not an elementary
  divisor domain.
-/

noncomputable section

namespace BezoutCounterexample

open Set Topology Matrix CL

/-- **Lemma 5.3 for `RL`.** -/
theorem RL.key_obstruction :
    ¬ ∃ p q u v μ : RL, μ * (![p, q] ᵥ* (M.map RL.ι) ⬝ᵥ ![u, v]) = 1 := by
  rintro ⟨p, q, u, v, μ, hrel⟩
  obtain ⟨N, w, hw⟩ := RL.exists_of_fin 5 ![p, q, u, v, μ]
  have hrelN : w 4 * (![w 0, w 1] ᵥ* (M.map (CL.ι N)) ⬝ᵥ ![w 2, w 3]) = 1 := by
    apply RL.of_injective N
    have e : ∀ t, RL.of N (w t) = ![p, q, u, v, μ] t := hw
    simp only [vecMul_M_dotProduct, map_mul, map_add, map_sub, map_one, RL.of_ι, e] at hrel ⊢
    simpa using hrel
  rw [vecMul_M_dotProduct] at hrelN
  apply nonorientable N
  have hc : ∀ a : A N, Continuous fun z : K N => z.1 a :=
    fun a => (RealPt.continuous_eval a).comp continuous_subtype_val
  refine ⟨fun z => (Mreal (z.1 (CL.ι N x)) (z.1 (CL.ι N y))).mulVec ![z.1 (w 2), z.1 (w 3)], ?_,
    fun z => ⟨?_, mem_lineBundle_iff.2 ⟨_, rfl⟩⟩⟩
  · refine continuous_pi fun i => ?_
    fin_cases i <;> simp only [Mreal_mulVec] <;> simp <;> fun_prop
  · intro h0
    have h := congrArg z.1 hrelN
    simp only [map_mul, map_add, map_sub, map_one] at h
    have h1 := congrFun h0 0
    have h2 := congrFun h0 1
    simp only [Mreal_mulVec, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h1 h2
    have : z.1 (w 4) * (z.1 (w 0) * ((1 + z.1 (CL.ι N x)) * z.1 (w 2) + z.1 (CL.ι N y) * z.1 (w 3)) +
        z.1 (w 1) * (z.1 (CL.ι N y) * z.1 (w 2) + (1 - z.1 (CL.ι N x)) * z.1 (w 3))) = 1 := by
      linear_combination h
    rw [h1, h2, mul_zero, mul_zero, add_zero, mul_zero] at this
    exact zero_ne_one this

/-- If `f : A → R` is injective and `A[Y₀, Y₁] → R`, `Yᵢ ↦ vᵢ` is injective, then `v` is
algebraically independent over the image of `f`. -/
lemma algebraicIndependent_range {A R : Type*} [CommRing A] [CommRing R] (f : A →+* R)
    (hf : Function.Injective f) (v : Fin 2 → R)
    (h : Function.Injective (MvPolynomial.eval₂Hom f v)) : AlgebraicIndependent f.range v := by
  let e : A ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b hab => hf (congrArg Subtype.val hab), f.rangeRestrict_surjective⟩
  rw [algebraicIndependent_iff_injective_aeval]
  have hfac : (MvPolynomial.aeval v : MvPolynomial (Fin 2) f.range →ₐ[f.range] R).toRingHom =
      (MvPolynomial.eval₂Hom f v).comp (MvPolynomial.map e.symm.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
        RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
      show (r : R) = f (e.symm r)
      have : f (e.symm r) = (e (e.symm r) : R) := rfl
      rw [this, RingEquiv.apply_symm_apply]
    · intro i
      simp
  intro p q hpq
  have : (MvPolynomial.aeval v : MvPolynomial (Fin 2) f.range →ₐ[f.range] R).toRingHom p =
      (MvPolynomial.aeval v : MvPolynomial (Fin 2) f.range →ₐ[f.range] R).toRingHom q := hpq
  rw [hfac] at this
  exact MvPolynomial.map_injective _ e.symm.injective (h this)

namespace CL

/-- The Laurent variables of stage `n + 1`. -/
def lvar (n : ℕ) (i : Fin 2) : A (n + 1) :=
  algebraMap (Poly2 (step (stage n) (pairAt n).1 (pairAt n).2).A')
    (L2 (step (stage n) (pairAt n).1 (pairAt n).2).A') (MvPolynomial.X i)

lemma isUnit_lvar (n : ℕ) (i : Fin 2) : IsUnit (lvar n i) := isUnit_X _ i

lemma incl_eq (n : ℕ) (a : A n) :
    incl n a = toL2 _ ((step (stage n) (pairAt n).1 (pairAt n).2).f a) := rfl

lemma eval₂_lvar_injective (n : ℕ) :
    Function.Injective (MvPolynomial.eval₂Hom (RL.of n) ![RL.of (n + 1) (lvar n 0),
      RL.of (n + 1) (lvar n 1)]) := by
  set D := step (stage n) (pairAt n).1 (pairAt n).2
  have h1 : (RL.of (n + 1)).comp ((toL2 D.A').comp (D.f : A n →+* D.A')) = RL.of n :=
    RingHom.ext fun a => RL.of_incl n a
  have h2 : (⇑(RL.of (n + 1)) ∘ ![lvar n 0, lvar n 1]) =
      ![RL.of (n + 1) (lvar n 0), RL.of (n + 1) (lvar n 1)] := by
    funext i
    fin_cases i <;> rfl
  have h : MvPolynomial.eval₂Hom (RL.of n) ![RL.of (n + 1) (lvar n 0), RL.of (n + 1) (lvar n 1)] =
      (RL.of (n + 1)).comp (MvPolynomial.eval₂Hom ((toL2 D.A').comp (D.f : A n →+* D.A'))
        ![lvar n 0, lvar n 1]) := by
    calc _ = MvPolynomial.eval₂Hom ((RL.of (n + 1)).comp ((toL2 D.A').comp (D.f : A n →+* D.A')))
          (fun i => RL.of (n + 1) (![lvar n 0, lvar n 1] i)) := by
            rw [h1]
            congr 1
            funext i
            fin_cases i <;> rfl
      _ = _ := (MvPolynomial.comp_eval₂Hom _ _ _).symm
  rw [h]
  exact (RL.of_injective (n + 1)).comp (eval₂_X_injective D.A' _ D.injective)

end CL

namespace RL

lemma range_mono : Monotone fun n => (of n).range := by
  apply monotone_nat_of_le_succ
  rintro n _ ⟨a, rfl⟩
  exact ⟨CL.incl n a, of_incl n a⟩

/-- **`RL` is a fresh target.** -/
def freshTarget : FreshTarget where
  T := RL
  B n := (of n).range
  mono := range_mono
  exhaust t := by
    obtain ⟨n, a, h⟩ := exists_of t
    exact ⟨n, a, h⟩
  fresh n := by
    let c : RLˣ := Units.map (of (n + 1)).toMonoidHom (CL.isUnit_lvar n 0).unit
    refine ⟨c, of (n + 1) (CL.lvar n 1), ⟨_, rfl⟩, ⟨_, (Units.coe_map_inv _ _).symm⟩,
      ⟨_, rfl⟩, ?_⟩
    have := algebraicIndependent_range (of n) (of_injective n) _ (CL.eval₂_lvar_injective n)
    convert this using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  ι := ι
  ι_injective := ι_injective
  ι_mem a := ⟨a, rfl⟩

end RL

/-- **Main theorem for the naive ring.** The Kronecker ring `R_naive`, obtained from `ℚ[x, y]` by
the steps `A ↦ A[σ, τ, a/g, b/g]` with `g = aσ + bτ`, is a Bézout domain that is not an elementary
divisor domain. -/
theorem naive_main_theorem : IsDomain RN ∧ IsBezout RN ∧ ¬ IsElementaryDivisorDomain RN :=
  ⟨RN.isDomain, RN.isBezout, RN.not_isElementaryDivisorDomain RL.freshTarget RL.key_obstruction⟩

end BezoutCounterexample
