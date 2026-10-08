import Mathlib
import BezoutCounterexample.Principalization.Chart
import BezoutCounterexample.Constructive.ChainLiftGlue
import BezoutCounterexample.Constructive.ChainLiftChoice

/-!
# Chart data from a chart (bridge (b) of the chain-lifting strand)

`P = ℚ[Y₁ … Y_N]`, `A₀ = P ⧸ (G₀)`, and `S` a localization of `A₀` carrying a chart
`c : Chart S n`. For polynomials `y₁ … yₙ` we produce chart data in the sense of
`Constructive.ChartData`: `(L) B ∂G + V ∂y = c₀`, `(D) ∂G V = 0`, `(X) ∂y V = c₀` in `S`, with
`c₀ = det J`, `J_{l j} = ∂_l (y_j)`.

The key input is (L), the exactness of the conormal sequence. It is obtained without the Kähler
API: the *gradient derivation* `δ : S → S^N ⧸ (∇G)` (`gradDer`, built through the trivial
square-zero extension and the universal property of the localization) satisfies
`δ s = Σ_l ∂_l(s) δ(x_l)` by the chart (`kD_eq_sum`), so `c₀ e_k - (V ∂y)_k` has class zero.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial TrivSqZeroExt BezoutCounterexample.Constructive
open scoped Matrix

-- `CStarMatrix` is reducible to `Matrix`; its `HMul` instance must not be picked for matrices.
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Grad

variable {N : ℕ} (G₀ : List (MvPolynomial (Fin N) ℚ))

/-- The presented ring. -/
abbrev Quo : Type := MvPolynomial (Fin N) ℚ ⧸ lspan G₀

variable {S : Type*} [CommRing S] [Algebra ℚ S] [Algebra (Quo G₀) S] [IsScalarTower ℚ (Quo G₀) S]

/-- Image of a polynomial in `S`. -/
def toS (p : MvPolynomial (Fin N) ℚ) : S := algebraMap (Quo G₀) S (Ideal.Quotient.mk _ p)

lemma toS_add (p q : MvPolynomial (Fin N) ℚ) : toS (S := S) G₀ (p + q) = toS G₀ p + toS G₀ q := by
  simp [toS]

lemma toS_mul (p q : MvPolynomial (Fin N) ℚ) : toS (S := S) G₀ (p * q) = toS G₀ p * toS G₀ q := by
  simp [toS]

lemma toS_C (a : ℚ) : toS (S := S) G₀ (C a) = algebraMap ℚ S a := by
  rw [toS, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap,
    ← IsScalarTower.algebraMap_apply]

lemma toS_G (j : Fin G₀.length) : toS (S := S) G₀ (G₀.get j) = 0 := by
  rw [toS, Ideal.Quotient.eq_zero_iff_mem.2 (get_mem_lspan G₀ j), map_zero]

/-- The gradient of a polynomial, in `S^N`. -/
def gradRow (p : MvPolynomial (Fin N) ℚ) : Fin N → S := fun k => toS G₀ (pderiv k p)

/-- The span of the gradients of the relations. -/
def gradK : Submodule S (Fin N → S) :=
  Submodule.span S (Set.range fun j : Fin G₀.length => gradRow (S := S) G₀ (G₀.get j))

/-- `S^N ⧸ (∇G)`. -/
abbrev GradQ := (Fin N → S) ⧸ gradK (S := S) G₀

example : CommRing (TrivSqZeroExt S (GradQ (S := S) G₀)) := inferInstance
example : Algebra ℚ (TrivSqZeroExt S (GradQ (S := S) G₀)) := inferInstance

/-- `p ↦ (p, [∇p])` on polynomials. -/
def gradP : MvPolynomial (Fin N) ℚ →ₐ[ℚ] TrivSqZeroExt S (GradQ (S := S) G₀) :=
  aeval fun k => inl (toS G₀ (X k)) + inr (Submodule.Quotient.mk (Pi.single k 1))

lemma gradP_apply (p : MvPolynomial (Fin N) ℚ) :
    gradP (S := S) G₀ p = inl (toS G₀ p) + inr (Submodule.Quotient.mk (gradRow G₀ p)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [gradP, aeval_C, algebraMap_eq_inl', toS_C]
    have : gradRow (S := S) G₀ (C a) = 0 := by ext k; simp [gradRow, toS]
    rw [this, Submodule.Quotient.mk_zero, inr_zero, add_zero]
  | add p q hp hq =>
    rw [map_add, hp, hq, toS_add]
    have : gradRow (S := S) G₀ (p + q) = gradRow G₀ p + gradRow G₀ q := by
      ext k; simp [gradRow, toS]
    rw [this, Submodule.Quotient.mk_add, inr_add, inl_add]
    abel
  | mul_X p i hp =>
    rw [map_mul, hp]
    have hX : gradP (S := S) G₀ (X i) =
        inl (toS G₀ (X i)) + inr (Submodule.Quotient.mk (Pi.single i 1)) := by
      rw [gradP, aeval_X]
    rw [hX]
    have hg : gradRow (S := S) G₀ (p * X i) =
        toS (S := S) G₀ (X i) • gradRow G₀ p + toS (S := S) G₀ p • (Pi.single i (1 : S) : Fin N → S) := by
      ext k
      simp only [gradRow, Derivation.leibniz, pderiv_X, smul_eq_mul, Pi.add_apply,
        Pi.smul_apply, toS_add, toS_mul]
      by_cases hk : i = k
      · subst hk; simp [toS, Pi.single_apply]; ring
      · simp [toS, Pi.single_apply, Ne.symm hk, hk]
    rw [hg, toS_mul]
    ext
    · simp
    · simp only [snd_mul, fst_add, fst_inl, fst_inr, add_zero, snd_add, snd_inl, snd_inr,
        zero_add, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul]
      rw [op_smul_eq_smul]
      abel

lemma gradP_G (j : Fin G₀.length) : gradP (S := S) G₀ (G₀.get j) = 0 := by
  rw [gradP_apply, toS_G, inl_zero, zero_add]
  have : (Submodule.Quotient.mk (gradRow (S := S) G₀ (G₀.get j)) : GradQ (S := S) G₀) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨j, rfl⟩)
  rw [this, inr_zero]

/-- The descent to `A₀`. -/
def gradA : Quo G₀ →+* TrivSqZeroExt S (GradQ (S := S) G₀) :=
  Ideal.Quotient.lift _ (gradP (S := S) G₀).toRingHom fun p hp => by
    have hle : lspan G₀ ≤ RingHom.ker (gradP (S := S) G₀).toRingHom := by
      rw [lspan, Ideal.span_le]
      intro g hg
      obtain ⟨j, rfl⟩ := List.get_of_mem hg
      exact gradP_G G₀ j
    exact hle hp

lemma gradA_mk (p : MvPolynomial (Fin N) ℚ) :
    gradA (S := S) G₀ (Ideal.Quotient.mk _ p) = gradP G₀ p := rfl

lemma fst_gradA (a : Quo G₀) : (gradA (S := S) G₀ a).fst = algebraMap (Quo G₀) S a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [gradA_mk, gradP_apply, fst_add, fst_inl, fst_inr, add_zero]; rfl

variable (Mo : Submonoid (Quo G₀)) [IsLocalization Mo S]

lemma gradA_isUnit (m : Mo) : IsUnit (gradA (S := S) G₀ m) := by
  rw [isUnit_iff_isUnit_fst, fst_gradA]
  exact IsLocalization.map_units S m

/-- The lift to `S`. -/
def gradS : S →+* TrivSqZeroExt S (GradQ (S := S) G₀) :=
  IsLocalization.lift (M := Mo) (gradA_isUnit G₀ Mo)

lemma gradS_algebraMap (a : Quo G₀) :
    gradS G₀ Mo (algebraMap (Quo G₀) S a) = gradA G₀ a := IsLocalization.lift_eq _ _

lemma fst_gradS (s : S) : (gradS G₀ Mo s).fst = s := by
  have : (fstHom S S (GradQ (S := S) G₀)).toRingHom.comp (gradS G₀ Mo) = RingHom.id S :=
    IsLocalization.ringHom_ext Mo (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, gradS_algebraMap, RingHom.id_apply]
      exact fst_gradA G₀ a)
  exact congrArg (fun f : S →+* S => f s) this

/-- **The gradient derivation** `δ : S → S^N ⧸ (∇G)`. -/
def gradDer : Derivation ℚ S (GradQ (S := S) G₀) where
  toFun s := (gradS G₀ Mo s).snd
  map_add' s t := by simp
  map_smul' q s := by
    change (gradS G₀ Mo (q • s)).snd = q • (gradS G₀ Mo s).snd
    rw [Algebra.smul_def, map_mul, snd_mul, fst_gradS]
    have h0 : (gradS G₀ Mo (algebraMap ℚ S q)).snd = 0 := by
      rw [IsScalarTower.algebraMap_apply ℚ (Quo G₀) S, gradS_algebraMap,
        ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, gradA_mk, gradP_apply]
      have : gradRow (S := S) G₀ (C q) = 0 := by ext k; simp [gradRow, toS]
      rw [snd_add, snd_inl, snd_inr, zero_add, this, Submodule.Quotient.mk_zero]
    rw [h0, smul_zero, add_zero]
    exact algebraMap_smul S q _
  map_one_eq_zero' := by
    change (gradS G₀ Mo 1).snd = 0
    rw [map_one, snd_one]
  leibniz' s t := by
    change (gradS G₀ Mo (s * t)).snd = s • (gradS G₀ Mo t).snd + t • (gradS G₀ Mo s).snd
    rw [map_mul, snd_mul, fst_gradS, fst_gradS, op_smul_eq_smul, add_comm]

lemma gradDer_toS (p : MvPolynomial (Fin N) ℚ) :
    gradDer (S := S) G₀ Mo (toS G₀ p) = Submodule.Quotient.mk (gradRow G₀ p) := by
  change (gradS G₀ Mo (algebraMap (Quo G₀) S _)).snd = _
  rw [gradS_algebraMap, gradA_mk, gradP_apply, snd_add, snd_inl, snd_inr, zero_add]

/-! ### Chart data in `S` -/

variable {n : ℕ} (c : Chart S n)

/-- `δ s = Σ_l ∂_l(s) δ(x_l)`: the chart spans `Ω`. -/
lemma gradDer_chart (s : S) :
    gradDer (S := S) G₀ Mo s = ∑ l, c.d l s • gradDer (S := S) G₀ Mo (c.x l) := by
  have h := congrArg (gradDer (S := S) G₀ Mo).liftKaehlerDifferential (c.kD_eq_sum s)
  simpa only [Derivation.liftKaehlerDifferential_comp_D, map_sum, map_smul] using h

omit [IsScalarTower ℚ (Quo G₀) S] in
/-- The chain rule for derivations of `S` on polynomial expressions. -/
lemma derivation_toS (D : Derivation ℚ S S) (p : MvPolynomial (Fin N) ℚ) :
    D (toS G₀ p) = ∑ k, toS G₀ (pderiv k p) * D (toS G₀ (X k)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [toS_C, Derivation.map_algebraMap]
    simp [toS]
  | add p q hp hq =>
    rw [toS_add, map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, toS_add, add_mul]
  | mul_X p i hp =>
    rw [toS_mul, Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul, Finset.mul_sum]
    have : ∀ k, toS (S := S) G₀ (pderiv k (p * X i)) =
        toS G₀ (pderiv k p) * toS G₀ (X i) + toS G₀ p * (if i = k then 1 else 0) := by
      intro k
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, toS_add, toS_mul, toS_mul]
      by_cases hk : i = k
      · subst hk; simp [toS]; ring
      · simp [hk, toS]; ring
    simp only [this, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, mul_ite,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by ring
    · ring

/-- `V⁰_{k l} = ∂_l (Y_k)`. -/
def V0 : Matrix (Fin N) (Fin n) S := Matrix.of fun k l => c.d l (toS G₀ (X k))

/-- `J_{l j} = ∂_l (y_j)`. -/
def Jm (y : Fin n → MvPolynomial (Fin N) ℚ) : Matrix (Fin n) (Fin n) S :=
  Matrix.of fun l j => c.d l (toS G₀ (y j))

/-- The gradient matrix of a family of polynomials, in `S`. -/
def jacS {r : ℕ} (p : Fin r → MvPolynomial (Fin N) ℚ) : Matrix (Fin r) (Fin N) S :=
  Matrix.of fun j k => toS G₀ (pderiv k (p j))

omit [IsScalarTower ℚ (Quo G₀) S] in
lemma jacS_mul_V0 {r : ℕ} (p : Fin r → MvPolynomial (Fin N) ℚ) :
    jacS (S := S) G₀ p * V0 G₀ c = Matrix.of fun j l => c.d l (toS G₀ (p j)) := by
  ext j l
  simp only [jacS, V0, Matrix.mul_apply, Matrix.of_apply]
  exact (derivation_toS G₀ (c.d l) (p j)).symm

omit [IsScalarTower ℚ (Quo G₀) S] in
lemma jacS_G_mul_V0 : jacS (S := S) G₀ G₀.get * V0 G₀ c = 0 := by
  rw [jacS_mul_V0]
  ext j l
  simp only [Matrix.of_apply, Matrix.zero_apply]
  rw [toS_G, map_zero]

omit [IsScalarTower ℚ (Quo G₀) S] in
lemma jacS_y_mul_V0 (y : Fin n → MvPolynomial (Fin N) ℚ) :
    jacS (S := S) G₀ y * V0 G₀ c = (Jm G₀ c y)ᵀ := by
  rw [jacS_mul_V0]; ext; simp [Jm]

include Mo in
/-- **Chart data in `S`** for polynomial coordinates `y`: `V = V⁰ adj Jᵀ`, `c₀ = det J`. -/
theorem chartS (y : Fin n → MvPolynomial (Fin N) ℚ) :
    ∃ B : Matrix (Fin N) (Fin G₀.length) S,
      B * jacS G₀ G₀.get + (V0 G₀ c * (Jm G₀ c y)ᵀ.adjugate) * jacS (S := S) G₀ y =
        (Jm G₀ c y).det • (1 : Matrix (Fin N) (Fin N) S) ∧
      jacS (S := S) G₀ G₀.get * (V0 G₀ c * (Jm G₀ c y)ᵀ.adjugate) = 0 ∧
      jacS (S := S) G₀ y * (V0 G₀ c * (Jm G₀ c y)ᵀ.adjugate) =
        (Jm G₀ c y).det • (1 : Matrix (Fin n) (Fin n) S) := by
  set V := V0 G₀ c * (Jm G₀ c y)ᵀ.adjugate
  set c₀ := (Jm G₀ c y).det
  have hJT : jacS (S := S) G₀ y * V0 G₀ c = (Jm G₀ c y)ᵀ := by
    rw [jacS_mul_V0]; ext; simp [Jm]
  have hX : jacS (S := S) G₀ y * V = c₀ • (1 : Matrix (Fin n) (Fin n) S) := by
    rw [← Matrix.mul_assoc, hJT, Matrix.mul_adjugate, Matrix.det_transpose]
  have hD : jacS (S := S) G₀ G₀.get * V = 0 := by
    rw [← Matrix.mul_assoc, jacS_G_mul_V0, Matrix.zero_mul]
  have hVJ : V * (Jm G₀ c y)ᵀ = c₀ • V0 G₀ c := by
    rw [Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.det_transpose, Matrix.mul_smul,
      Matrix.mul_one]
  -- each row of `c₀ - V ∂y` lies in the span of the `∇gⱼ`
  have hrow : ∀ k, (c₀ • Pi.single k 1 - (V * jacS (S := S) G₀ y) k : Fin N → S) ∈ gradK (S := S) G₀ := by
    intro k
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
    have h1 : (Submodule.Quotient.mk (Pi.single k 1 : Fin N → S) : GradQ (S := S) G₀) =
        gradDer (S := S) G₀ Mo (toS G₀ (X k)) := by
      rw [gradDer_toS]
      congr 1
      ext k'
      simp only [gradRow, pderiv_X]
      by_cases h : k = k' <;> simp [Pi.single_apply, h, toS, eq_comm]
    have h2 : (Submodule.Quotient.mk ((V * jacS (S := S) G₀ y) k) : GradQ (S := S) G₀) =
        ∑ j, V k j • gradDer (S := S) G₀ Mo (toS G₀ (y j)) := by
      have : (V * jacS (S := S) G₀ y) k = ∑ j, V k j • gradRow G₀ (y j) := by
        ext k'; simp [Matrix.mul_apply, jacS, gradRow, Finset.sum_apply]
      rw [this, ← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply, gradDer_toS]
    rw [h1, h2, gradDer_chart G₀ Mo c]
    simp only [gradDer_chart G₀ Mo c (toS G₀ (y _)), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← Finset.sum_smul, ← sub_smul]
    have : ∑ j, V k j * c.d l (toS G₀ (y j)) = c₀ * c.d l (toS G₀ (X k)) := by
      have := congrFun (congrFun hVJ k) l
      simpa [Matrix.mul_apply, Jm, V0] using this
    rw [this, sub_self, zero_smul]
  obtain ⟨b, hb⟩ := fin_choice fun k => (Submodule.mem_span_range_iff_exists_fun S).1 (hrow k)
  refine ⟨Matrix.of fun k j => b k j, ?_, hD, hX⟩
  ext k k'
  have h := congrFun (hb k) k'
  rw [Finset.sum_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul, gradRow, Pi.sub_apply] at h
  change ∑ j, b k j * toS G₀ (pderiv k' (G₀.get j)) + (V * jacS (S := S) G₀ y) k k' = _
  rw [h, sub_add_cancel, Matrix.smul_apply]
  by_cases hk : k = k'
  · subst hk; simp
  · simp [hk, Pi.single_apply, Ne.symm hk]

/-! ### Polynomial chart data over `ℚ` -/

/-- `toS` as a ring hom. -/
def toSHom : MvPolynomial (Fin N) ℚ →+* S := (algebraMap (Quo G₀) S).comp (Ideal.Quotient.mk _)

omit [IsScalarTower ℚ (Quo G₀) S] in
lemma toSHom_apply (p : MvPolynomial (Fin N) ℚ) : toSHom (S := S) G₀ p = toS G₀ p := rfl

/-- The polynomial gradient matrix. -/
def jacP {r : ℕ} (p : Fin r → MvPolynomial (Fin N) ℚ) :
    Matrix (Fin r) (Fin N) (MvPolynomial (Fin N) ℚ) :=
  Matrix.of fun j k => pderiv k (p j)

omit [IsScalarTower ℚ (Quo G₀) S] in
lemma jacP_map {r : ℕ} (p : Fin r → MvPolynomial (Fin N) ℚ) :
    (jacP p).map (toSHom (S := S) G₀) = jacS G₀ p := rfl

omit [Algebra ℚ S] in
include Mo in
omit [IsScalarTower ℚ (Quo G₀) S] in
/-- Clearing denominators of finitely many elements of `S`. -/
lemma clear_den {ι : Type*} [Finite ι] (f : ι → S) :
    ∃ (m : Mo) (p : ι → MvPolynomial (Fin N) ℚ),
      ∀ i, toS G₀ (p i) = algebraMap (Quo G₀) S m * f i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite Mo f
  obtain ⟨a, ha⟩ := finite_choice hb
  obtain ⟨p, hp⟩ := finite_choice fun i => Ideal.Quotient.mk_surjective (a i)
  refine ⟨b, p, fun i => ?_⟩
  rw [toS, hp, ha, Algebra.smul_def]

include Mo in
omit [IsScalarTower ℚ (Quo G₀) S] in
/-- Elements vanishing in `S` are killed by one element of `M`, modulo `(G₀)`. -/
lemma kill_zero {ι : Type*} [Fintype ι] (e : ι → MvPolynomial (Fin N) ℚ)
    (h : ∀ i, toS (S := S) G₀ (e i) = 0) :
    ∃ mt : MvPolynomial (Fin N) ℚ, Ideal.Quotient.mk _ mt ∈ Mo ∧ ∀ i, mt * e i ∈ lspan G₀ := by
  obtain ⟨m, hm⟩ := finite_choice fun i => (IsLocalization.map_eq_zero_iff Mo S _).1 (h i)
  obtain ⟨mt, hmt⟩ := Ideal.Quotient.mk_surjective (∏ i, (m i : Quo G₀))
  refine ⟨mt, hmt ▸ Submonoid.prod_mem _ fun i _ => (m i).2, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun i => (m i : Quo G₀)) (Finset.mem_univ i)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hmt, hc, mul_right_comm, hm i, zero_mul]

section RMap
variable {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') {a b : Type*}

lemma rmap_add (A B : Matrix a b R) : (A + B).map f = A.map f + B.map f := by ext; simp
lemma rmap_sub (A B : Matrix a b R) : (A - B).map f = A.map f - B.map f := by ext; simp
lemma rmap_smul (r : R) (A : Matrix a b R) : (r • A).map f = f r • A.map f := by ext; simp
lemma rmap_one [Fintype a] [DecidableEq a] : (1 : Matrix a a R).map f = 1 := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

end RMap

include Mo in
/-- **Chart data over `ℚ`**, modulo `(G₀)`, for polynomial coordinates `y`: the multiplier `c₀`
is `λ · det J` in `S`, with `λ ∈ M`. -/
theorem chartQ (hn : 0 < n) (y : Fin n → MvPolynomial (Fin N) ℚ) :
    ∃ (B : Matrix (Fin N) (Fin G₀.length) (MvPolynomial (Fin N) ℚ))
      (V : Matrix (Fin N) (Fin n) (MvPolynomial (Fin N) ℚ)) (c₀ lam : MvPolynomial (Fin N) ℚ),
      Ideal.Quotient.mk _ lam ∈ Mo ∧
      MatCong (lspan G₀) (B * jacP G₀.get + V * jacP y) (c₀ • 1) ∧
      MatCong (lspan G₀) (jacP G₀.get * V) 0 ∧
      MatCong (lspan G₀) (jacP y * V) (c₀ • 1) ∧
      toS (S := S) G₀ c₀ = toS G₀ lam * (Jm G₀ c y).det := by
  obtain ⟨Bs, hL, -, -⟩ := chartS G₀ Mo c y
  set φ := toSHom (S := S) G₀
  -- 1. the numerators of `V⁰`
  obtain ⟨m₁, V0f, hV0⟩ := clear_den G₀ Mo (fun kl : Fin N × Fin n => V0 G₀ c kl.1 kl.2)
  obtain ⟨m1t, hm1t⟩ := Ideal.Quotient.mk_surjective (m₁ : Quo G₀)
  have hφm1 : φ m1t = algebraMap (Quo G₀) S m₁ := by
    rw [toSHom_apply, toS, hm1t]
  set V0P : Matrix (Fin N) (Fin n) (MvPolynomial (Fin N) ℚ) := Matrix.of fun k l => V0f (k, l)
  have hV0map : V0P.map φ = φ m1t • V0 G₀ c := by
    ext k l
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, V0P]
    rw [toSHom_apply, hV0 (k, l), hφm1]
  set JTP := jacP y * V0P
  have hJT : JTP.map φ = φ m1t • (Jm G₀ c y)ᵀ := by
    rw [Matrix.map_mul, jacP_map, hV0map, Matrix.mul_smul, jacS_y_mul_V0]
  set VP := V0P * JTP.adjugate
  set c0P := JTP.det
  have hn' : n - 1 + 1 = n := by omega
  have hVP : VP.map φ = φ m1t ^ n • (V0 G₀ c * (Jm G₀ c y)ᵀ.adjugate) := by
    have ha : JTP.adjugate.map φ = (JTP.map φ).adjugate := RingHom.map_adjugate φ JTP
    rw [Matrix.map_mul, ha, hV0map, hJT, Matrix.adjugate_smul, Fintype.card_fin,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ', hn']
  have hc0 : φ c0P = φ m1t ^ n * (Jm G₀ c y).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hJT, Matrix.det_smul, Matrix.det_transpose,
      Fintype.card_fin]
  -- 2. (D): `∂G V⁰` vanishes in `S`
  set DV := jacP G₀.get * V0P
  obtain ⟨m2t, hm2, hm2D⟩ := kill_zero (S := S) G₀ Mo (fun jl : Fin G₀.length × Fin n => DV jl.1 jl.2)
    fun jl => by
      have : DV.map φ = 0 := by
        rw [Matrix.map_mul, jacP_map, hV0map, Matrix.mul_smul, jacS_G_mul_V0, smul_zero]
      exact congrFun (congrFun this jl.1) jl.2
  -- 3. (L): the numerators of `B`
  obtain ⟨m₃, Bf, hB⟩ := clear_den G₀ Mo (fun kj : Fin N × Fin G₀.length => Bs kj.1 kj.2)
  obtain ⟨m3t, hm3t⟩ := Ideal.Quotient.mk_surjective (m₃ : Quo G₀)
  have hφm3 : φ m3t = algebraMap (Quo G₀) S m₃ := by rw [toSHom_apply, toS, hm3t]
  set BP : Matrix (Fin N) (Fin G₀.length) (MvPolynomial (Fin N) ℚ) :=
    m1t ^ n • Matrix.of fun k j => Bf (k, j)
  have hBP : BP.map φ = (φ m1t ^ n * φ m3t) • Bs := by
    ext k j
    simp only [BP, Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul,
      map_pow]
    rw [show φ (Bf (k, j)) = toS G₀ (Bf (k, j)) from rfl, hB (k, j), hφm3]; ring
  set E := BP * jacP G₀.get + m3t • (VP * jacP y - c0P • (1 : Matrix (Fin N) (Fin N) _))
  obtain ⟨m4t, hm4, hm4E⟩ := kill_zero (S := S) G₀ Mo (fun kk : Fin N × Fin N => E kk.1 kk.2)
    fun kk => by
      have : E.map φ = 0 := by
        have e1 : E.map φ = (φ m1t ^ n * φ m3t) • (Bs * jacS (S := S) G₀ G₀.get +
            V0 G₀ c * (Jm G₀ c y)ᵀ.adjugate * jacS (S := S) G₀ y -
              (Jm G₀ c y).det • (1 : Matrix (Fin N) (Fin N) S)) := by
          have hjG : (jacP G₀.get).map φ = jacS G₀ G₀.get := jacP_map G₀ _
          have hjy : (jacP y).map φ = jacS G₀ y := jacP_map G₀ _
          simp only [E, rmap_add, rmap_sub, rmap_smul, Matrix.map_mul, hjG, hjy, hBP, hVP, hc0,
            rmap_one, Matrix.smul_mul]
          module
        rw [e1]
        have h0 : Bs * jacS (S := S) G₀ G₀.get + V0 G₀ c * (Jm G₀ c y)ᵀ.adjugate * jacS (S := S) G₀ y -
            (Jm G₀ c y).det • (1 : Matrix (Fin N) (Fin N) S) = 0 := by
          rw [sub_eq_zero]; exact hL
        rw [h0, smul_zero]
      exact congrFun (congrFun this kk.1) kk.2
  -- 4. assemble
  refine ⟨(m2t * m4t) • BP, (m2t * m3t * m4t) • VP, (m2t * m3t * m4t) * c0P,
    m2t * m3t * m4t * m1t ^ n, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, map_mul, map_pow, hm1t]
    exact Mo.mul_mem (Mo.mul_mem (Mo.mul_mem hm2 (hm3t ▸ m₃.2)) hm4) (Mo.pow_mem m₁.2 n)
  · intro k k'
    have h := Ideal.mul_mem_left (lspan G₀) m2t (hm4E (k, k'))
    convert h using 1
    simp only [E, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.smul_mul, Matrix.mul_smul]
    ring
  · intro j l
    rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.zero_apply, sub_zero, smul_eq_mul]
    have : (jacP G₀.get * VP) j l = ∑ l', DV j l' * JTP.adjugate l' l := by
      simp only [VP, DV, ← Matrix.mul_assoc]; rfl
    rw [this, Finset.mul_sum]
    refine Ideal.sum_mem _ fun l' _ => ?_
    have := Ideal.mul_mem_right (JTP.adjugate l' l * (m3t * m4t)) _ (hm2D (j, l'))
    convert this using 1; ring
  · intro j j'
    have : jacP y * VP = c0P • (1 : Matrix (Fin n) (Fin n) _) := by
      simp only [VP, ← Matrix.mul_assoc, JTP, c0P]
      rw [Matrix.mul_adjugate]
    rw [Matrix.mul_smul, this, smul_smul, sub_self]
    exact Ideal.zero_mem _
  · rw [← toSHom_apply, ← toSHom_apply, map_mul, map_mul, map_mul, map_mul, map_mul, map_pow,
      show φ c0P = _ from hc0]
    simp only [φ, map_mul]
    ring

end Grad

end BezoutCounterexample.Principalization
