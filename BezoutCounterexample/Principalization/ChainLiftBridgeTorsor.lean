import Mathlib
import BezoutCounterexample.Principalization.ChainLiftBridgeFinal
import BezoutCounterexample.Principalization.MaxLocusPt

/-!
# The torsor presentation presents HM's torsor (bridge, step (1) of the tower)

`G'` (from `Constructive.exists_offStep`) generates the kernel of
`Φ : ℚ[Y, s, y, σ] → B_Q = ℚ[Y, T, W, σ] ⧸ (H₀)`. We show `ℚ[Y, s, y, σ] ⧸ (G') ≅ U`, HM's torsor
`J_R(y)` (`torsor_presentation`), via `Ψ : ℚ[Y, s, y, σ] → U` (`Y ↦ Y`, `s ↦ T⁻¹`,
`yᵢ ↦ Dᵢ yᵢ`, `σᵢ ↦ σᵢ / Dᵢ`):

* `κ : U → J_{A[T^±]}(y)` is injective: it is the localization at `s` (`Jou.isLocalization_map`,
  `isLocalization_away_s`) and `U` is a domain;
* `β : B_Q → J_{A[T^±]}(y)` has a left inverse `γ` (Laurent `eval₂`), so it is injective;
* `κ ∘ Ψ = β ∘ Φ`, hence `ker Ψ = ker Φ = (G')`;
* `Ψ` is surjective: `R = A[T⁻¹, gT^j]` (`reesAlg_eq_adjoin`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] [Fact (Constructive.HasPres A)] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (d : ℕ) {π : A}
  (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

/-- The injection of the torsor into the Jouanolou ring over `A[T^±]`. -/
abbrev torsorκ [Fact (Constructive.HasPres A)] [Constructive.Enum A] : Torsor hI hmax h𝔭 d hπ →+*
    Jou.J (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) A[T;T⁻¹] ∘ torsorY hI hmax h𝔭 d hπ) :=
  Jou.map (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) A[T;T⁻¹]) (torsorY hI hmax h𝔭 d hπ)

set_option maxHeartbeats 1000000 in
include hπ in
/-- **`κ` is injective.** -/
theorem torsorκ_injective [Fact (Constructive.HasPres A)] [Constructive.Enum A] (hπ0 : π ≠ 0) : Function.Injective (torsorκ hI hmax h𝔭 d hπ) := by
  set R := ReesAlg (compFil hI hmax h𝔭 d)
  set s := reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj)
  set y := torsorY hI hmax h𝔭 d hπ
  have := torsor_isDomain hI hmax h𝔭 hπ hπ0
  have : IsLocalization.Away s A[T;T⁻¹] := isLocalization_away_s _ _
  let : Algebra (Torsor hI hmax h𝔭 d hπ) (Jou.J (algebraMap R A[T;T⁻¹] ∘ y)) :=
    (Jou.map (algebraMap R A[T;T⁻¹]) y).toAlgebra
  have hloc : IsLocalization ((Submonoid.powers s).map (algebraMap R (Jou.J y)))
      (Jou.J (algebraMap R A[T;T⁻¹] ∘ y)) := Jou.isLocalization_map y (Submonoid.powers s)
  have hsR : s ≠ 0 := by
    intro h
    have h1 : (s : A[T;T⁻¹]) = 0 := by rw [h]; rfl
    rw [reesS_coe] at h1
    exact (isUnit_T (-1)).ne_zero h1
  have hs0 : algebraMap R (Torsor hI hmax h𝔭 d hπ) s ≠ 0 :=
    (map_ne_zero_iff _ (Jou.algebraMap_injective (torsorY_zero_ne hI hmax h𝔭 hπ hπ0))).2 hsR
  have hle : (Submonoid.powers s).map (algebraMap R (Jou.J y)) ≤
      nonZeroDivisors (Torsor hI hmax h𝔭 d hπ) := by
    rw [Submonoid.map_powers]
    exact powers_le_nonZeroDivisors_of_noZeroDivisors hs0
  exact IsLocalization.injective (Jou.J (algebraMap R A[T;T⁻¹] ∘ y)) hle

section Pres

variable [Fact (Constructive.HasPres A)] [Constructive.Enum A] {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ)) (e : Quo (GQ G) ≃+* A)
  (gZ : Fin (nGen hI hmax h𝔭 d + 1) → MvPolynomial (Fin (m + n)) ℤ)
  (Dg : Fin (nGen hI hmax h𝔭 d + 1) → ℕ)

/-- The degrees `dᵢ = genDegᵢ`. -/
abbrev ddeg : Fin (nGen hI hmax h𝔭 d + 1) → ℕ := fun i => (genDeg hI hmax h𝔭 d i).toNat

lemma ddeg_cast (i : Fin (nGen hI hmax h𝔭 d + 1)) :
    ((ddeg hI hmax h𝔭 d i : ℕ) : ℤ) = genDeg hI hmax h𝔭 d i := by
  have := genDeg_pos hI hmax h𝔭 d i; simp only [ddeg]; omega

/-- The Jouanolou ring over `A[T^±]`. -/
abbrev Jc := Jou.J (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) A[T;T⁻¹] ∘ torsorY hI hmax h𝔭 d hπ)

/-- `A → J_{A[T^±]}(y)`. -/
abbrev aJ : A →+* Jc hI hmax h𝔭 d hπ :=
  (algebraMap A[T;T⁻¹] (Jc hI hmax h𝔭 d hπ)).comp LaurentPolynomial.C

/-- The presented ring `B_Q = ℚ[Y, T, W, σ] ⧸ (H₀)`. -/
abbrev BQ := MvPolynomial (Fin ((m + n) + (2 + (nGen hI hmax h𝔭 d + 1)))) ℚ ⧸
  lspan (H₀ G gZ (ddeg hI hmax h𝔭 d))

/-- The values of `β` on the variables. -/
def bvec : Fin ((m + n) + (2 + (nGen hI hmax h𝔭 d + 1))) → Jc hI hmax h𝔭 d hπ :=
  Fin.append (fun k => aJ hI hmax h𝔭 d hπ (e (Ideal.Quotient.mk _ (X k))))
    (Fin.append (fun j : Fin 2 => if j = 0 then algebraMap A[T;T⁻¹] _ (T 1)
      else algebraMap A[T;T⁻¹] _ (T (-1)))
      (fun i => algebraMap ℚ _ ((Dg i : ℚ)⁻¹) *
        Jou.σ (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) A[T;T⁻¹] ∘ torsorY hI hmax h𝔭 d hπ) i))

lemma aeval_bvec_rename (p : MvPolynomial (Fin (m + n)) ℚ) :
    aeval (bvec hI hmax h𝔭 d hπ G e Dg) (rename (tpY (r := nGen hI hmax h𝔭 d + 1)) p) =
      aJ hI hmax h𝔭 d hπ (e (Ideal.Quotient.mk _ p)) := by
  rw [aeval_rename]
  have : (aeval (bvec hI hmax h𝔭 d hπ G e Dg ∘ tpY)).toRingHom =
      (aJ hI hmax h𝔭 d hπ).comp (e.toRingHom.comp (Ideal.Quotient.mk _)) := by
    refine MvPolynomial.ringHom_ext (fun q => ?_) (fun k => ?_)
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.comp_apply]
      rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      exact (RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ _)
        ((aJ hI hmax h𝔭 d hπ).comp (e.toRingHom.comp (algebraMap ℚ _)))) q)
    · simp [bvec, tpY]
  exact congrArg (fun φ : MvPolynomial (Fin (m + n)) ℚ →+* _ => φ p) this

lemma bvec_tpT : bvec hI hmax h𝔭 d hπ G e Dg tpT = algebraMap A[T;T⁻¹] (Jc hI hmax h𝔭 d hπ) (T 1) := by
  simp [bvec, tpT]
lemma bvec_tpW : bvec hI hmax h𝔭 d hπ G e Dg tpW =
    algebraMap A[T;T⁻¹] (Jc hI hmax h𝔭 d hπ) (T (-1)) := by
  simp [bvec, tpW]
lemma bvec_tpσ (i : Fin (nGen hI hmax h𝔭 d + 1)) : bvec hI hmax h𝔭 d hπ G e Dg (tpσ i) =
    algebraMap ℚ _ ((Dg i : ℚ)⁻¹) *
      Jou.σ (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) A[T;T⁻¹] ∘ torsorY hI hmax h𝔭 d hπ) i := by
  simp [bvec, tpσ]

lemma torsorY_coe (i : Fin (nGen hI hmax h𝔭 d + 1)) :
    (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) A[T;T⁻¹] ∘ torsorY hI hmax h𝔭 d hπ) i =
      LaurentPolynomial.C (genCoeff hI hmax h𝔭 d π i) * T (genDeg hI hmax h𝔭 d i) := rfl

lemma torsorY_coe' (i : Fin (nGen hI hmax h𝔭 d + 1)) :
    algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) A[T;T⁻¹] (torsorY hI hmax h𝔭 d hπ i) =
      LaurentPolynomial.C (genCoeff hI hmax h𝔭 d π i) * T (genDeg hI hmax h𝔭 d i) := rfl

lemma T_one_pow (i : Fin (nGen hI hmax h𝔭 d + 1)) :
    (T 1 : A[T;T⁻¹]) ^ ddeg hI hmax h𝔭 d i = T (genDeg hI hmax h𝔭 d i) := by
  rw [T_pow, mul_one, ddeg_cast (h𝔭 := h𝔭)]

include hπ in
/-- **`β` kills the relations.** -/
lemma bvec_H₀ (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i) :
    ∀ h ∈ H₀ G gZ (ddeg hI hmax h𝔭 d), aeval (bvec hI hmax h𝔭 d hπ G e Dg) h = 0 := by
  intro h hh
  simp only [H₀, H₀Z, List.map_append, List.mem_append, List.mem_map, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with ⟨_, ⟨P, hP, rfl⟩, rfl⟩ | rfl | rfl
  · rw [toQZ, map_rename]
    rw [aeval_bvec_rename (h𝔭 := h𝔭)]
    have : Ideal.Quotient.mk (lspan (GQ G)) (MvPolynomial.map (Int.castRingHom ℚ) P) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (List.mem_map_of_mem hP))
    rw [this, map_zero, map_zero]
  · simp only [map_sub, map_mul, map_X, map_one, aeval_X, bvec_tpT (h𝔭 := h𝔭), bvec_tpW (h𝔭 := h𝔭)]
    rw [← map_mul, ← T_add]; simp
  · simp only [map_sub, map_sum, map_mul, map_pow, map_X, map_one, aeval_X, bvec_tpT (h𝔭 := h𝔭), bvec_tpσ (h𝔭 := h𝔭)]
    rw [sub_eq_zero, ← Jou.sum_σ_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [embYZ, toQZ, map_rename, aeval_bvec_rename (h𝔭 := h𝔭)]
    have hA : e (Ideal.Quotient.mk (lspan (GQ G)) (MvPolynomial.map (Int.castRingHom ℚ) (gZ i))) =
        (Dg i : A) * genCoeff hI hmax h𝔭 d π i := hgZ i
    rw [hA, torsorY_coe (h𝔭 := h𝔭), map_mul, map_mul, ← T_one_pow (h𝔭 := h𝔭), map_pow]
    simp only [aJ, RingHom.comp_apply, map_mul, map_natCast]
    have hD : algebraMap ℚ (Jc hI hmax h𝔭 d hπ) ((Dg i : ℚ)⁻¹) * (Dg i : Jc hI hmax h𝔭 d hπ) = 1 := by
      have e1 : (Dg i : Jc hI hmax h𝔭 d hπ) = algebraMap ℚ _ (Dg i : ℚ) := (map_natCast _ _).symm
      rw [e1, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (hDg i).ne'), map_one]
    linear_combination (Jou.σ _ i * algebraMap A[T;T⁻¹] (Jc hI hmax h𝔭 d hπ)
      (LaurentPolynomial.C (genCoeff hI hmax h𝔭 d π i)) *
        algebraMap A[T;T⁻¹] (Jc hI hmax h𝔭 d hπ) (T 1) ^ ddeg hI hmax h𝔭 d i) * hD

/-- `β : B_Q → J_{A[T^±]}(y)`. -/
def torsorβ (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i) : BQ hI hmax h𝔭 d G gZ →+* Jc hI hmax h𝔭 d hπ :=
  Ideal.Quotient.lift _ (aeval (bvec hI hmax h𝔭 d hπ G e Dg)).toRingHom fun h hh => by
    have hle : lspan (H₀ G gZ (ddeg hI hmax h𝔭 d)) ≤
        RingHom.ker (aeval (bvec hI hmax h𝔭 d hπ G e Dg)).toRingHom := by
      rw [lspan, Ideal.span_le]
      intro x hx
      exact bvec_H₀ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg x hx
    exact hle hh

/-- `A → B_Q`, through the presentation. -/
def φA : A →+* BQ hI hmax h𝔭 d G gZ :=
  (Ideal.Quotient.lift (lspan (GQ G))
    ((Ideal.Quotient.mk _).comp (rename (tpY (r := nGen hI hmax h𝔭 d + 1))).toRingHom)
    fun p hp => by
      have hle : lspan (GQ G) ≤ RingHom.ker ((Ideal.Quotient.mk
          (lspan (H₀ G gZ (ddeg hI hmax h𝔭 d)))).comp
          (rename (tpY (r := nGen hI hmax h𝔭 d + 1))).toRingHom) := by
        rw [lspan, Ideal.span_le]
        intro x hx
        simp only [Set.mem_setOf_eq, GQ, List.mem_map] at hx
        obtain ⟨P, hP, rfl⟩ := hx
        show Ideal.Quotient.mk _ (rename tpY (MvPolynomial.map (Int.castRingHom ℚ) P)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        refine Ideal.subset_span ?_
        show _ ∈ (H₀Z G gZ (ddeg hI hmax h𝔭 d)).map toQZ
        refine List.mem_map.2 ⟨embYZ P, List.mem_append_left _ (List.mem_map_of_mem hP), ?_⟩
        rw [embYZ, toQZ, map_rename]
      exact hle hp).comp e.symm.toRingHom

lemma φA_e (p : MvPolynomial (Fin (m + n)) ℚ) :
    φA hI hmax h𝔭 d G e gZ (e (Ideal.Quotient.mk _ p)) =
      Ideal.Quotient.mk _ (rename (tpY (r := nGen hI hmax h𝔭 d + 1)) p) := by
  simp [φA]

lemma mem_H₀_TW : (X tpT * X tpW - 1 : MvPolynomial (Fin ((m + n) + (2 + (nGen hI hmax h𝔭 d + 1)))) ℚ)
    ∈ lspan (H₀ G gZ (ddeg hI hmax h𝔭 d)) := by
  refine Ideal.subset_span ?_
  show _ ∈ (H₀Z G gZ (ddeg hI hmax h𝔭 d)).map toQZ
  refine List.mem_map.2 ⟨X tpT * X tpW - 1, List.mem_append_right _ (by simp), ?_⟩
  simp

/-- The unit `T` of `B_Q`. -/
def uT : (BQ hI hmax h𝔭 d G gZ)ˣ where
  val := Ideal.Quotient.mk _ (X tpT)
  inv := Ideal.Quotient.mk _ (X tpW)
  val_inv := by
    rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact mem_H₀_TW hI hmax h𝔭 d G gZ
  inv_val := by
    rw [mul_comm, ← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact mem_H₀_TW hI hmax h𝔭 d G gZ

/-- `A[T^±] → B_Q`. -/
def φL : A[T;T⁻¹] →+* BQ hI hmax h𝔭 d G gZ :=
  LaurentPolynomial.eval₂ (φA hI hmax h𝔭 d G e gZ) (uT hI hmax h𝔭 d G gZ)

lemma φL_C (a : A) : φL hI hmax h𝔭 d G e gZ (LaurentPolynomial.C a) = φA hI hmax h𝔭 d G e gZ a := by
  simp [φL]

lemma φL_T (j : ℤ) : φL hI hmax h𝔭 d G e gZ (T j) = ((uT hI hmax h𝔭 d G gZ) ^ j).val := by
  simp [φL]

include hπ in
lemma φL_rel (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i) :
    eval₂Hom (φL hI hmax h𝔭 d G e gZ) (fun i => (Dg i : BQ hI hmax h𝔭 d G gZ) *
      Ideal.Quotient.mk _ (X (tpσ i)))
      (Jou.rel (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) A[T;T⁻¹] ∘ torsorY hI hmax h𝔭 d hπ)) =
        0 := by
  rw [Jou.rel, map_sub, map_sum, map_one, sub_eq_zero]
  -- the image of the relation of `H₀` is zero
  have hrel : Ideal.Quotient.mk (lspan (H₀ G gZ (ddeg hI hmax h𝔭 d)))
      (toQZ (∑ i, X (tpσ i) * embYZ (gZ i) * X tpT ^ ddeg hI hmax h𝔭 d i - 1)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.subset_span (List.mem_map.2 ⟨_, List.mem_append_right _ (by simp), rfl⟩)
  simp only [map_sub, map_sum, map_mul, map_pow, map_X, map_one, sub_eq_zero] at hrel
  rw [← hrel]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, eval₂Hom_X', eval₂Hom_C, Function.comp_apply, torsorY_coe' (h𝔭 := h𝔭), map_mul, φL_C (h𝔭 := h𝔭), φL_T (h𝔭 := h𝔭),
    embYZ, toQZ, map_rename]
  have h1 : (Dg i : BQ hI hmax h𝔭 d G gZ) * φA hI hmax h𝔭 d G e gZ (genCoeff hI hmax h𝔭 d π i) =
      Ideal.Quotient.mk _ (rename tpY (MvPolynomial.map (Int.castRingHom ℚ) (gZ i))) := by
    rw [← map_natCast (φA hI hmax h𝔭 d G e gZ), ← map_mul, ← hgZ i]
    exact φA_e hI hmax h𝔭 d G e gZ _
  have h2 : ((uT hI hmax h𝔭 d G gZ) ^ genDeg hI hmax h𝔭 d i).val =
      Ideal.Quotient.mk _ (X tpT) ^ ddeg hI hmax h𝔭 d i := by
    rw [← ddeg_cast (h𝔭 := h𝔭), zpow_natCast, Units.val_pow_eq_pow_val]; rfl
  rw [h2, ← h1]
  ring

/-- `γ : J_{A[T^±]}(y) → B_Q`, the left inverse of `β`. -/
def torsorγ (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i) : Jc hI hmax h𝔭 d hπ →+* BQ hI hmax h𝔭 d G gZ :=
  Ideal.Quotient.lift _ (eval₂Hom (φL hI hmax h𝔭 d G e gZ)
    (fun i => (Dg i : BQ hI hmax h𝔭 d G gZ) * Ideal.Quotient.mk _ (X (tpσ i)))) fun p hp => by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [map_mul, φL_rel hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg, mul_zero]

lemma torsorγ_alg (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i) (p : A[T;T⁻¹]) :
    torsorγ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg (algebraMap A[T;T⁻¹] (Jc hI hmax h𝔭 d hπ) p) =
      φL hI hmax h𝔭 d G e gZ p := by
  rw [Jou.algebraMap_eq_mk_comp_C, RingHom.comp_apply]
  simp [torsorγ]

lemma torsorγ_σ (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i) (i : Fin (nGen hI hmax h𝔭 d + 1)) :
    torsorγ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg
      (Jou.σ (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) A[T;T⁻¹] ∘ torsorY hI hmax h𝔭 d hπ) i) =
      (Dg i : BQ hI hmax h𝔭 d G gZ) * Ideal.Quotient.mk _ (X (tpσ i)) := by
  simp [torsorγ, Jou.σ]

/-- **`γ ∘ β = id`**, so `β` is injective. -/
theorem torsorγβ (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i) :
    (torsorγ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg).comp (torsorβ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg) =
      RingHom.id _ := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun q => ?_) (fun v => ?_))
  · exact RingHom.congr_fun (RingHom.ext_rat (((torsorγ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg).comp
      (torsorβ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg)).comp ((Ideal.Quotient.mk _).comp C))
      ((RingHom.id _).comp ((Ideal.Quotient.mk _).comp C))) q
  simp only [RingHom.comp_apply, RingHom.id_apply, torsorβ, Ideal.Quotient.lift_mk,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  refine Fin.addCases (fun k => ?_) (fun v => ?_) v
  · have hk : (Fin.castAdd (2 + (nGen hI hmax h𝔭 d + 1)) k : Fin _) = tpY k := rfl
    rw [hk]
    simp only [bvec, tpY, Fin.append_left, aJ, RingHom.comp_apply]
    rw [torsorγ_alg (h𝔭 := h𝔭), φL_C (h𝔭 := h𝔭), φA_e (h𝔭 := h𝔭), rename_X]; rfl
  refine Fin.addCases (fun j => ?_) (fun i => ?_) v
  · fin_cases j
    · have : (Fin.natAdd (m + n) (Fin.castAdd (nGen hI hmax h𝔭 d + 1) (0 : Fin 2))) = tpT := rfl
      simp only [Fin.zero_eta, Fin.isValue] at this ⊢
      rw [this, bvec_tpT (h𝔭 := h𝔭), torsorγ_alg (h𝔭 := h𝔭), φL_T (h𝔭 := h𝔭), zpow_one]; rfl
    · have : (Fin.natAdd (m + n) (Fin.castAdd (nGen hI hmax h𝔭 d + 1) (1 : Fin 2))) = tpW := rfl
      simp only [Fin.mk_one, Fin.isValue] at this ⊢
      rw [this, bvec_tpW (h𝔭 := h𝔭), torsorγ_alg (h𝔭 := h𝔭), φL_T (h𝔭 := h𝔭), zpow_neg, zpow_one]; rfl
  · have : Fin.natAdd (m + n) (Fin.natAdd 2 i) = tpσ i := rfl
    rw [this, bvec_tpσ (h𝔭 := h𝔭), map_mul, torsorγ_σ (h𝔭 := h𝔭)]
    have hq : torsorγ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg (algebraMap ℚ _ ((Dg i : ℚ)⁻¹)) =
        algebraMap ℚ (BQ hI hmax h𝔭 d G gZ) ((Dg i : ℚ)⁻¹) :=
      RingHom.congr_fun (RingHom.ext_rat ((torsorγ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg).comp
        (algebraMap ℚ _)) (algebraMap ℚ _)) _
    rw [hq, ← mul_assoc]
    have : algebraMap ℚ (BQ hI hmax h𝔭 d G gZ) ((Dg i : ℚ)⁻¹) * (Dg i : BQ hI hmax h𝔭 d G gZ) = 1 := by
      have e1 : (Dg i : BQ hI hmax h𝔭 d G gZ) = algebraMap ℚ _ (Dg i : ℚ) := (map_natCast _ _).symm
      rw [e1, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (hDg i).ne'), map_one]
    rw [this, one_mul]

lemma torsorβ_injective (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i) : Function.Injective (torsorβ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg) := by
  intro x y h
  have := congrArg (torsorγ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg) h
  rwa [← RingHom.comp_apply, ← RingHom.comp_apply, torsorγβ (h𝔭 := h𝔭), RingHom.id_apply,
    RingHom.id_apply] at this

/-- The values of `Ψ` on `(Y, s, y, σ)`. -/
def psiVec : Fin ((m + n) + (1 + ((nGen hI hmax h𝔭 d + 1) + (nGen hI hmax h𝔭 d + 1)))) →
    Torsor hI hmax h𝔭 d hπ :=
  Fin.append (fun k => algebraMap A (Torsor hI hmax h𝔭 d hπ) (e (Ideal.Quotient.mk _ (X k))))
    (Fin.append (fun _ : Fin 1 => algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)
      (reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj)))
      (Fin.append (fun i => (Dg i : Torsor hI hmax h𝔭 d hπ) *
        algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) _ (torsorY hI hmax h𝔭 d hπ i))
        (fun i => algebraMap ℚ _ ((Dg i : ℚ)⁻¹) * Jou.σ (torsorY hI hmax h𝔭 d hπ) i)))

/-- `Ψ : ℚ[Y, s, y, σ] → U`. -/
abbrev torsorΨ : MvPolynomial (Fin ((m + n) + (1 + ((nGen hI hmax h𝔭 d + 1) +
    (nGen hI hmax h𝔭 d + 1))))) ℚ →ₐ[ℚ] Torsor hI hmax h𝔭 d hπ :=
  aeval (psiVec hI hmax h𝔭 d hπ G e Dg)

lemma κ_algebraMap_A (a : A) : torsorκ hI hmax h𝔭 d hπ (algebraMap A (Torsor hI hmax h𝔭 d hπ) a) =
    aJ hI hmax h𝔭 d hπ a := by
  rw [IsScalarTower.algebraMap_apply A (ReesAlg (compFil hI hmax h𝔭 d)), Jou.map_algebraMap]
  rfl

lemma κ_algebraMap_ℚ (q : ℚ) : torsorκ hI hmax h𝔭 d hπ (algebraMap ℚ (Torsor hI hmax h𝔭 d hπ) q) =
    algebraMap ℚ _ q :=
  RingHom.congr_fun (RingHom.ext_rat ((torsorκ hI hmax h𝔭 d hπ).comp (algebraMap ℚ _))
    (algebraMap ℚ _)) q

/-- **`κ ∘ Ψ = β ∘ Φ`.** -/
theorem κΨ (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i) :
    (torsorκ hI hmax h𝔭 d hπ).comp (torsorΨ hI hmax h𝔭 d hπ G e Dg).toRingHom =
      (torsorβ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg).comp
        ((Ideal.Quotient.mk _).comp (aeval (fvec gZ (ddeg hI hmax h𝔭 d))).toRingHom) := by
  refine MvPolynomial.ringHom_ext (fun q => ?_) (fun v => ?_)
  · exact RingHom.congr_fun (RingHom.ext_rat (((torsorκ hI hmax h𝔭 d hπ).comp
      (torsorΨ hI hmax h𝔭 d hπ G e Dg).toRingHom).comp C) (((torsorβ hI hmax h𝔭 d hπ G e gZ Dg
        hgZ hDg).comp ((Ideal.Quotient.mk _).comp
          (aeval (fvec gZ (ddeg hI hmax h𝔭 d))).toRingHom)).comp C)) q
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, torsorβ,
    Ideal.Quotient.lift_mk, fvec]
  refine Fin.addCases (fun k => ?_) (fun v => ?_) v
  · simp only [psiVec, fvecZ, Fin.append_left, map_X, aeval_X, κ_algebraMap_A (h𝔭 := h𝔭)]
    simp only [bvec, tpY, Fin.append_left]
  refine Fin.addCases (fun _ => ?_) (fun v => ?_) v
  · simp only [psiVec, fvecZ, Fin.append_left, Fin.append_right, map_X, aeval_X, bvec_tpW (h𝔭 := h𝔭)]
    rw [Jou.map_algebraMap]; rfl
  refine Fin.addCases (fun i => ?_) (fun i => ?_) v
  · simp only [psiVec, fvecZ, Fin.append_left, Fin.append_right, map_mul, map_pow, map_X, aeval_X,
      map_natCast, Jou.map_algebraMap, bvec_tpT]
    rw [embYZ, toQZ, map_rename, aeval_bvec_rename (h𝔭 := h𝔭)]
    have hA : e (Ideal.Quotient.mk (lspan (GQ G)) (MvPolynomial.map (Int.castRingHom ℚ) (gZ i))) =
        (Dg i : A) * genCoeff hI hmax h𝔭 d π i := hgZ i
    rw [hA, ← map_pow, T_one_pow (h𝔭 := h𝔭), torsorY_coe' (h𝔭 := h𝔭)]
    simp only [aJ, RingHom.comp_apply, map_mul, map_natCast]
    ring
  · simp only [psiVec, fvecZ, Fin.append_right, map_mul, map_X, aeval_X, κ_algebraMap_ℚ (h𝔭 := h𝔭),
      Jou.map_σ, bvec_tpσ]

/-- **The kernel of `Ψ` is `(G')`.** -/
theorem ker_torsorΨ (hπ0 : π ≠ 0)
    (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i)
    (G' : List (MvPolynomial (Fin ((m + n) + (1 + ((nGen hI hmax h𝔭 d + 1) +
      (nGen hI hmax h𝔭 d + 1))))) ℤ))
    (hpres : ∀ h, aeval (fvec gZ (ddeg hI hmax h𝔭 d)) h ∈ lspan (H₀ G gZ (ddeg hI hmax h𝔭 d)) ↔
      h ∈ lspan (G'.map toQZ)) :
    RingHom.ker (torsorΨ hI hmax h𝔭 d hπ G e Dg).toRingHom = lspan (G'.map toQZ) := by
  ext h
  rw [RingHom.mem_ker, ← hpres, ← Ideal.Quotient.eq_zero_iff_mem,
    ← (torsorβ_injective hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg).eq_iff, map_zero,
    ← (torsorκ_injective hI hmax h𝔭 d hπ hπ0).eq_iff, map_zero]
  have := congrArg (fun φ : _ →+* _ => φ h) (κΨ hI hmax h𝔭 d hπ G e gZ Dg hgZ hDg)
  simp only [RingHom.comp_apply] at this
  rw [this]; rfl

set_option maxHeartbeats 2000000 in
/-- **`Ψ` is surjective**: `U` is generated by `A`, `T⁻¹`, the `yᵢ` and the `σᵢ`. -/
theorem torsorΨ_surjective (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
    (hDg : ∀ i, 0 < Dg i) : Function.Surjective (torsorΨ hI hmax h𝔭 d hπ G e Dg) := by
  set R := ReesAlg (compFil hI hmax h𝔭 d)
  set U := Torsor hI hmax h𝔭 d hπ
  set S := (torsorΨ hI hmax h𝔭 d hπ G e Dg).range
  have hunit : ∀ i, algebraMap ℚ U ((Dg i : ℚ)⁻¹) * (Dg i : U) = 1 := fun i => by
    have e1 : (Dg i : U) = algebraMap ℚ U (Dg i : ℚ) := (map_natCast _ _).symm
    rw [e1, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (hDg i).ne'), map_one]
  have hX : ∀ v, psiVec hI hmax h𝔭 d hπ G e Dg v ∈ S := fun v => ⟨X v, by simp⟩
  -- `A`
  have hA : ∀ a : A, algebraMap A U a ∈ S := fun a => by
    obtain ⟨y, rfl⟩ := e.surjective a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨rename (Fin.castAdd _) p, ?_⟩
    have : ((torsorΨ hI hmax h𝔭 d hπ G e Dg).comp (rename (Fin.castAdd
        (1 + ((nGen hI hmax h𝔭 d + 1) + (nGen hI hmax h𝔭 d + 1)))))).toRingHom =
        (algebraMap A U).comp (e.toRingHom.comp (Ideal.Quotient.mk _)) := by
      refine MvPolynomial.ringHom_ext (fun q => ?_) (fun k => ?_)
      · exact RingHom.congr_fun (RingHom.ext_rat (((torsorΨ hI hmax h𝔭 d hπ G e Dg).comp
          (rename (Fin.castAdd _))).toRingHom.comp MvPolynomial.C) (((algebraMap A U).comp
            (e.toRingHom.comp (Ideal.Quotient.mk _))).comp MvPolynomial.C)) q
      · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, rename_X,
          aeval_X, psiVec, Fin.append_left, RingHom.comp_apply]; rfl
    exact congrArg (fun φ : MvPolynomial (Fin (m + n)) ℚ →+* U => φ p) this
  have hs : algebraMap R U (reesS (compFil hI hmax h𝔭 d)
      (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj)) ∈ S := by
    have := hX (Fin.natAdd (m + n) (Fin.castAdd _ 0)); simpa [psiVec] using this
  have hy : ∀ i, algebraMap R U (torsorY hI hmax h𝔭 d hπ i) ∈ S := fun i => by
    have := S.mul_mem (S.algebraMap_mem ((Dg i : ℚ)⁻¹))
      (hX (Fin.natAdd (m + n) (Fin.natAdd 1 (Fin.castAdd _ i))))
    simp only [psiVec, Fin.append_right, Fin.append_left] at this
    rwa [← mul_assoc, hunit, one_mul] at this
  have hσ : ∀ i, Jou.σ (torsorY hI hmax h𝔭 d hπ) i ∈ S := fun i => by
    have := S.mul_mem (S.algebraMap_mem (Dg i : ℚ))
      (hX (Fin.natAdd (m + n) (Fin.natAdd 1 (Fin.natAdd _ i))))
    simp only [psiVec, Fin.append_right] at this
    have h1 : algebraMap ℚ U (Dg i : ℚ) * (algebraMap ℚ U ((Dg i : ℚ)⁻¹) *
        Jou.σ (torsorY hI hmax h𝔭 d hπ) i) = Jou.σ (torsorY hI hmax h𝔭 d hπ) i := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 (hDg i).ne'), map_one,
        one_mul]
    rwa [h1] at this
  -- the Rees algebra
  have hRmem : ∀ p : A[T;T⁻¹], p ∈ Algebra.adjoin A (reesGenSet hI hmax h𝔭 d) → p ∈ R :=
    fun p hp => (SetLike.ext_iff.1 (reesAlg_eq_adjoin hI hmax h𝔭 d hd hw) p).2 hp
  have hR : ∀ x : R, algebraMap R U x ∈ S := by
    intro x
    have hx : (x : A[T;T⁻¹]) ∈ Algebra.adjoin A (reesGenSet hI hmax h𝔭 d) :=
      (SetLike.ext_iff.1 (reesAlg_eq_adjoin hI hmax h𝔭 d hd hw) (x : A[T;T⁻¹])).1 x.2
    suffices h : ∀ p (hp : p ∈ Algebra.adjoin A (reesGenSet hI hmax h𝔭 d)),
        algebraMap R U ⟨p, hRmem p hp⟩ ∈ S from h x hx
    intro p hp
    refine Algebra.adjoin_induction (p := fun p hp => algebraMap R U ⟨p, hRmem p hp⟩ ∈ S)
      ?_ ?_ ?_ ?_ hp
    · intro q hq
      rcases hq with hq | hq
      · rw [Set.mem_singleton_iff] at hq
        subst hq
        exact hs
      · simp only [Set.mem_iUnion, Set.mem_image] at hq
        obtain ⟨j, hj, g, hg, rfl⟩ := hq
        obtain ⟨hj1, hjd⟩ := Finset.mem_Icc.1 hj
        obtain ⟨i, hi, hdeg⟩ := gen_covers hI hmax h𝔭 d π j hj1 hjd g hg
        have : (⟨LaurentPolynomial.C g * T j, hRmem _ (Algebra.subset_adjoin (Or.inr (by
            simp only [Set.mem_iUnion, Set.mem_image]
            exact ⟨j, hj, g, hg, rfl⟩)))⟩ : R) = torsorY hI hmax h𝔭 d hπ i := by
          apply Subtype.ext
          rw [show ((torsorY hI hmax h𝔭 d hπ i : R) : A[T;T⁻¹]) =
            LaurentPolynomial.C (genCoeff hI hmax h𝔭 d π i) * T (genDeg hI hmax h𝔭 d i) from rfl,
            hi, hdeg]
        rw [this]; exact hy i
    · intro a
      have : (⟨algebraMap A A[T;T⁻¹] a, hRmem _ (Subalgebra.algebraMap_mem _ a)⟩ : R) =
          algebraMap A R a := rfl
      rw [this, ← IsScalarTower.algebraMap_apply]
      exact hA a
    · intro p q hp hq hp' hq'
      have : (⟨p + q, hRmem _ (Subalgebra.add_mem _ hp hq)⟩ : R) =
          ⟨p, hRmem _ hp⟩ + ⟨q, hRmem _ hq⟩ := rfl
      rw [this, map_add]; exact S.add_mem hp' hq'
    · intro p q hp hq hp' hq'
      have : (⟨p * q, hRmem _ (Subalgebra.mul_mem _ hp hq)⟩ : R) =
          ⟨p, hRmem _ hp⟩ * ⟨q, hRmem _ hq⟩ := rfl
      rw [this, map_mul]; exact S.mul_mem hp' hq'
  -- everything
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  suffices h : Ideal.Quotient.mk _ p ∈ S by obtain ⟨w, hw⟩ := h; exact ⟨w, hw⟩
  induction p using MvPolynomial.induction_on with
  | C x =>
    have : Ideal.Quotient.mk (Ideal.span {Jou.rel (torsorY hI hmax h𝔭 d hπ)}) (MvPolynomial.C x) =
        algebraMap R U x := (Jou.mk_C _ x)
    rw [this]; exact hR x
  | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact S.mul_mem hp (hσ i)

/-- **`G'` presents HM's torsor**: the isomorphism `ℚ[Y, s, y, σ] ⧸ (G') ≃ U` induced by `Ψ`. -/
def torsorEquiv (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) (hπ0 : π ≠ 0)
    (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i)
    (G' : List (MvPolynomial (Fin ((m + n) + (1 + ((nGen hI hmax h𝔭 d + 1) +
      (nGen hI hmax h𝔭 d + 1))))) ℤ))
    (hpres : ∀ h, aeval (fvec gZ (ddeg hI hmax h𝔭 d)) h ∈ lspan (H₀ G gZ (ddeg hI hmax h𝔭 d)) ↔
      h ∈ lspan (G'.map toQZ)) :
    Quo (G'.map toQZ) ≃+* Torsor hI hmax h𝔭 d hπ :=
  (Ideal.quotEquivOfEq (ker_torsorΨ hI hmax h𝔭 d hπ G e gZ Dg hπ0 hgZ hDg G' hpres).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (torsorΨ_surjective hI hmax h𝔭 d hπ G e Dg hd hw hDg))

/-- `torsorEquiv` sends the old variables to their images in `U`. -/
lemma torsorEquiv_X (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) (hπ0 : π ≠ 0)
    (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i)
    (G' : List (MvPolynomial (Fin ((m + n) + (1 + ((nGen hI hmax h𝔭 d + 1) +
      (nGen hI hmax h𝔭 d + 1))))) ℤ))
    (hpres : ∀ h, aeval (fvec gZ (ddeg hI hmax h𝔭 d)) h ∈ lspan (H₀ G gZ (ddeg hI hmax h𝔭 d)) ↔
      h ∈ lspan (G'.map toQZ)) (k : Fin (m + n)) :
    torsorEquiv hI hmax h𝔭 d hπ G e gZ Dg hd hw hπ0 hgZ hDg G' hpres
      (Ideal.Quotient.mk _ (X (Fin.castAdd _ k))) =
      algebraMap A (Torsor hI hmax h𝔭 d hπ) (e (Ideal.Quotient.mk _ (X k))) := by
  unfold torsorEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, psiVec, Fin.append_left]

theorem torsor_presentation (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) (hπ0 : π ≠ 0)
    (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i)
    (G' : List (MvPolynomial (Fin ((m + n) + (1 + ((nGen hI hmax h𝔭 d + 1) +
      (nGen hI hmax h𝔭 d + 1))))) ℤ))
    (hpres : ∀ h, aeval (fvec gZ (ddeg hI hmax h𝔭 d)) h ∈ lspan (H₀ G gZ (ddeg hI hmax h𝔭 d)) ↔
      h ∈ lspan (G'.map toQZ)) :
    Nonempty (Quo (G'.map toQZ) ≃+* Torsor hI hmax h𝔭 d hπ) :=
  ⟨torsorEquiv hI hmax h𝔭 d hπ G e gZ Dg hd hw hπ0 hgZ hDg G' hpres⟩

end Pres

end BezoutCounterexample.Principalization
