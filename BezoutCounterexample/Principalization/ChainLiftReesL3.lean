import Mathlib
import BezoutCounterexample.Principalization.Points
import BezoutCounterexample.Constructive.Colon
import BezoutCounterexample.Constructive.PresentedOps
import BezoutCounterexample.Principalization.ReesSmooth
import BezoutCounterexample.Principalization.RecentrePos

/-!
# The local kernel equality of the Rees model (Task B, Rees layer S5c, L3)

Plan: `docs/pending/rees-cert-design.md` §11.

* **L3-a** `exists_pow_mul_eq_zero_of_pts`: in a presented ring, an element killed near every point
  of `D(d)` is killed by a power of `d` (annihilator by `exists_colon`, radical membership decided by
  `inRad_dec`, a point outside it by `exists_pt_away`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

lemma mem_lspan_nil {R : Type*} [CommRing R] {x : R} : x ∈ lspan ([] : List R) ↔ x = 0 := by
  rw [lspan]
  simp

lemma mem_lspan_singleton {R : Type*} [CommRing R] {x z : R} : x ∈ lspan [z] ↔ ∃ c, c * z = x := by
  rw [lspan, show {y | y ∈ [z]} = ({z} : Set R) by ext; simp]
  exact Ideal.mem_span_singleton'

/-- Rabinowitsch: `b` is nilpotent iff `1 - bX` generates `(1)` (as `DynPrime.isNilpotent_iff_one_mem`,
which is not in the root). -/
lemma l3_isNilpotent_iff_one_mem {B : Type*} [CommRing B] (b : B) :
    IsNilpotent b ↔ (1 : Polynomial B) ∈ lspan [1 - Polynomial.C b * Polynomial.X] := by
  rw [lspan_singleton, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top]
  constructor
  · intro hb
    obtain ⟨n, hn⟩ := hb
    exact IsNilpotent.isUnit_one_sub ⟨n, by
      rw [mul_pow, ← Polynomial.C_pow, hn, Polynomial.C_0, zero_mul]⟩
  · intro hu
    have := (Polynomial.coeff_isUnit_isNilpotent_of_isUnit hu).2 1 one_ne_zero
    rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul_X,
      ite_eq_right_iff.2 (fun h => absurd h one_ne_zero),
      ite_eq_left_iff.2 (fun h => absurd rfl h), zero_sub] at this
    exact neg_neg b ▸ this.neg

/-- **Radical membership is decidable** in a presented ring. -/
lemma l3_rad_dec {B : Type*} [CommRing B] (h : HasPres B) (P : List B) (x : B) :
    (∃ n : ℕ, x ^ n ∈ lspan P) ∨ ¬ ∃ n : ℕ, x ^ n ∈ lspan P := by
  have e : (∃ n : ℕ, x ^ n ∈ lspan P) ↔ IsNilpotent (Ideal.Quotient.mk (lspan P) x) :=
    exists_congr fun n => by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  rw [e, l3_isNilpotent_iff_one_mem]
  exact (h.quotient P).polynomial.mem_dec _ _

/-- **L3-a: local–global for annihilation over points.** If near every point of `D(d)` some element
outside the point kills `z`, a power of `d` kills `z`. -/
theorem exists_pow_mul_eq_zero_of_pts {M : Type} [CommRing M] [Algebra ℚ M] (hp : HasPres M)
    (z d : M) (h : ∀ P : Pt M, d ∉ P.ker → ∃ b, b ∉ P.ker ∧ b * z = 0) :
    ∃ N : ℕ, d ^ N * z = 0 := by
  obtain ⟨C, hC⟩ := hp.exists_colon [] [z]
  have hCiff : ∀ x, x ∈ lspan C ↔ x * z = 0 := fun x => by
    rw [hC]
    constructor
    · intro hx
      exact mem_lspan_nil.1 (hx z (mem_lspan_singleton.2 ⟨1, one_mul z⟩))
    · intro hx y hy
      obtain ⟨c, rfl⟩ := mem_lspan_singleton.1 hy
      rw [mul_left_comm, hx, mul_zero]
      exact mem_lspan_nil.2 rfl
  rcases l3_rad_dec hp C d with ⟨N, hN⟩ | hn
  · exact ⟨N, (hCiff _).1 hN⟩
  · exfalso
    obtain ⟨P, hCP, hdP⟩ := HasPres.exists_pt_away hp C d fun k hk => hn ⟨k, hk⟩
    obtain ⟨b, hbP, hbz⟩ := h P hdP
    exact hbP (hCP ((hCiff b).2 hbz))

/-! ### L3-c, the local core -/

section Local

open LaurentPolynomial hiding C

variable {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ}

/-- The filtration of a chart as a `WFil`. -/
def chartWFil (c : Chart S n) (e : Fin n → ℚ) (d : ℕ) (he : ∀ i, 0 ≤ e i) : WFil S where
  F j := chartFil c e d j
  mul_le a b := chartFil_mul c e d a b
  zero_eq := by
    rw [chartFil, c.RF_of_nonpos he (by simp)]

variable [IsLocalRing S] [Fact (PolyIndNoeth S)] (c : Chart S n) (hc : c.IsCentred)
  {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} (he : ∀ i, 0 ≤ e i) (hd : 0 < d)
  (hw : ∀ i, (w i : ℚ) = d * e i) {k : ℕ} (hkn : k ≤ n) (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k)

/-- The Laurent values of the Rees generators: `s ↦ T⁻¹`, `uᵢ ↦ C(xᵢ) T^{wᵢ}`. -/
def l3Gen (w : Fin n → ℕ) (hkn : k ≤ n) : Option (Fin k) → S[T;T⁻¹] := fun o =>
  o.elim (T (-1)) (fun i => LaurentPolynomial.C (c.x (ιk hkn i)) * T (w (ιk hkn i)))

include hc hsupp he hd hw in
/-- **L3-c, local core**: the kernel of `S[s, u] → S[T^±]`, `s ↦ T⁻¹`, `uᵢ ↦ xᵢ T^{wᵢ}`, is generated
by the relations `xᵢ − s^{wᵢ} uᵢ` (`reesPsi_ker` with the chart's own filtration). -/
theorem l3_ker_local (p : MvPolynomial (Option (Fin k)) S)
    (hp : MvPolynomial.aeval (l3Gen c w hkn) p = 0) :
    p ∈ Ideal.span (Set.range (reesRel c w hkn)) := by
  have hF : ∀ j, (chartWFil c e d he).F j = chartFil c e d j := fun _ => rfl
  rw [← reesPsi_ker c hc hF he hd hw hkn hsupp, RingHom.mem_ker]
  apply Subtype.val_injective
  rw [ZeroMemClass.coe_zero, ← hp]
  have : ((ReesAlg (chartWFil c e d he)).val.comp (reesPsi c hF he hd hw hkn)) =
      MvPolynomial.aeval (l3Gen c w hkn) := by
    rw [reesPsi, MvPolynomial.comp_aeval]
    congr 1
    funext o
    cases o with
    | none => simp [reesGen, l3Gen]
    | some i => simp [reesGen, l3Gen]
  exact congrArg (fun f => f p) this

end Local

/-! ### L3-c, the Laurent case: a head is a unit -/

section Laurent

open LaurentPolynomial hiding C
open MvPolynomial

variable {S : Type*} [CommRing S] {k : ℕ} (x : Fin k → S) (w : Fin k → ℕ)

/-- `s ↦ T⁻¹`, `uᵢ ↦ C(xᵢ) T^{wᵢ}`. -/
def lGen : Option (Fin k) → S[T;T⁻¹] := fun o =>
  o.elim (T (-1)) (fun i => LaurentPolynomial.C (x i) * T (w i))

/-- The relations `xᵢ − s^{wᵢ} uᵢ`. -/
def lRel (i : Fin k) : MvPolynomial (Option (Fin k)) S := C (x i) - X none ^ w i * X (some i)

/-- The model ring `S[s, u]/(xᵢ − s^{wᵢ} uᵢ)`. -/
abbrev LQ := MvPolynomial (Option (Fin k)) S ⧸ Ideal.span (Set.range (lRel x w))

lemma lQ_rel (i : Fin k) :
    (Ideal.Quotient.mk _ (C (x i)) : LQ x w) =
      Ideal.Quotient.mk _ (X none) ^ w i * Ideal.Quotient.mk _ (X (some i)) := by
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- `s` is a unit of the model ring when a head of positive weight has an inverse `xi`. -/
def lUnitS {i₀ : Fin k} (xi : S) (hxi : xi * x i₀ = 1) (hw : 0 < w i₀) : (LQ x w)ˣ where
  val := Ideal.Quotient.mk _ (X none)
  inv := Ideal.Quotient.mk _ (C xi * X (some i₀) * X none ^ (w i₀ - 1))
  val_inv := by
    have h1 : (Ideal.Quotient.mk _ (C (xi * x i₀)) : LQ x w) = 1 := by rw [hxi, C_1, map_one]
    obtain ⟨t, ht⟩ : ∃ t, w i₀ = t + 1 := ⟨w i₀ - 1, by omega⟩
    rw [← h1, C_mul]
    simp only [map_mul, map_pow]
    rw [lQ_rel, ht, Nat.add_sub_cancel, pow_succ]
    ring
  inv_val := by
    have h1 : (Ideal.Quotient.mk _ (C (xi * x i₀)) : LQ x w) = 1 := by rw [hxi, C_1, map_one]
    obtain ⟨t, ht⟩ : ∃ t, w i₀ = t + 1 := ⟨w i₀ - 1, by omega⟩
    rw [← h1, C_mul]
    simp only [map_mul, map_pow]
    rw [lQ_rel, ht, Nat.add_sub_cancel, pow_succ]
    ring

/-- `S[T^±] → model`, `T ↦ s⁻¹`. -/
def lInv {i₀ : Fin k} (xi : S) (hxi : xi * x i₀ = 1) (hw : 0 < w i₀) : S[T;T⁻¹] →+* LQ x w :=
  LaurentPolynomial.eval₂ (algebraMap S (LQ x w)) (lUnitS x w xi hxi hw)⁻¹

/-- The model map `model → S[T^±]`. -/
def lMap : LQ x w →ₐ[S] S[T;T⁻¹] :=
  Ideal.Quotient.liftₐ _ (aeval (lGen x w)) fun p hp => by
    refine (Ideal.span_le.2 ?_ : _ ≤ RingHom.ker (aeval (lGen x w)).toRingHom) hp
    rintro _ ⟨i, rfl⟩
    show aeval (lGen x w) (lRel x w i) = 0
    simp only [lRel, map_sub, map_mul, map_pow, aeval_C, aeval_X, lGen, Option.elim]
    rw [T_pow, mul_comm (T _), mul_assoc, ← T_add]
    rw [show ((w i : ℕ) : ℤ) + (w i : ℤ) * -1 = 0 by ring, T_zero, mul_one,
      ← LaurentPolynomial.C_eq_algebraMap, sub_self]

lemma lInv_lMap {i₀ : Fin k} (xi : S) (hxi : xi * x i₀ = 1) (hw : 0 < w i₀) (q : LQ x w) :
    lInv x w xi hxi hw (lMap x w q) = q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  show ((lInv x w xi hxi hw).comp ((aeval (lGen x w)).toRingHom)) p = Ideal.Quotient.mk _ p
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun o => ?_)
  · simp [lInv, ← LaurentPolynomial.C_eq_algebraMap]; rfl
  · cases o with
    | none =>
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, lGen,
        Option.elim, lInv, LaurentPolynomial.eval₂_T, zpow_neg, zpow_one, inv_inv]
      rfl
    | some i =>
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, lGen,
        Option.elim, lInv, map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T,
        zpow_natCast]
      rw [show algebraMap S (LQ x w) (x i) = Ideal.Quotient.mk _ (C (x i)) from rfl, lQ_rel]
      have hs : ((lUnitS x w xi hxi hw : (LQ x w)ˣ) : LQ x w) = Ideal.Quotient.mk _ (X none) := rfl
      rw [← hs, Units.val_pow_eq_pow_val, mul_right_comm, ← mul_pow, Units.mul_inv, one_pow, one_mul]

/-- **L3-c, Laurent case.** -/
theorem l3_ker_laurent {i₀ : Fin k} (xi : S) (hxi : xi * x i₀ = 1) (hw : 0 < w i₀)
    (p : MvPolynomial (Option (Fin k)) S) (hp : aeval (lGen x w) p = 0) :
    p ∈ Ideal.span (Set.range (lRel x w)) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have := lInv_lMap x w xi hxi hw (Ideal.Quotient.mk _ p)
  rw [show lMap x w (Ideal.Quotient.mk _ p) = 0 from hp, map_zero] at this
  exact this.symm

/-- **G1, rescaling**: the kernel statement for `x` gives the one for `v x` when each `vᵢ` has an
inverse `viᵢ`. -/
theorem l3_ker_rescale (v vi : Fin k → S) (hvi : ∀ i, vi i * v i = 1)
    (hx : ∀ p, aeval (lGen x w) p = 0 → p ∈ Ideal.span (Set.range (lRel x w)))
    (p : MvPolynomial (Option (Fin k)) S) (hp : aeval (lGen (fun i => v i * x i) w) p = 0) :
    p ∈ Ideal.span (Set.range (lRel (fun i => v i * x i) w)) := by
  -- `θ c`: `s ↦ s`, `uᵢ ↦ cᵢ uᵢ`
  let θ : (Fin k → S) → MvPolynomial (Option (Fin k)) S →ₐ[S] MvPolynomial (Option (Fin k)) S :=
    fun c => aeval fun o => o.elim (X none) (fun i => C (c i) * X (some i))
  have hθθ : ∀ q, θ vi (θ v q) = q := by
    intro q
    show ((θ vi).comp (θ v)) q = AlgHom.id S _ q
    congr 1
    refine MvPolynomial.algHom_ext fun o => ?_
    cases o with
    | none => simp [θ]
    | some i =>
      simp only [θ, AlgHom.comp_apply, aeval_X, Option.elim, map_mul, aeval_C, AlgHom.id_apply]
      rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_comm (v i), hvi i, C_1, one_mul]
  have h1 : aeval (lGen x w) (θ v p) = 0 := by
    rw [← hp, ← AlgHom.comp_apply]
    congr 1
    refine MvPolynomial.algHom_ext fun o => ?_
    cases o with
    | none => simp [θ, lGen]
    | some i =>
      simp only [θ, lGen, AlgHom.comp_apply, aeval_X, Option.elim, map_mul, aeval_C]
      rw [← LaurentPolynomial.C_eq_algebraMap, ← mul_assoc, ← map_mul]
  have h2 := Ideal.mem_map_of_mem (θ vi).toRingHom (hx _ h1)
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hθθ, Ideal.map_span] at h2
  refine (Ideal.span_le.2 ?_) h2
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  show θ vi (lRel x w i) ∈ _
  have : θ vi (lRel x w i) = C (vi i) * lRel (fun i => v i * x i) w i := by
    simp only [θ, lRel, map_sub, map_mul, map_pow, aeval_C, aeval_X, Option.elim, algebraMap_eq]
    have hC : (C (x i) : MvPolynomial (Option (Fin k)) S) = C (vi i) * C (v i) * C (x i) := by
      rw [← C_mul, hvi i, C_1, one_mul]
    linear_combination hC
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Laurent

/-! ### L3-e2a: the centred case over a local ring -/

section Centred

open LaurentPolynomial hiding C
open MvPolynomial IsLocalRing

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [Fact (PolyIndNoeth S)]
  [Algebra.FormallySmooth ℚ S] [Algebra.FormallySmooth ℚ (ResidueField S)] {n kc : ℕ}

omit [Algebra.FormallySmooth ℚ S] [Algebra.FormallySmooth ℚ (ResidueField S)] in
lemma l3Gen_eq (c : Chart S n) (w : Fin n → ℕ) (hkn : kc ≤ n) :
    l3Gen c w hkn = lGen (fun i => c.x (ιk hkn i)) (fun i => w (ιk hkn i)) := rfl

/-- **L3-e2a**: over a local ring with an explicit point, a chart whose first `kc` coordinates
lie in the maximal ideal gives the kernel statement for heads `xᵢ = vᵢ · c.x(ιk i)` (`vᵢ` with explicit
inverses): `exists_centred_pos` (keeps those coordinates), `l3_ker_local`, `l3_ker_rescale`. -/
theorem l3_ker_centred {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    (hz : ∀ x : L, x = 0 ∨ x ≠ 0) (ζ : S →ₐ[ℚ] L) (hζ : ∀ x, ζ x = 0 ↔ x ∈ maximalIdeal S)
    (c : Chart S n) (hkn : kc ≤ n) {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i)
    (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < kc) {d : ℕ} (hd : 0 < d) {wf : Fin n → ℕ}
    (hw : ∀ i, (wf i : ℚ) = d * e i) (hmax : ∀ i : Fin kc, c.x (ιk hkn i) ∈ maximalIdeal S)
    (w : Fin kc → ℕ) (hwk : ∀ i, w i = wf (ιk hkn i)) (x v vi : Fin kc → S)
    (hvi : ∀ i, vi i * v i = 1) (hx : ∀ i, x i = v i * c.x (ιk hkn i))
    (p : MvPolynomial (Option (Fin kc)) S) (hp : aeval (lGen x w) p = 0) :
    p ∈ Ideal.span (Set.range (lRel x w)) := by
  obtain ⟨c', hc', hc'x⟩ := Chart.exists_centred_pos hz ζ hζ c
  have hx' : ∀ i : Fin kc, c'.x (ιk hkn i) = c.x (ιk hkn i) := fun i => hc'x _ (hmax i)
  have hw' : w = fun i => wf (ιk hkn i) := funext hwk
  have hxv : x = fun i => v i * c'.x (ιk hkn i) := funext fun i => by rw [hx i, hx' i]
  subst hw' hxv
  refine l3_ker_rescale _ _ v vi hvi (fun p hp => ?_) p hp
  rw [← l3Gen_eq] at hp
  exact l3_ker_local c' hc' he hd hw hkn hsupp p hp

end Centred

/-! ### G2: clearing a localisation of the coefficients -/

section Clear

open MvPolynomial

/-- **G2**: membership in an ideal of `S⁻¹A[σ]` generated by images of `A`-polynomials gives, after
multiplying by some `a ∈ M`, membership over `A`. -/
theorem exists_mul_mem_span_of_loc {A : Type*} [CommRing A] (M : Submonoid A) (Aq : Type*)
    [CommRing Aq] [Algebra A Aq] [IsLocalization M Aq] {σ ι : Type*}
    (rels : ι → MvPolynomial σ A) (p : MvPolynomial σ A)
    (hp : map (algebraMap A Aq) p ∈ Ideal.span (Set.range fun i => map (algebraMap A Aq) (rels i))) :
    ∃ a ∈ M, C a * p ∈ Ideal.span (Set.range rels) := by
  let := MvPolynomial.algebraMvPolynomial (σ := σ) (R := A) (S := Aq)
  have hmap : ∀ q : MvPolynomial σ A,
      algebraMap (MvPolynomial σ A) (MvPolynomial σ Aq) q = map (algebraMap A Aq) q := fun _ => rfl
  have hspan : Ideal.span (Set.range fun i => map (algebraMap A Aq) (rels i)) =
      (Ideal.span (Set.range rels)).map (algebraMap (MvPolynomial σ A) (MvPolynomial σ Aq)) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  rw [hspan, ← hmap, IsLocalization.mem_map_algebraMap_iff (M.map (C (σ := σ)))] at hp
  obtain ⟨⟨a, ⟨_, m, hm, rfl⟩⟩, hpa⟩ := hp
  rw [← map_mul] at hpa
  obtain ⟨⟨_, c, hc, rfl⟩, hc'⟩ := (IsLocalization.eq_iff_exists (M.map (C (σ := σ))) _).1 hpa
  refine ⟨c * m, M.mul_mem hc hm, ?_⟩
  rw [C_mul, mul_assoc, mul_comm (C m), hc']
  exact Ideal.mul_mem_left _ _ a.2

end Clear

end BezoutCounterexample.Principalization
