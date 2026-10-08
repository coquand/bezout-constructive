import BezoutCounterexample.Constructive.GCDPoly
import BezoutCounterexample.Constructive.NoethBar

/-!
# Dynamical evaluation in `K[X] ⧸ (f)`, `f` squarefree (D5; `docs/d5-plan.md`, step 1)

`L = K[X] ⧸ (f)` with `f` squarefree is used *as if* it were a field: an element is tested for
invertibility, and when the test fails `f` splits. No factorisation of `f` is needed.

* `exists_bezout_polynomial_field`: extended Euclid in `K[X]`, `K` a field with a zero test (the
  one `@[cprim]` here; it strengthens `exists_isGcd_polynomial_field` by the Bézout identity).
* `dyn_split`: `f = f₁ f₂` with `f₁ ∣ a`, `a` coprime to `f₂`, `f₁` coprime to `f₂`
  (`f₁ = gcd(f, a)`; squarefreeness gives the two coprimalities).
* `dyn_trichotomy`: `a` is coprime to `f`, or `f ∣ a`, or the split is proper (both degrees `> 0`).
* `dynInv`: the same in `L`: `x` is a unit, or `x = 0`, or `f` splits properly with `x = 0` in
  `K[X] ⧸ (f₁)` and `x` a unit in `K[X] ⧸ (f₂)`.
* `quot_eq_zero_or`: the zero test of `L` (from `dyn_trichotomy`; no division by `f` needed).
* `eq_of_proj_eq`: Chinese remainders (injectivity half): `L → K[X]⧸(f₁) × K[X]⧸(f₂)`.
* `dyn_induction`: induction on `deg f` over all points `z : B → K[X] ⧸ (f)`; a step may consult
  the points obtained by projecting to proper factors of smaller degree.
* `ExplicitNS_D5`: the Nullstellensatz with points in `ℚ[X] ⧸ (f)`, `f` squarefree, replacing
  `Principalization.ExplicitNS` (points in a field).
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open Polynomial

section Euclid

variable (K : Type*) [Field K]

/-- **Extended Euclid** in `K[X]` over a field with a zero test (trusted primitive: constructively
valid statement, classical Mathlib proof). -/
@[cprim]
theorem exists_bezout_polynomial_field (_hK : ∀ x : K, x = 0 ∨ x ≠ 0) (f g : K[X]) :
    ∃ h u v : K[X], IsGcd h f g ∧ u * f + v * g = h := by
  classical
  refine ⟨EuclideanDomain.gcd f g, EuclideanDomain.gcdA f g, EuclideanDomain.gcdB f g,
    ⟨EuclideanDomain.gcd_dvd_left f g, EuclideanDomain.gcd_dvd_right f g,
      fun c hcf hcg => EuclideanDomain.dvd_gcd hcf hcg⟩, ?_⟩
  rw [EuclideanDomain.gcd_eq_gcd_ab f g]; ring

variable {K}

/-- Relatively prime polynomials are coprime (Bézout). -/
lemma isCoprime_of_rel (hK : ∀ x : K, x = 0 ∨ x ≠ 0) {a b : K[X]}
    (h : ∀ d, d ∣ a → d ∣ b → IsUnit d) : IsCoprime a b := by
  obtain ⟨g, u, v, hg, huv⟩ := exists_bezout_polynomial_field K hK a b
  obtain ⟨w, hw⟩ := isUnit_iff_dvd_one.1 (h g hg.1 hg.2.1)
  exact ⟨w * u, w * v, by linear_combination w * huv - hw⟩

/-- A divisor of an element it is coprime to is a unit. -/
lemma isUnit_of_isCoprime_of_dvd {R : Type*} [CommRing R] {a g : R} (hc : IsCoprime a g)
    (hd : g ∣ a) : IsUnit g := by
  obtain ⟨u, v, huv⟩ := hc
  exact isUnit_of_dvd_one (huv ▸ dvd_add (dvd_mul_of_dvd_right hd u) (dvd_mul_left g v))

lemma squarefree_of_dvd' {R : Type*} [CommRing R] {f g : R} (hf : Squarefree f) (h : g ∣ f) :
    Squarefree g :=
  fun d hd => hf d (hd.trans h)

end Euclid

section Split

variable {K : Type*} [Field K] (hK : ∀ x : K, x = 0 ∨ x ≠ 0)
include hK

/-- **The D5 splitting**: `f₁ = gcd(f, a)`, `f₂ = f / f₁`. -/
theorem dyn_split {f : K[X]} (hf : Squarefree f) (a : K[X]) :
    ∃ f₁ f₂ : K[X], f = f₁ * f₂ ∧ f₁ ∣ a ∧ IsCoprime a f₂ ∧ IsCoprime f₁ f₂ := by
  obtain ⟨g, -, -, hg, -⟩ := exists_bezout_polynomial_field K hK f a
  obtain ⟨f₂, hf₂⟩ := hg.1
  refine ⟨g, f₂, hf₂, hg.2.1, isCoprime_of_rel hK fun d hda hd₂ => ?_,
    isCoprime_of_rel hK fun d hdg hd₂ => hf d (hf₂ ▸ mul_dvd_mul hdg hd₂)⟩
  have hdf : d ∣ f := hf₂ ▸ dvd_mul_of_dvd_right hd₂ g
  exact hf d (hf₂ ▸ mul_dvd_mul (hg.2.2 d hdf hda) hd₂)

omit hK in
/-- A constant nonzero polynomial is a unit. -/
lemma isUnit_of_natDegree_eq_zero {g : K[X]} (hg : g ≠ 0) (h : g.natDegree = 0) : IsUnit g := by
  rw [eq_C_of_natDegree_eq_zero h] at hg ⊢
  exact (IsUnit.mk0 _ fun h0 => hg (by rw [h0, C_0])).map C

/-- **Trichotomy**: `a` is invertible modulo `f`, or zero modulo `f`, or `f` splits properly. -/
theorem dyn_trichotomy {f : K[X]} (hf : Squarefree f) (hf0 : f ≠ 0) (a : K[X]) :
    IsCoprime a f ∨ f ∣ a ∨ ∃ f₁ f₂ : K[X], f = f₁ * f₂ ∧ 0 < f₁.natDegree ∧ 0 < f₂.natDegree ∧
      f₁ ∣ a ∧ IsCoprime a f₂ ∧ IsCoprime f₁ f₂ := by
  obtain ⟨f₁, f₂, hf₁₂, hd, hc, hc'⟩ := dyn_split hK hf a
  have h₁ : f₁ ≠ 0 := fun h => hf0 (by rw [hf₁₂, h, zero_mul])
  have h₂ : f₂ ≠ 0 := fun h => hf0 (by rw [hf₁₂, h, mul_zero])
  rcases Nat.eq_zero_or_pos f₁.natDegree with e₁ | p₁
  · obtain ⟨w, hw⟩ := isUnit_iff_dvd_one.1 (isUnit_of_natDegree_eq_zero h₁ e₁)
    obtain ⟨u, v, huv⟩ := hc
    exact Or.inl ⟨u, v * w, by rw [hf₁₂]; linear_combination huv - v * f₂ * hw⟩
  rcases Nat.eq_zero_or_pos f₂.natDegree with e₂ | p₂
  · obtain ⟨w, hw⟩ := isUnit_iff_dvd_one.1 (isUnit_of_natDegree_eq_zero h₂ e₂)
    obtain ⟨k, hk⟩ := hd
    exact Or.inr (Or.inl ⟨w * k, by rw [hf₁₂, hk]; linear_combination (f₁ * k) * hw⟩)
  exact Or.inr (Or.inr ⟨f₁, f₂, hf₁₂, p₁, p₂, hd, hc, hc'⟩)

omit hK in
/-- Both factors of a proper split have smaller degree. -/
lemma natDegree_lt_of_split {f f₁ f₂ : K[X]} (hf0 : f ≠ 0) (h : f = f₁ * f₂)
    (p₁ : 0 < f₁.natDegree) (p₂ : 0 < f₂.natDegree) :
    f₁.natDegree < f.natDegree ∧ f₂.natDegree < f.natDegree := by
  have h₁ : f₁ ≠ 0 := fun h' => hf0 (by rw [h, h', zero_mul])
  have h₂ : f₂ ≠ 0 := fun h' => hf0 (by rw [h, h', mul_zero])
  rw [h, natDegree_mul h₁ h₂]
  exact ⟨by omega, by omega⟩

end Split

section Quot

variable {K : Type*} [Field K]

/-- The projection `K[X] ⧸ (f) → K[X] ⧸ (g)` for `g ∣ f`. -/
abbrev proj {f g : K[X]} (h : g ∣ f) : K[X] ⧸ Ideal.span {f} →ₐ[K] K[X] ⧸ Ideal.span {g} :=
  Ideal.Quotient.factorₐ K (Ideal.span_singleton_le_span_singleton.2 h)

lemma proj_mk {f g : K[X]} (h : g ∣ f) (a : K[X]) :
    proj h (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

lemma mk_eq_zero_iff {f a : K[X]} : Ideal.Quotient.mk (Ideal.span {f}) a = 0 ↔ f ∣ a := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

lemma isUnit_mk_of_isCoprime {f a : K[X]} (h : IsCoprime a f) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {f}) a) := by
  obtain ⟨u, v, huv⟩ := h
  refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ u) ?_
  have hv : Ideal.Quotient.mk (Ideal.span {f}) f = 0 := mk_eq_zero_iff.2 dvd_rfl
  rw [← map_mul, mul_comm, show u * a = 1 - v * f by rw [← huv]; ring, map_sub, map_one,
    map_mul, hv, mul_zero, sub_zero]

variable (hK : ∀ x : K, x = 0 ∨ x ≠ 0)
include hK

/-- **Dynamical inverse** in `K[X] ⧸ (f)`. -/
theorem dynInv {f : K[X]} (hf : Squarefree f) (hf0 : f ≠ 0) (x : K[X] ⧸ Ideal.span {f}) :
    IsUnit x ∨ x = 0 ∨ ∃ (f₁ f₂ : K[X]) (h₁ : f₁ ∣ f) (h₂ : f₂ ∣ f), f = f₁ * f₂ ∧
      0 < f₁.natDegree ∧ 0 < f₂.natDegree ∧ IsCoprime f₁ f₂ ∧ proj h₁ x = 0 ∧
      IsUnit (proj h₂ x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rcases dyn_trichotomy hK hf hf0 a with hc | hd | ⟨f₁, f₂, h, p₁, p₂, hd, hc, hc'⟩
  · exact Or.inl (isUnit_mk_of_isCoprime hc)
  · exact Or.inr (Or.inl (mk_eq_zero_iff.2 hd))
  · exact Or.inr (Or.inr ⟨f₁, f₂, ⟨f₂, h⟩, ⟨f₁, h.trans (mul_comm _ _)⟩, h, p₁, p₂, hc',
      mk_eq_zero_iff.2 hd, isUnit_mk_of_isCoprime hc⟩)

/-- **Zero test** in `K[X] ⧸ (f)`. -/
theorem quot_eq_zero_or {f : K[X]} (hf : Squarefree f) (hf0 : f ≠ 0) (hd : 0 < f.natDegree)
    (x : K[X] ⧸ Ideal.span {f}) : x = 0 ∨ x ≠ 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rcases dyn_trichotomy hK hf hf0 a with hc | hfa | ⟨f₁, f₂, h, -, p₂, -, hc, -⟩
  · refine Or.inr fun h0 => ?_
    have := natDegree_eq_zero_of_isUnit (isUnit_of_isCoprime_of_dvd hc (mk_eq_zero_iff.1 h0))
    omega
  · exact Or.inl (mk_eq_zero_iff.2 hfa)
  · refine Or.inr fun h0 => ?_
    have hfa := mk_eq_zero_iff.1 h0
    have := natDegree_eq_zero_of_isUnit
      (isUnit_of_isCoprime_of_dvd hc ((Dvd.intro_left f₁ h.symm).trans hfa))
    omega

omit hK in
/-- **Chinese remainders** (injectivity): an element vanishing in both factors vanishes. -/
theorem eq_zero_of_proj {f f₁ f₂ : K[X]} (h : f = f₁ * f₂) (hc : IsCoprime f₁ f₂)
    (x : K[X] ⧸ Ideal.span {f}) (h₁ : proj (⟨f₂, h⟩ : f₁ ∣ f) x = 0)
    (h₂ : proj (⟨f₁, h.trans (mul_comm _ _)⟩ : f₂ ∣ f) x = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [proj_mk, mk_eq_zero_iff] at h₁ h₂
  exact mk_eq_zero_iff.2 (h ▸ hc.mul_dvd h₁ h₂)

omit hK in
/-- **Dynamical induction** on `deg f` over all points `z : B → K[X] ⧸ (f)`, `f` squarefree. A step
may use the claim at the projections to factors of smaller positive degree. -/
theorem dyn_induction {B : Type*} [CommRing B] [Algebra K B]
    (C : ∀ f : K[X], (B →ₐ[K] K[X] ⧸ Ideal.span {f}) → Prop)
    (step : ∀ (f : K[X]) (z : B →ₐ[K] K[X] ⧸ Ideal.span {f}), Squarefree f → 0 < f.natDegree →
      (∀ (g : K[X]) (hg : g ∣ f), 0 < g.natDegree → g.natDegree < f.natDegree →
        C g ((proj hg).comp z)) → C f z)
    (f : K[X]) (hf : Squarefree f) (hd : 0 < f.natDegree) (z : B →ₐ[K] K[X] ⧸ Ideal.span {f}) :
    C f z := by
  induction h : f.natDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
    subst h
    exact step f z hf hd fun g hg hgd hlt =>
      ih g.natDegree hlt g (squarefree_of_dvd' hf hg) hgd _ rfl

end Quot

/-- **The Nullstellensatz with D5 points**: a finite list not generating `(1)` vanishes at a point
with values in `ℚ[X] ⧸ (f)`, `f` squarefree of positive degree. No factorisation of `f`: it is
split on demand by `dynInv`. -/
def ExplicitNS_D5 (A : Type) [CommRing A] [Algebra ℚ A] : Prop :=
  ∀ l : List A, (1 : A) ∉ lspan l →
    ∃ (f : ℚ[X]) (_ : Squarefree f) (_ : 0 < f.natDegree)
      (z : A →ₐ[ℚ] ℚ[X] ⧸ Ideal.span {f}), ∀ x ∈ l, z x = 0

end BezoutCounterexample.Constructive
