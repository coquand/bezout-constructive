import Mathlib

/-!
# The Kronecker step

For a domain `R` and `a, b ∈ R`, let `K` be the fraction field of `R[σ, τ]`, put
`g = a σ + b τ` and

  `U = R[σ, τ, a/g, b/g] ⊆ K`.

Then `U` is a domain containing `R`, and `(a, b) U = g U` (`span_pair_eq`).

**Embedding lemma** (`exists_extension`). Let `φ : R ↪ T` be an injective homomorphism into a
domain, and suppose that in `T`
  `φ a = h₀ a'`, `φ b = h₀ b'`, `r₀ a' + s₀ b' = 1`,
with `r₀, s₀, a', b'` and the image of `φ` in a subring `B ⊆ T`, and `c ∈ Tˣ`, `c' ∈ T`
algebraically independent over `B`. Then `σ ↦ c r₀ + c' b'`, `τ ↦ c s₀ - c' a'` extends `φ` to an
injective homomorphism `U → T`. The point is that this substitution is invertible over `B`
(determinant `-1`), so the images of `σ, τ` are algebraically independent over `B`, and
`g ↦ c h₀`, so `a/g ↦ a'/c` and `b/g ↦ b'/c` lie in `T`.
-/

noncomputable section

namespace BezoutCounterexample.Naive

open MvPolynomial

section Step

variable (R : Type*) [CommRing R] [IsDomain R]

/-- The fraction field of `R[σ, τ]`. -/
abbrev KF : Type _ := FractionRing (MvPolynomial (Fin 2) R)

variable {R}

/-- `σ ∈ K`. -/
def σ : KF R := algebraMap (MvPolynomial (Fin 2) R) (KF R) (X 0)

/-- `τ ∈ K`. -/
def τ : KF R := algebraMap (MvPolynomial (Fin 2) R) (KF R) (X 1)

/-- The polynomial `a X₀ + b X₁`. -/
def gPoly (a b : R) : MvPolynomial (Fin 2) R := C a * X 0 + C b * X 1

/-- `g = a σ + b τ ∈ K`. -/
def gen (a b : R) : KF R := algebraMap (MvPolynomial (Fin 2) R) (KF R) (gPoly a b)

lemma algebraMap_KF_apply (r : R) :
    algebraMap R (KF R) r = algebraMap (MvPolynomial (Fin 2) R) (KF R) (C r) := by
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin 2) R) (KF R)]
  rfl

lemma gen_eq (a b : R) : gen a b = algebraMap R (KF R) a * σ + algebraMap R (KF R) b * τ := by
  simp [gen, gPoly, σ, τ, algebraMap_KF_apply]

lemma algebraMap_KF_injective : Function.Injective (algebraMap R (KF R)) := by
  rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 2) R) (KF R)]
  exact (IsFractionRing.injective (MvPolynomial (Fin 2) R) (KF R)).comp (C_injective _ _)

lemma gPoly_ne_zero {a b : R} (h : ¬(a = 0 ∧ b = 0)) : gPoly a b ≠ 0 := by
  intro h0
  apply h
  have h1 := congrArg (fun p : MvPolynomial (Fin 2) R => p.coeff (Finsupp.single 0 1)) h0
  have h2 := congrArg (fun p : MvPolynomial (Fin 2) R => p.coeff (Finsupp.single 1 1)) h0
  simp [gPoly, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Finsupp.single_eq_single_iff] at h1 h2
  exact ⟨h1, h2⟩

lemma gen_ne_zero {a b : R} (h : ¬(a = 0 ∧ b = 0)) : gen a b ≠ 0 := by
  rw [gen, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact gPoly_ne_zero h

/-- The generators of `U`. -/
def gens (a b : R) : Set (KF R) :=
  {σ, τ, algebraMap R (KF R) a / gen a b, algebraMap R (KF R) b / gen a b}

/-- **The Kronecker step** `U = R[σ, τ, a/g, b/g] ⊆ K`. -/
def U (a b : R) : Subalgebra R (KF R) := Algebra.adjoin R (gens a b)

lemma σ_mem (a b : R) : σ ∈ U a b := Algebra.subset_adjoin (by simp [gens])
lemma τ_mem (a b : R) : τ ∈ U a b := Algebra.subset_adjoin (by simp [gens])
lemma divA_mem (a b : R) : algebraMap R (KF R) a / gen a b ∈ U a b :=
  Algebra.subset_adjoin (by simp [gens])
lemma divB_mem (a b : R) : algebraMap R (KF R) b / gen a b ∈ U a b :=
  Algebra.subset_adjoin (by simp [gens])

lemma gen_mem (a b : R) : gen a b ∈ U a b := by
  rw [gen_eq]
  exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ a) (σ_mem a b))
    (mul_mem (Subalgebra.algebraMap_mem _ b) (τ_mem a b))

instance (a b : R) : IsDomain (U a b) := inferInstance

/-- `R → U` is injective. -/
lemma algebraMap_U_injective (a b : R) : Function.Injective (algebraMap R (U a b)) := by
  intro x y h
  apply algebraMap_KF_injective (R := R)
  have := congrArg (fun u : U a b => (u : KF R)) h
  simpa using this

/-- **`(a, b) U = g U`.** -/
theorem span_pair_eq (a b : R) :
    (Ideal.span {a, b} : Ideal R).map (algebraMap R (U a b)) =
      Ideal.span {(⟨gen a b, gen_mem a b⟩ : U a b)} := by
  rw [Ideal.map_span, Set.image_pair]
  set g : U a b := ⟨gen a b, gen_mem a b⟩
  apply le_antisymm
  · rw [Ideal.span_le]
    by_cases h : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp
    have hg : gen a b ≠ 0 := gen_ne_zero h
    have hA : algebraMap R (U a b) a ∈ Ideal.span {g} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨_, divA_mem a b⟩, Subtype.ext ?_⟩
      simp [g, div_mul_cancel₀ _ hg]
    have hB : algebraMap R (U a b) b ∈ Ideal.span {g} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨_, divB_mem a b⟩, Subtype.ext ?_⟩
      simp [g, div_mul_cancel₀ _ hg]
    intro u hu
    rcases hu with rfl | hu
    · exact hA
    · rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact hB
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_pair]
    refine ⟨⟨σ, σ_mem a b⟩, ⟨τ, τ_mem a b⟩, Subtype.ext ?_⟩
    simp only [g, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, gen_eq]
    ring

end Step

/-! ## The embedding lemma -/

section Embedding

variable {R : Type*} [CommRing R] [IsDomain R] {T : Type*} [CommRing T] [IsDomain T]

/-- The invertible linear substitution `X₀ ↦ r₀ X₀ + b' X₁`, `X₁ ↦ s₀ X₀ - a' X₁` over `B`. -/
def linSubst {B : Type*} [CommRing B] (r₀ s₀ a' b' : B) :
    MvPolynomial (Fin 2) B →ₐ[B] MvPolynomial (Fin 2) B :=
  aeval ![C r₀ * X 0 + C b' * X 1, C s₀ * X 0 - C a' * X 1]

lemma linSubst_injective {B : Type*} [CommRing B] {r₀ s₀ a' b' : B}
    (h : r₀ * a' + s₀ * b' = 1) : Function.Injective (linSubst r₀ s₀ a' b') := by
  have hC : (C (r₀ * a' + s₀ * b') : MvPolynomial (Fin 2) B) = 1 := by rw [h, map_one]
  simp only [map_add, map_mul] at hC
  have hinv : (linSubst a' s₀ r₀ b').comp (linSubst r₀ s₀ a' b') = AlgHom.id B _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [linSubst]
      linear_combination X 0 * hC
    · simp [linSubst]
      linear_combination X 1 * hC
  intro p q hpq
  have := congrArg (linSubst a' s₀ r₀ b') hpq
  simpa [← AlgHom.comp_apply, hinv] using this

variable (φ : R →+* T) {a b : R} {h₀ a' b' r₀ s₀ : T} (B : Subring T)
  (hφB : ∀ x, φ x ∈ B) (hr₀ : r₀ ∈ B) (hs₀ : s₀ ∈ B) (ha' : a' ∈ B) (hb' : b' ∈ B)
  (c : Tˣ) (c' : T)

/-- The homomorphism `θ : R[σ, τ] → T`, `σ ↦ c r₀ + c' b'`, `τ ↦ c s₀ - c' a'`. -/
def θ (r₀ s₀ a' b' : T) (c : Tˣ) (c' : T) : MvPolynomial (Fin 2) R →+* T :=
  eval₂Hom φ ![(c : T) * r₀ + c' * b', (c : T) * s₀ - c' * a']

include hφB hr₀ hs₀ ha' hb' in
/-- `θ` is injective. -/
theorem θ_injective (hφ : Function.Injective φ) (hrs : r₀ * a' + s₀ * b' = 1)
    (hind : AlgebraicIndependent B ![(c : T), c']) :
    Function.Injective (θ (R := R) φ r₀ s₀ a' b' c c') := by
  set φB : R →+* B := φ.codRestrict B hφB
  have hφB_inj : Function.Injective φB := fun x y h => hφ (congrArg Subtype.val h)
  let r₀B : B := ⟨r₀, hr₀⟩
  let s₀B : B := ⟨s₀, hs₀⟩
  let a'B : B := ⟨a', ha'⟩
  let b'B : B := ⟨b', hb'⟩
  have hrsB : r₀B * a'B + s₀B * b'B = 1 := Subtype.ext (by simpa using hrs)
  have hB : ∀ x : B, algebraMap B T x = x := fun _ => rfl
  -- `θ = aeval (c, c') ∘ linSubst ∘ map φB`
  have hfac : θ φ r₀ s₀ a' b' c c' =
      ((aeval ![(c : T), c'] : MvPolynomial (Fin 2) B →ₐ[B] T).toRingHom.comp
        (linSubst r₀B s₀B a'B b'B).toRingHom).comp (map φB) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [θ, φB]
      rfl
    · intro i
      fin_cases i <;> simp [θ, linSubst, r₀B, s₀B, a'B, b'B, hB] <;> ring
  intro p q hpq
  rw [hfac] at hpq
  have h1 := (algebraicIndependent_iff_injective_aeval.1 hind) hpq
  exact map_injective φB hφB_inj (linSubst_injective hrsB h1)

/-- The subring of `T` generated by the image of `φ` and the images of the generators of `U`. -/
def imgRing (φ : R →+* T) (r₀ s₀ a' b' : T) (c : Tˣ) (c' : T) : Subring T :=
  Subring.closure (Set.range φ ∪
    {(c : T) * r₀ + c' * b', (c : T) * s₀ - c' * a', a' * ↑c⁻¹, b' * ↑c⁻¹})

include hφB hr₀ hs₀ ha' hb' in
/-- **The embedding lemma.** `φ` extends to an injective homomorphism `U → T`, with image in the
subring generated by the image of `φ`, `c r₀ + c' b'`, `c s₀ - c' a'`, `a'/c` and `b'/c`. -/
theorem exists_extension (hφ : Function.Injective φ) (a b : R)
    (ha : φ a = h₀ * a') (hb : φ b = h₀ * b') (hrs : r₀ * a' + s₀ * b' = 1)
    (hind : AlgebraicIndependent B ![(c : T), c']) :
    ∃ ψ : U a b →+* T, Function.Injective ψ ∧ (∀ x, ψ (algebraMap R (U a b) x) = φ x) ∧
      ∀ u, ψ u ∈ imgRing φ r₀ s₀ a' b' c c' := by
  have hθ := θ_injective φ B hφB hr₀ hs₀ ha' hb' c c' hφ hrs hind
  set θ' := θ (R := R) φ r₀ s₀ a' b' c c' with hθ'
  set j := algebraMap T (FractionRing T)
  have hj : Function.Injective j := IsFractionRing.injective T (FractionRing T)
  set Θ : KF R →+* FractionRing T :=
    IsFractionRing.lift (A := MvPolynomial (Fin 2) R) (K := KF R) (g := j.comp θ') (hj.comp hθ)
  have hΘ : ∀ p, Θ (algebraMap _ (KF R) p) = j (θ' p) := fun p =>
    IsFractionRing.lift_algebraMap (A := MvPolynomial (Fin 2) R) (K := KF R) (hj.comp hθ) p
  set S := imgRing φ r₀ s₀ a' b' c c'
  have hS : ∀ x, x ∈ Set.range φ ∪
      {(c : T) * r₀ + c' * b', (c : T) * s₀ - c' * a', a' * ↑c⁻¹, b' * ↑c⁻¹} → x ∈ S :=
    fun x hx => Subring.subset_closure hx
  have hθX0 : θ' (X 0) = (c : T) * r₀ + c' * b' := by simp [hθ', θ]
  have hθX1 : θ' (X 1) = (c : T) * s₀ - c' * a' := by simp [hθ', θ]
  have hθC : ∀ r, θ' (C r) = φ r := by simp [hθ', θ]
  have hθg : θ' (gPoly a b) = h₀ * c := by
    simp only [gPoly, map_add, map_mul, hθC, hθX0, hθX1, ha, hb]
    linear_combination (h₀ * (c : T)) * hrs
  -- the generators `a/g`, `b/g`
  have hdiv : ∀ (e e' : R) (e₀ : T), φ e = h₀ * e₀ → e₀ * ↑c⁻¹ ∈ S →
      ∃ t ∈ S, Θ (algebraMap R (KF R) e / gen a b) = j t := by
    intro e e' e₀ he hmem
    rw [map_div₀, algebraMap_KF_apply, hΘ, gen, hΘ, hθC, hθg, he]
    by_cases h0 : h₀ = 0
    · exact ⟨0, zero_mem _, by simp [h0]⟩
    · refine ⟨e₀ * ↑c⁻¹, hmem, ?_⟩
      have hc0 : j (h₀ * c) ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ hj]
        exact mul_ne_zero h0 c.ne_zero
      rw [div_eq_iff hc0, ← map_mul]
      congr 1
      rw [show e₀ * ↑c⁻¹ * (h₀ * ↑c) = h₀ * e₀ * (↑c⁻¹ * ↑c) by ring, Units.inv_mul, mul_one]
  have hmem : ∀ u ∈ U a b, ∃ t ∈ S, Θ u = j t := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem x hx =>
      simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨(c : T) * r₀ + c' * b', hS _ (Or.inr (by simp)), by rw [σ, hΘ, hθX0]⟩
      · exact ⟨(c : T) * s₀ - c' * a', hS _ (Or.inr (by simp)), by rw [τ, hΘ, hθX1]⟩
      · exact hdiv a b a' ha (hS _ (Or.inr (by simp)))
      · exact hdiv b a b' hb (hS _ (Or.inr (by simp)))
    | algebraMap r =>
      exact ⟨φ r, hS _ (Or.inl ⟨r, rfl⟩), by rw [algebraMap_KF_apply, hΘ, hθC]⟩
    | add x y _ _ hx hy =>
      obtain ⟨tx, htx, hx⟩ := hx
      obtain ⟨ty, hty, hy⟩ := hy
      exact ⟨tx + ty, add_mem htx hty, by rw [map_add, hx, hy, map_add]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨tx, htx, hx⟩ := hx
      obtain ⟨ty, hty, hy⟩ := hy
      exact ⟨tx * ty, mul_mem htx hty, by rw [map_mul, hx, hy, map_mul]⟩
  choose f hfS hf using fun u : U a b => hmem u u.2
  let ψ : U a b →+* T :=
    { toFun := f
      map_one' := hj (by rw [← hf, map_one]; simp)
      map_mul' := fun x y => hj (by rw [map_mul, ← hf, ← hf, ← hf]; simp)
      map_zero' := hj (by rw [← hf, map_zero]; simp)
      map_add' := fun x y => hj (by rw [map_add, ← hf, ← hf, ← hf]; simp) }
  refine ⟨ψ, fun u v huv => ?_, fun x => hj ?_, fun u => hfS u⟩
  · apply Subtype.ext
    apply Θ.injective
    rw [hf u, hf v]
    exact congrArg j huv
  · show j (f _) = j (φ x)
    rw [← hf]
    simp [algebraMap_KF_apply, hΘ, hθC]

end Embedding

end BezoutCounterexample.Naive
