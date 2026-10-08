import BezoutCounterexample.Constructive.GCDPoly

/-!
# The generic prime (`~/COLL/bezout-gcd.tex`, Proposition 6.1)

Let `A` be a GCD domain with a zero test and `p₀, …, p_m ∈ A` with `p₀ ≠ 0` and no common
non-unit divisor. Then `π = Σ λᵢ pᵢ` is a prime element of `A[λ₀, …, λ_m]`.

The proof keeps Gauss univariate: over `B = A[λ₁, …, λ_m]` (a GCD domain by
`hasGcd_mvPolynomial`), `π` is the linear polynomial `p₀ X + π'` with `π' = Σ_{i ≥ 1} λᵢ pᵢ`.

* `prime_linear`: in `B[X]`, `a X + b` with `a ≠ 0` and `a, b` coprime is prime. In a GCD
  domain an element with only trivial factorisations is prime, and the factorisations of a
  linear polynomial are decided by degree.
* `isRelPrime_generic`: `p₀` and `π'` are coprime in `B`, since a divisor of the constant `p₀`
  is a constant (total degree), and a constant dividing `π'` divides every `pᵢ`.
* `prime_generic`: transport along `finSuccEquiv`.
-/

namespace BezoutCounterexample.Constructive

open Polynomial

section Linear

variable {B : Type*} [CommRing B] [IsDomain B]

omit [IsDomain B] in
/-- A constant dividing `a X + b` divides `a` and `b`. -/
lemma dvd_of_C_dvd_linear {a b c : B} (h : C c ∣ C a * X + C b) : c ∣ a ∧ c ∣ b := by
  have h1 := (C_dvd_iff_dvd_coeff _ _).1 h
  refine ⟨?_, ?_⟩
  · simpa using h1 1
  · simpa using h1 0

/-- **Linear polynomials with coprime coefficients are prime** over a GCD domain. -/
theorem prime_linear (hG : HasGcd B) (hz : ∀ b : B, b = 0 ∨ b ≠ 0) {a b : B} (ha : a ≠ 0)
    (hab : IsRelPrime a b) : Prime (C a * X + C b) := by
  have hGX := hasGcd_polynomial hG hz
  have hzX := polynomial_eq_zero_or hz
  set π := C a * X + C b with hπ
  have hdeg : π.natDegree = 1 := natDegree_linear ha
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; exact zero_ne_one hdeg
  -- a constant factor of `π` is a unit
  have hconst : ∀ d : B[X], d ∣ π → d.natDegree = 0 → IsUnit d := by
    intro d hd hd0
    rw [eq_C_of_natDegree_eq_zero hd0] at hd ⊢
    obtain ⟨h1, h2⟩ := dvd_of_C_dvd_linear hd
    exact (hab h1 h2).map C
  refine ⟨hπ0, fun hu => ?_, fun x y hxy => ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu
    rw [hdeg] at this; exact one_ne_zero this
  obtain ⟨d, hdπ, hdx, hdc⟩ := hGX π x
  obtain ⟨e, he⟩ := hdπ
  have hd0 : d ≠ 0 := by rintro rfl; exact hπ0 (by rw [he, zero_mul])
  have he0 : e ≠ 0 := by rintro rfl; exact hπ0 (by rw [he, mul_zero])
  have hsum : d.natDegree + e.natDegree = 1 := by rw [← natDegree_mul hd0 he0, ← he, hdeg]
  rcases Nat.eq_zero_or_pos d.natDegree with hd | hd
  · -- `d` is a unit: `π` is coprime to `x`
    have hdu : IsUnit d := hconst d ⟨e, he⟩ hd
    have hrel : IsRelPrime π x := fun c hcπ hcx => isUnit_of_dvd_unit (hdc c hcπ hcx) hdu
    exact Or.inr (dvd_of_isRelPrime_of_dvd_mul hGX hzX hrel hxy)
  · -- `e` is a unit: `π` is associated to `d`, which divides `x`
    have heu : IsUnit e := hconst e ⟨d, by rw [he, mul_comm]⟩ (by omega)
    exact Or.inl (by rw [he]; exact heu.mul_right_dvd.2 hdx)

end Linear

section Generic

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
/-- The coefficient of `λᵢ` in `Σ pⱼ λⱼ`. -/
lemma coeff_single_linear {m : ℕ} (p : Fin m → A) (i : Fin m) :
    (∑ j, MvPolynomial.C (p j) * MvPolynomial.X j).coeff (Finsupp.single i 1) = p i := by
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    split_ifs with h
    · exact absurd (Finsupp.single_left_injective one_ne_zero h) hji
    · rw [mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `p₀` and `π' = Σ pᵢ λᵢ` are coprime in `A[λ₁, …, λ_m]`. -/
theorem isRelPrime_generic {m : ℕ} {p₀ : A} (hp₀ : p₀ ≠ 0) (p : Fin m → A)
    (hrel : ∀ c : A, c ∣ p₀ → (∀ i, c ∣ p i) → IsUnit c) :
    IsRelPrime (MvPolynomial.C p₀ : MvPolynomial (Fin m) A)
      (∑ j, MvPolynomial.C (p j) * MvPolynomial.X j) := by
  intro c ⟨e, he⟩ hcπ
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [zero_mul, MvPolynomial.C_eq_zero] at he; exact hp₀ he
  have he0 : e ≠ 0 := by
    rintro rfl; rw [mul_zero, MvPolynomial.C_eq_zero] at he; exact hp₀ he
  have htd : c.totalDegree = 0 := by
    have := MvPolynomial.totalDegree_mul_of_isDomain (R := A) hc0 he0
    rw [← he, MvPolynomial.totalDegree_C] at this
    omega
  obtain ⟨c₀, rfl⟩ : ∃ c₀, c = MvPolynomial.C c₀ :=
    ⟨_, MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 htd⟩
  refine (hrel c₀ ?_ fun i => ?_).map MvPolynomial.C
  · have := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).1 ⟨e, he⟩ 0
    simpa using this
  · have := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).1 hcπ (Finsupp.single i 1)
    rwa [coeff_single_linear] at this

/-- **The generic element is prime.** -/
theorem prime_generic (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) {m : ℕ}
    (p : Fin (m + 1) → A) (hp₀ : p 0 ≠ 0) (hrel : ∀ c : A, (∀ i, c ∣ p i) → IsUnit c) :
    Prime (∑ i, MvPolynomial.C (p i) * MvPolynomial.X i : MvPolynomial (Fin (m + 1)) A) := by
  obtain ⟨hGB, hzB⟩ := hasGcd_mvPolynomial hG hz m
  let e := MvPolynomial.finSuccEquiv A m
  have himg : e (∑ i, MvPolynomial.C (p i) * MvPolynomial.X i) =
      C (MvPolynomial.C (p 0)) * X +
        C (∑ j : Fin m, MvPolynomial.C (p j.succ) * MvPolynomial.X j) := by
    have hC : ∀ a : A, e (MvPolynomial.C a) = C (MvPolynomial.C a) := fun a => by
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_apply,
        MvPolynomial.algebraMap_eq]
    rw [Fin.sum_univ_succ, map_add, map_mul, hC, MvPolynomial.finSuccEquiv_X_zero, map_sum,
      map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hC, MvPolynomial.finSuccEquiv_X_succ, C_mul]
  have hprime := prime_linear hGB hzB (a := MvPolynomial.C (p 0))
    (by rwa [Ne, MvPolynomial.C_eq_zero])
    (isRelPrime_generic hp₀ (fun j => p j.succ) fun c hc0 hc => hrel c fun i =>
      Fin.cases hc0 hc i)
  rw [← himg] at hprime
  exact (MulEquiv.prime_iff (e.toRingEquiv.toMulEquiv)).1 hprime

end Generic

end BezoutCounterexample.Constructive
