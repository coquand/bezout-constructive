import BezoutCounterexample.Constructive.DynGCDPoly
import BezoutCounterexample.Constructive.DynJou
import BezoutCounterexample.Constructive.JouGCD

/-!
# Jouanolou rings over GCD domains, up to an escape (D5; `docs/d5-plan.md`, step 4, O6)

`GenericPrime.lean` and `JouGCD.hasGcd_jou` with the gcds of `B` (and the coprimality of the row)
only **up to `Q`**.

* `prime_linearQ`, `isRelPrimeQ_generic`, `prime_genericQ`: `π = Σ cᵢ λᵢ` is prime up to `Q`.
* `jouπ_primeQ`: `π` is prime up to `Q` in `J_{B[λ]}(π, c)`: `Constructive.jou_dyn_l` with
  `𝔞 = (π)` (decidable by divisibility in `B[λ]`) and the entry `c₀ ∉ (π)`; no quotient domain.
* `jouπ_not_isUnit`: evaluation `λ ↦ 0`, `σ₁ ↦ 1/c₀` into `Frac(B)` sends `π` to `0`.
* `hasGcdQ_of_mvPolynomial`: descent of gcds from `R[X]` to `R`, up to `Q`.
* `hasGcdQ_jou`: `J_B(c)` has gcds up to `Q` (Nagata at `π` by `hasGcd_of_away_dyn`).
-/

namespace BezoutCounterexample.Constructive

open Polynomial

section Linear

variable {B : Type*} [CommRing B] [IsDomain B] {Q : Prop}

/-- **Linear polynomials with coefficients coprime up to `Q` are prime up to `Q`.** -/
theorem prime_linearQ (hG : HasGcdQ Q B) (hz : ∀ b : B, b = 0 ∨ b ≠ 0) {a b : B} (ha : a ≠ 0)
    (hab : IsRelPrimeQ Q a b) (x y : B[X]) (hxy : C a * X + C b ∣ x * y) :
    C a * X + C b ∣ x ∨ C a * X + C b ∣ y ∨ Q := by
  have hGX := hasGcdQ_polynomial hG hz
  have hzX := polynomial_eq_zero_or hz
  set π := C a * X + C b with hπ
  have hdeg : π.natDegree = 1 := natDegree_linear ha
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; exact zero_ne_one hdeg
  have hconst : ∀ d : B[X], d ∣ π → d.natDegree = 0 → IsUnit d ∨ Q := by
    intro d hd hd0
    rw [eq_C_of_natDegree_eq_zero hd0] at hd ⊢
    obtain ⟨h1, h2⟩ := dvd_of_C_dvd_linear hd
    exact (hab _ h1 h2).imp_left (·.map C)
  obtain ⟨d, hdπ, hdx, hdc⟩ := hGX π x
  rcases hdπ with ⟨e, he⟩ | hQ
  swap; · exact Or.inr (Or.inr hQ)
  rcases hdx with hdx | hQ
  swap; · exact Or.inr (Or.inr hQ)
  have hd0 : d ≠ 0 := by rintro rfl; exact hπ0 (by rw [he, zero_mul])
  have he0 : e ≠ 0 := by rintro rfl; exact hπ0 (by rw [he, mul_zero])
  have hsum : d.natDegree + e.natDegree = 1 := by rw [← natDegree_mul hd0 he0, ← he, hdeg]
  rcases Nat.eq_zero_or_pos d.natDegree with hd | hd
  · rcases hconst d ⟨e, he⟩ hd with hdu | hQ
    swap; · exact Or.inr (Or.inr hQ)
    have hrel : IsRelPrimeQ Q π x := fun c hcπ hcx =>
      (hdc c hcπ hcx).imp_left fun h => isUnit_of_dvd_unit h hdu
    rcases dvd_of_isRelPrimeQ_of_dvd_mul hGX hzX hrel hxy with h | hQ
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr hQ)
  · rcases hconst e ⟨d, by rw [he, mul_comm]⟩ (by omega) with heu | hQ
    · exact Or.inl (by rw [he]; exact heu.mul_right_dvd.2 hdx)
    · exact Or.inr (Or.inr hQ)

end Linear

section Generic

variable {A : Type*} [CommRing A] [IsDomain A] {Q : Prop}

/-- `p₀` and `Σ pᵢ λᵢ` are coprime up to `Q`. -/
theorem isRelPrimeQ_generic {m : ℕ} {p₀ : A} (hp₀ : p₀ ≠ 0) (p : Fin m → A)
    (hrel : ∀ c : A, c ∣ p₀ → (∀ i, c ∣ p i) → IsUnit c ∨ Q) :
    IsRelPrimeQ Q (MvPolynomial.C p₀ : MvPolynomial (Fin m) A)
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
  refine (hrel c₀ ?_ fun i => ?_).imp_left (·.map MvPolynomial.C)
  · have := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).1 ⟨e, he⟩ 0
    simpa using this
  · have := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).1 hcπ (Finsupp.single i 1)
    rwa [coeff_single_linear] at this

/-- **The generic element is prime up to `Q`.** -/
theorem prime_genericQ (hG : HasGcdQ Q A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) {m : ℕ}
    (p : Fin (m + 1) → A) (hp₀ : p 0 ≠ 0) (hrel : ∀ c : A, (∀ i, c ∣ p i) → IsUnit c ∨ Q)
    (x y : MvPolynomial (Fin (m + 1)) A)
    (hxy : (∑ i, MvPolynomial.C (p i) * MvPolynomial.X i) ∣ x * y) :
    (∑ i, MvPolynomial.C (p i) * MvPolynomial.X i) ∣ x ∨
      (∑ i, MvPolynomial.C (p i) * MvPolynomial.X i) ∣ y ∨ Q := by
  obtain ⟨hGB, hzB⟩ := hasGcdQ_mvPolynomial hG hz m
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
  clear_value e
  have hxy' : e (∑ i, MvPolynomial.C (p i) * MvPolynomial.X i) ∣ e x * e y := by
    obtain ⟨w, hw⟩ := hxy
    exact ⟨e w, by rw [← map_mul, hw, map_mul]⟩
  rw [himg] at hxy'
  have h := prime_linearQ hGB hzB (a := MvPolynomial.C (p 0))
    (by rwa [Ne, MvPolynomial.C_eq_zero])
    (isRelPrimeQ_generic hp₀ (fun j => p j.succ) fun c hc0 hc => hrel c fun i =>
      Fin.cases hc0 hc i) (e x) (e y) hxy'
  rw [← himg, map_dvd_iff, map_dvd_iff] at h
  exact h

end Generic

section Descent

variable {R : Type*} [CommRing R] [IsDomain R] {Q : Prop}

/-- **Descent of gcds** from `R[X₁, …, Xₙ]` to `R`, up to `Q`. -/
theorem hasGcdQ_of_mvPolynomial (hz : ∀ a : R, a = 0 ∨ a ≠ 0) {n : ℕ}
    (h : HasGcdQ Q (MvPolynomial (Fin n) R)) : HasGcdQ Q R := by
  intro a b
  rcases hz a with rfl | ha
  · exact ⟨b, isGcdQ_of_isGcd Q (isGcd_zero_left b)⟩
  obtain ⟨G, hGa, hGb, hGc⟩ := h (MvPolynomial.C a) (MvPolynomial.C b)
  rcases hGa with hGa | hQ
  swap; · exact ⟨0, isGcdQ_of_Q hQ _ _ _⟩
  obtain ⟨g, rfl⟩ := exists_eq_C_of_dvd_C ha hGa
  exact ⟨g, Or.inl (dvd_of_C_dvd_C hGa), hGb.imp_left dvd_of_C_dvd_C,
    fun c hca hcb => (hGc _ (_root_.map_dvd MvPolynomial.C hca)
      (_root_.map_dvd MvPolynomial.C hcb)).imp_left dvd_of_C_dvd_C⟩

end Descent

section Main

variable {B : Type*} [CommRing B] [IsDomain B] {r : ℕ} (c : Fin (r + 1) → B) {Q : Prop}

omit [IsDomain B] in
lemma genRow_one : genRow c 1 = MvPolynomial.C (c 0) := rfl

omit [IsDomain B] in
lemma genπ_ne_zero (hc0 : c 0 ≠ 0) : genπ c ≠ 0 := fun h => hc0 (by
  have := genπ_coeff c 0
  rw [h] at this
  simpa using this.symm)

/-- `π` is not a unit of `J_{B[λ]}(π, c)`: evaluate `λ ↦ 0` into `Frac(B)`. -/
lemma jouπ_not_isUnit (hc0 : c 0 ≠ 0) : ¬ IsUnit (genπJ c) := by
  intro hu
  let K := FractionRing B
  let φ : MvPolynomial (Fin (r + 1)) B →+* K :=
    MvPolynomial.eval₂Hom (algebraMap B K) fun _ => 0
  have hc : φ (genRow c 1) ≠ 0 := by
    rw [genRow_one]
    simp only [φ, MvPolynomial.eval₂Hom_C]
    exact fun h => hc0 ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective B K) _ h)
  have hπ : φ (genπ c) = 0 := by simp [φ, genπ]
  have := hu.map (Jou.elim (c := genRow c) (l := 1) φ (Units.mk0 _ hc) rfl)
  have h2 := Jou.elim_algebraMap (c := genRow c) (l := 1) φ (Units.mk0 _ hc) rfl (genπ c)
  rw [hπ, MvPolynomial.C_0] at h2
  exact not_isUnit_zero (h2 ▸ this)

/-- **`π` is prime up to `Q` in `J_{B[λ]}(π, c)`.** -/
theorem jouπ_primeQ (hπQ : ∀ x y, genπ c ∣ x * y → genπ c ∣ x ∨ genπ c ∣ y ∨ Q)
    (hdvdπ : ∀ x, genπ c ∣ x ∨ ¬ genπ c ∣ x) (hc0 : c 0 ≠ 0) (u v : genJ c)
    (huv : genπJ c ∣ u * v) : genπJ c ∣ u ∨ genπJ c ∣ v ∨ Q := by
  have hmem : ∀ w : genJ c, genπJ c ∣ w ↔
      w ∈ (Ideal.span {genπ c}).map (algebraMap _ (genJ c)) := fun w => by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have hcl : genRow c 1 ∉ Ideal.span {genπ c} := by
    rw [Ideal.mem_span_singleton, genRow_one]; exact not_dvd_genπ c hc0 hc0
  rw [hmem] at huv
  rw [hmem, hmem]
  have hdec : ∀ x, x ∈ Ideal.span {genπ c} ∨ x ∉ Ideal.span {genπ c} := fun x => by
    rw [Ideal.mem_span_singleton]; exact hdvdπ x
  have hpr : ∀ x y, x * y ∈ Ideal.span {genπ c} →
      x ∈ Ideal.span {genπ c} ∨ y ∈ Ideal.span {genπ c} ∨ Q := fun x y h => by
    simp only [Ideal.mem_span_singleton] at h ⊢; exact hπQ x y h
  -- `jou_dyn_l`, transported through `mk_mem_map`
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hK : ∀ w : MvPolynomial (Fin (r + 1 + 1)) (MvPolynomial (Fin (r + 1)) B),
      Ideal.Quotient.mk (Ideal.span {Jou.rel (genRow c)}) w ∈
        (Ideal.span {genπ c}).map (algebraMap _ (genJ c)) ↔
      w ∈ KJ (Ideal.span {genπ c}) (genRow c) := fun w => by
    rw [Jou.algebraMap_eq_mk_comp_C, ← Ideal.map_map, Ideal.mem_quotient_iff_mem_sup, KJ,
      Jou.rel_eq]
    rfl
  rw [← map_mul, hK] at huv
  rw [hK, hK]
  exact jou_dyn_l hdec hpr (genRow c) 1 hcl huv

/-- **Jouanolou rings over GCD domains have gcds, up to `Q`.** -/
theorem hasGcdQ_jou (hG : HasGcdQ Q B) (hz : ∀ b : B, b = 0 ∨ b ≠ 0) (hN : PolyIndNoeth B)
    (hc0 : c 0 ≠ 0) (hrel : ∀ e : B, (∀ i, e ∣ c i) → IsUnit e ∨ Q)
    (hzJ : ∀ z : Jou.J c, z = 0 ∨ z ≠ 0)
    (hdvd : ∀ z : genJ c, genπJ c ∣ z ∨ ¬ genπJ c ∣ z)
    (hdvdπ : ∀ x, genπ c ∣ x ∨ ¬ genπ c ∣ x) : HasGcdQ Q (Jou.J c) := by
  obtain ⟨hGB', hzB'⟩ := hasGcdQ_mvPolynomial hG hz (r + 1)
  have hπQ := prime_genericQ hG hz c hc0 hrel
  have hπ0 := genπ_ne_zero c hc0
  have : IsDomain (Jou.J c) := Jou.isDomain (l := 0) hc0
  have : IsDomain (genJ c) := Jou.isDomain (c := genRow c) (l := 0) hπ0
  have hπD := jouπ_primeQ c hπQ hdvdπ hc0
  have hne : genπJ c ≠ 0 := fun h => hπ0
    (Jou.algebraMap_injective (c := genRow c) (l := 0) hπ0 (by rw [map_zero]; exact h))
  -- `J_{B[λ]}(π, c)[1/π]` is a polynomial ring over `B[λ][1/π]`
  let L := Jou.LocP (genRow c) 0
  let _ : Algebra (genJ c) L := (Jou.elimLoc (genRow c) 0).toAlgebra
  have : IsLocalization.Away (genπJ c) L := Jou.isLocalization_elim (genRow c) 0
  have hS : Submonoid.powers (genπ c) ≤ nonZeroDivisors (MvPolynomial (Fin (r + 1)) B) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hπ0
  have : IsDomain (Localization.Away (genπ c)) := IsLocalization.isDomain_localization hS
  have hGL0 := hasGcdQ_of_isLocalization (Submonoid.powers (genπ c))
    (Localization.Away (genπ c)) hGB' hzB'
  have hzL0 := localization_eq_zero_or hzB' _ hS (Localization.Away (genπ c))
  have hGL : HasGcdQ Q L := (hasGcdQ_mvPolynomial hGL0 hzL0 (r + 1)).1
  have hzD : ∀ z : genJ c, z = 0 ∨ z ≠ 0 :=
    eq_zero_or_of_ringEquiv (genEquiv c).symm (mvPolynomial_eq_zero_or hzJ (r + 1 + 1))
  have hND : IndNoeth (genJ c) := IndNoeth.of_surjective (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective ((hN.mvPolynomial (r + 1)) (r + 1 + 1))
  have hval : ∀ a : genJ c, a ≠ 0 → ∃ n : ℕ, ∃ x, a = genπJ c ^ n * x ∧ ¬ genπJ c ∣ x :=
    fun a ha => match hND with
      | .step h => (h a).exists_val (jouπ_not_isUnit c hc0) hdvd a [] rfl ha
          (fun _ hx => absurd hx List.not_mem_nil)
  have hGD : HasGcdQ Q (genJ c) := hasGcd_of_away_dyn hne hπD L hzD hval hGL
  exact hasGcdQ_of_mvPolynomial hzJ (hasGcdQ_of_ringEquiv (genEquiv c) hGD)

end Main

end BezoutCounterexample.Constructive
