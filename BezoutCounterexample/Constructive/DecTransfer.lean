import BezoutCounterexample.Constructive.JouGCD
import BezoutCounterexample.Constructive.Groebner

/-!
# Transfer of zero tests and decidable divisibility

Constructive transfer of the decision procedures (`a = 0 ∨ a ≠ 0`, `DvdDec`) along the ring
constructions of the GCD form of HM's tower. The point is to replace the `Classical.em` decisions
of `torsorSGD` / `torsor_gcd` / `laurentSGD` by decisions computed from those of the base ring.

* `dvdDec_polynomial`, `dvdDec_mvPolynomial`: `A[X]`, `A[X₁, …, Xₙ]` (division by the leading
  coefficient, induction on the degree; no fraction field).
* `dvdDec_of_mvPolynomial`: descent from `A[X₁, …, Xₙ]` to `A`.
* `dvdDec_of_away`: from `A[1/p]` to `A`, given the decision of `p`-divisibility in `A`
  (`a ∣ b` iff `pⁿ ∣ q` where `a q = pⁿ b`).
* `dvdDec_away`, `dvdDec_away_mul`: from `A` to `A[1/p]` (`p` prime) and to `A[1/(p q)]`
  (`p`, `q` prime), using valuations (`hval`) and `dvd_of_dvd_pow_mul`.
* `zeroTest_jou`: the zero test of `J_B(c)` from that of `B` (embedding `elimLoc` into a polynomial
  ring over `B[1/c_l]`).
* `dvdDec_jou_prime`: `J_B(c)` with `c_l` prime, from `B` (`J[1/c_l]` is a polynomial ring over
  `B[1/c_l]`, and `J / c_l J = J_{B/c_l}(c̄)`).
* `dvdDec_genJ`, `dvdDec_jou`: `J_{B[λ]}(π, c)` (`π` the generic prime) and then any `J_B(c)` with
  `c₀ ≠ 0` and no common non-unit divisor, by descent along `genEquiv`.
-/

namespace BezoutCounterexample.Constructive

open Polynomial

section Poly

variable {A : Type*} [CommRing A] [IsDomain A]

/-- **Decidable divisibility in `A[X]`**: division by the leading coefficient. -/
theorem dvdDec_polynomial (hz : ∀ a : A, a = 0 ∨ a ≠ 0) (hd : DvdDec A) : DvdDec A[X] := by
  intro f g
  rcases polynomial_eq_zero_or hz f with rfl | hf
  · rcases polynomial_eq_zero_or hz g with rfl | hg
    · exact Or.inl dvd_rfl
    · exact Or.inr fun h => hg (zero_dvd_iff.1 h)
  suffices H : ∀ n, ∀ g : A[X], g.natDegree = n → f ∣ g ∨ ¬ f ∣ g from H _ g rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro g hgn
  rcases polynomial_eq_zero_or hz g with rfl | hg
  · exact Or.inl (dvd_zero f)
  by_cases hlt : g.natDegree < f.natDegree
  · exact Or.inr fun h => hlt.not_ge (natDegree_le_of_dvd h hg)
  push Not at hlt
  rcases hd f.leadingCoeff g.leadingCoeff with ⟨c, hc⟩ | hnd
  swap
  · refine Or.inr fun ⟨h, hh⟩ => hnd ⟨h.leadingCoeff, ?_⟩
    rw [hh, leadingCoeff_mul]
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [mul_zero] at hc; exact hg (leadingCoeff_eq_zero.1 hc)
  set m := g.natDegree - f.natDegree
  set q := C c * X ^ m * f
  have hq : q.natDegree = g.natDegree := by
    rw [natDegree_mul (by simpa using hc0) hf, natDegree_C_mul_X_pow m c hc0]; omega
  have hqlc : q.leadingCoeff = g.leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_C_mul_X_pow, hc, mul_comm]
  have hiff : f ∣ g ↔ f ∣ g - q := by
    have : f ∣ q := dvd_mul_left f _
    exact ⟨fun h => dvd_sub h this, fun h => by simpa using dvd_add h this⟩
  rw [hiff]
  rcases polynomial_eq_zero_or hz (g - q) with h0 | h0
  · rw [h0]; exact Or.inl (dvd_zero f)
  have hdeg : (g - q).degree < g.degree := by
    have hq0 : q ≠ 0 := fun h => by rw [h, leadingCoeff_zero] at hqlc; exact hg (leadingCoeff_eq_zero.1 hqlc.symm)
    exact degree_sub_lt (by rw [degree_eq_natDegree hg, degree_eq_natDegree hq0, hq]) hg hqlc.symm
  exact ih _ (hgn ▸ natDegree_lt_natDegree h0 hdeg) _ rfl

/-- **Decidable divisibility in `A[X₁, …, Xₙ]`.** -/
theorem dvdDec_mvPolynomial (hz : ∀ a : A, a = 0 ∨ a ≠ 0) (hd : DvdDec A) :
    ∀ n : ℕ, DvdDec (MvPolynomial (Fin n) A)
  | 0 => DvdDec.of_ringEquiv (MvPolynomial.isEmptyRingEquiv A (Fin 0)) hd
  | n + 1 => DvdDec.of_ringEquiv (MvPolynomial.finSuccEquiv A n).toRingEquiv
      (dvdDec_polynomial (mvPolynomial_eq_zero_or hz n) (dvdDec_mvPolynomial hz hd n))

omit [IsDomain A] in
/-- **Descent** of decidable divisibility from `A[X₁, …, Xₙ]` to `A`. -/
theorem dvdDec_of_mvPolynomial {n : ℕ} (h : DvdDec (MvPolynomial (Fin n) A)) : DvdDec A := by
  intro a b
  rcases h (MvPolynomial.C a) (MvPolynomial.C b) with h1 | h1
  · exact Or.inl (dvd_of_C_dvd_C h1)
  · exact Or.inr fun h2 => h1 (_root_.map_dvd MvPolynomial.C h2)

end Poly

section Away

variable {A : Type*} [CommRing A] [IsDomain A] {p : A} (L : Type*) [CommRing L] [Algebra A L]
  [IsLocalization.Away p L]

/-- Divisibility by the powers of `p`, from divisibility by `p`. -/
lemma pow_dvd_dec (hp0 : p ≠ 0) (hp : ∀ x : A, p ∣ x ∨ ¬ p ∣ x) :
    ∀ (n : ℕ) (x : A), p ^ n ∣ x ∨ ¬ p ^ n ∣ x
  | 0, x => Or.inl (by rw [pow_zero]; exact one_dvd x)
  | n + 1, x => by
    rcases hp x with ⟨y, rfl⟩ | hn
    · rcases pow_dvd_dec hp0 hp n y with ⟨z, rfl⟩ | hn'
      · exact Or.inl ⟨z, by ring⟩
      · refine Or.inr fun ⟨z, hz⟩ => hn' ⟨z, mul_left_cancel₀ hp0 ?_⟩
        rw [← mul_assoc, ← pow_succ', hz]
    · exact Or.inr fun h => hn ((dvd_pow_self p n.succ_ne_zero).trans h)

/-- **From `A[1/p]` to `A`**: `a ∣ b` is decided in `A[1/p]`, and then by `p`-divisibility. -/
theorem dvdDec_of_away (hp0 : p ≠ 0) (hz : ∀ a : A, a = 0 ∨ a ≠ 0)
    (hp : ∀ x : A, p ∣ x ∨ ¬ p ∣ x) (hL : DvdDec L) : DvdDec A := by
  intro a b
  rcases hz a with rfl | ha
  · rcases hz b with rfl | hb
    · exact Or.inl dvd_rfl
    · exact Or.inr fun h => hb (zero_dvd_iff.1 h)
  rcases hL (algebraMap A L a) (algebraMap A L b) with h | h
  swap
  · exact Or.inr fun h' => h (_root_.map_dvd _ h')
  obtain ⟨σ, ⟨n, rfl⟩, ⟨q, hq⟩⟩ := exists_dvd_of_dvd_localization (Submonoid.powers p) L h
  have hpn : p ^ n ≠ 0 := pow_ne_zero n hp0
  rcases pow_dvd_dec hp0 hp n q with ⟨t, rfl⟩ | hn
  · refine Or.inl ⟨t, mul_left_cancel₀ hpn ?_⟩
    simp only at hq; rw [hq]; ring
  · refine Or.inr fun ⟨t, ht⟩ => hn ⟨t, mul_left_cancel₀ ha ?_⟩
    simp only at hq; rw [← hq, ht]; ring

include L in
/-- **From `A` to `A[1/p]`**, `p` prime with valuations. -/
theorem dvdDec_away (hp : Prime p) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) (hd : DvdDec A)
    (hval : ∀ a : A, a ≠ 0 → ∃ n : ℕ, ∃ c : A, a = p ^ n * c ∧ ¬ p ∣ c) : DvdDec L := by
  intro x y
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers p) x
  obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers p) y
  have hu : ∀ k : ℕ, IsUnit (algebraMap A L (p ^ k)) := fun k =>
    IsLocalization.map_units L (⟨p ^ k, k, rfl⟩ : Submonoid.powers p)
  -- `mk' a s` and `algebraMap a` are associated
  have h1 : ∀ (a : A) (k : ℕ), IsLocalization.mk' L a (⟨p ^ k, k, rfl⟩ : Submonoid.powers p) ∣
      algebraMap A L a ∧ algebraMap A L a ∣
        IsLocalization.mk' L a (⟨p ^ k, k, rfl⟩ : Submonoid.powers p) := fun a k =>
    ⟨⟨algebraMap A L (p ^ k), (IsLocalization.mk'_spec L a _).symm⟩, by
      rw [← (hu k).dvd_mul_right, IsLocalization.mk'_spec]⟩
  suffices H : algebraMap A L a ∣ algebraMap A L b ∨ ¬ algebraMap A L a ∣ algebraMap A L b by
    rcases H with H | H
    · exact Or.inl ((h1 a m).1.trans (H.trans (h1 b n).2))
    · exact Or.inr fun h => H (((h1 a m).2.trans h).trans (h1 b n).1)
  rcases hz a with rfl | ha
  · rcases hz b with rfl | hb
    · exact Or.inl dvd_rfl
    · refine Or.inr fun h => hb ?_
      rw [map_zero, zero_dvd_iff] at h
      exact IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors hp.ne_zero)
        (h.trans (map_zero _).symm)
  obtain ⟨v, a', rfl, ha'⟩ := hval a ha
  have hiff : algebraMap A L (p ^ v * a') ∣ algebraMap A L b ↔ a' ∣ b := by
    rw [map_mul, (hu v).mul_left_dvd]
    constructor
    · intro h
      obtain ⟨σ, ⟨k, rfl⟩, hk⟩ := exists_dvd_of_dvd_localization (Submonoid.powers p) L h
      exact dvd_of_dvd_pow_mul hp ha' k hk
    · exact _root_.map_dvd _
  rw [hiff]
  exact hd a' b

/-- **From `A` to `A[1/(p q)]`**, `p`, `q` prime with valuations. -/
theorem dvdDec_away_mul {q : A} (hp : Prime p) (hq : Prime q) (hz : ∀ a : A, a = 0 ∨ a ≠ 0)
    (hd : DvdDec A) (hvp : ∀ a : A, a ≠ 0 → ∃ n : ℕ, ∃ c : A, a = p ^ n * c ∧ ¬ p ∣ c)
    (hvq : ∀ a : A, a ≠ 0 → ∃ n : ℕ, ∃ c : A, a = q ^ n * c ∧ ¬ q ∣ c)
    (L' : Type*) [CommRing L'] [Algebra A L'] [IsLocalization.Away (p * q) L'] : DvdDec L' := by
  intro x y
  obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p * q)) x
  obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p * q)) y
  have hu : ∀ k : ℕ, IsUnit (algebraMap A L' ((p * q) ^ k)) := fun k =>
    IsLocalization.map_units L' (⟨(p * q) ^ k, k, rfl⟩ : Submonoid.powers (p * q))
  have hup : IsUnit (algebraMap A L' p) := isUnit_of_mul_isUnit_left (by
    rw [← map_mul]; simpa using hu 1)
  have huq : IsUnit (algebraMap A L' q) := isUnit_of_mul_isUnit_right (by
    rw [← map_mul]; simpa using hu 1)
  have h1 : ∀ (a : A) (k : ℕ), IsLocalization.mk' L' a
      (⟨(p * q) ^ k, k, rfl⟩ : Submonoid.powers (p * q)) ∣ algebraMap A L' a ∧
      algebraMap A L' a ∣ IsLocalization.mk' L' a (⟨(p * q) ^ k, k, rfl⟩ : Submonoid.powers (p * q)) :=
    fun a k => ⟨⟨algebraMap A L' ((p * q) ^ k), (IsLocalization.mk'_spec L' a _).symm⟩, by
      rw [← (hu k).dvd_mul_right, IsLocalization.mk'_spec]⟩
  suffices H : algebraMap A L' a ∣ algebraMap A L' b ∨ ¬ algebraMap A L' a ∣ algebraMap A L' b by
    rcases H with H | H
    · exact Or.inl ((h1 a m).1.trans (H.trans (h1 b n).2))
    · exact Or.inr fun h => H (((h1 a m).2.trans h).trans (h1 b n).1)
  have hpq0 : p * q ≠ 0 := mul_ne_zero hp.ne_zero hq.ne_zero
  rcases hz a with rfl | ha
  · rcases hz b with rfl | hb
    · exact Or.inl dvd_rfl
    · refine Or.inr fun h => hb ?_
      rw [map_zero, zero_dvd_iff] at h
      exact IsLocalization.injective L' (powers_le_nonZeroDivisors_of_noZeroDivisors hpq0)
        (h.trans (map_zero _).symm)
  obtain ⟨v, a', rfl, ha'⟩ := hvp a ha
  have ha'0 : a' ≠ 0 := by rintro rfl; exact ha (by rw [mul_zero])
  obtain ⟨w, a'', rfl, ha''⟩ := hvq a' ha'0
  have hpa'' : ¬ p ∣ a'' := fun h => ha' (dvd_mul_of_dvd_right h _)
  have hiff : algebraMap A L' (p ^ v * (q ^ w * a'')) ∣ algebraMap A L' b ↔ a'' ∣ b := by
    rw [map_mul, map_mul, map_pow, map_pow, (hup.pow v).mul_left_dvd, (huq.pow w).mul_left_dvd]
    constructor
    · intro h
      obtain ⟨σ, ⟨k, rfl⟩, hk⟩ := exists_dvd_of_dvd_localization (Submonoid.powers (p * q)) L' h
      have h2 : a'' ∣ p ^ k * (q ^ k * b) := by simp only at hk; rwa [mul_pow, mul_assoc] at hk
      exact dvd_of_dvd_pow_mul hq ha'' k (dvd_of_dvd_pow_mul hp hpa'' k h2)
    · exact _root_.map_dvd _
  rw [hiff]
  exact hd a'' b

end Away

section Jouanolou

variable {B : Type*} [CommRing B] [IsDomain B] {r : ℕ}

/-- **Zero test of `J_B(c)`**, through `elimLoc : J_B(c) → B[1/c_l][σ_{≠l}]`. -/
theorem zeroTest_jou (hz : ∀ b : B, b = 0 ∨ b ≠ 0) {c : Fin (r + 1) → B} {l : Fin (r + 1)}
    (hl : c l ≠ 0) : ∀ z : Jou.J c, z = 0 ∨ z ≠ 0 := by
  have hzL : ∀ x : Localization.Away (c l), x = 0 ∨ x ≠ 0 :=
    localization_eq_zero_or hz _ (powers_le_nonZeroDivisors_of_noZeroDivisors hl) _
  have : IsDomain (Jou.J c) := Jou.isDomain hl
  intro z
  rcases mvPolynomial_eq_zero_or hzL r (Jou.elimLoc c l z) with h | h
  · obtain ⟨n, hn⟩ := Jou.exists_pow_mul_eq_zero_of_elimLoc h
    have hc : algebraMap B (Jou.J c) (c l) ≠ 0 := fun h0 =>
      hl (Jou.algebraMap_injective hl (h0.trans (map_zero _).symm))
    exact Or.inl ((mul_eq_zero.1 hn).resolve_left (pow_ne_zero n hc))
  · exact Or.inr fun h0 => h (by rw [h0, map_zero])

/-- **Decidable divisibility in `J_B(c)` when `c_l` is prime**: `J[1/c_l]` is a polynomial ring
over `B[1/c_l]`, and `c_l`-divisibility is the zero test of `J_{B/c_l}(c̄)`. -/
theorem dvdDec_jou_prime (hz : ∀ b : B, b = 0 ∨ b ≠ 0) (hd : DvdDec B) (hN : IndNoeth B)
    {c : Fin (r + 1) → B} {l : Fin (r + 1)} (hl : Prime (c l)) {m : Fin (r + 1)}
    (hm : ¬ c l ∣ c m) : DvdDec (Jou.J c) := by
  have : IsDomain (Jou.J c) := Jou.isDomain hl.ne_zero
  let : Algebra (Jou.J c) (Jou.LocP c l) := (Jou.elimLoc c l).toAlgebra
  have := Jou.isLocalization_elim c l
  have hzL : ∀ x : Localization.Away (c l), x = 0 ∨ x ≠ 0 :=
    localization_eq_zero_or hz _ (powers_le_nonZeroDivisors_of_noZeroDivisors hl.ne_zero) _
  have hdL : DvdDec (Localization.Away (c l)) :=
    dvdDec_away (Localization.Away (c l)) hl hz hd fun a ha => hN.exists_val hl.not_unit hd ha
  have : IsDomain (Localization.Away (c l)) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors hl.ne_zero)
  have hdP : DvdDec (Jou.LocP c l) := dvdDec_mvPolynomial hzL hdL r
  -- `c_l`-divisibility in `J`
  have hQ : IsDomain (B ⧸ Ideal.span {c l}) :=
    (Ideal.Quotient.isDomain_iff_prime _).2 ((Ideal.span_singleton_prime hl.ne_zero).2 hl)
  have hzQ : ∀ y : B ⧸ Ideal.span {c l}, y = 0 ∨ y ≠ 0 := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hd (c l) b
  have hmQ : (Ideal.Quotient.mk (Ideal.span {c l}) ∘ c) m ≠ 0 := by
    rw [Function.comp_apply, Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hm
  have hp : ∀ z : Jou.J c, algebraMap B (Jou.J c) (c l) ∣ z ∨ ¬ algebraMap B (Jou.J c) (c l) ∣ z := by
    intro z
    have hiff : algebraMap B (Jou.J c) (c l) ∣ z ↔ Jou.redHom c (c l) z = 0 := by
      rw [← RingHom.mem_ker, Jou.ker_redHom, Ideal.mem_span_singleton]
    rw [hiff]
    exact zeroTest_jou hzQ hmQ _
  have hp0 : algebraMap B (Jou.J c) (c l) ≠ 0 := fun h0 =>
    hl.ne_zero (Jou.algebraMap_injective hl.ne_zero (h0.trans (map_zero _).symm))
  exact dvdDec_of_away (Jou.LocP c l) hp0 (zeroTest_jou hz hl.ne_zero) hp hdP

variable (c : Fin (r + 1) → B)

/-- **Decidable divisibility in `J_{B[λ]}(π, c)`**: `π` is prime (`prime_generic`). -/
theorem dvdDec_genJ (hG : HasGcd B) (hz : ∀ b : B, b = 0 ∨ b ≠ 0) (hd : DvdDec B)
    (hN : PolyIndNoeth B) (hc0 : c 0 ≠ 0) (hrel : ∀ e : B, (∀ i, e ∣ c i) → IsUnit e) :
    DvdDec (genJ c) :=
  dvdDec_jou_prime (mvPolynomial_eq_zero_or hz (r + 1)) (dvdDec_mvPolynomial hz hd (r + 1))
    (hN (r + 1)) (l := 0) (m := 1) (prime_generic hG hz c hc0 hrel) (not_dvd_genπ c hc0 hc0)

/-- **Decidable divisibility in `J_B(c)`** for any row with `c₀ ≠ 0` and no common non-unit
divisor: descent from `J_B(c)[σ', λ] ≅ J_{B[λ]}(π, c)`. -/
theorem dvdDec_jou (hG : HasGcd B) (hz : ∀ b : B, b = 0 ∨ b ≠ 0) (hd : DvdDec B)
    (hN : PolyIndNoeth B) (hc0 : c 0 ≠ 0) (hrel : ∀ e : B, (∀ i, e ∣ c i) → IsUnit e) :
    DvdDec (Jou.J c) :=
  dvdDec_of_mvPolynomial (DvdDec.of_ringEquiv (genEquiv c) (dvdDec_genJ c hG hz hd hN hc0 hrel))

/-- **`hasGcd_jou` with all decisions computed**: gcds, zero test and decidable divisibility of
`J_B(c)` from those of `B`. -/
theorem jou_dec (hG : HasGcd B) (hz : ∀ b : B, b = 0 ∨ b ≠ 0) (hd : DvdDec B)
    (hN : PolyIndNoeth B) (hc0 : c 0 ≠ 0) (hrel : ∀ e : B, (∀ i, e ∣ c i) → IsUnit e) :
    HasGcd (Jou.J c) ∧ (∀ z : Jou.J c, z = 0 ∨ z ≠ 0) ∧ DvdDec (Jou.J c) :=
  ⟨hasGcd_jou c hG hz hN hc0 hrel (zeroTest_jou hz hc0)
    (fun z => dvdDec_genJ c hG hz hd hN hc0 hrel (genπJ c) z),
   zeroTest_jou hz hc0, dvdDec_jou c hG hz hd hN hc0 hrel⟩

end Jouanolou

end BezoutCounterexample.Constructive
