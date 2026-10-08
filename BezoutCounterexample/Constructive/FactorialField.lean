import BezoutCounterexample.Constructive.Kronecker
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Factorial fields and the transfer `K ↝ K(t)` (option 2, M2a; MRR VII.3)

* `FactorSearch R`: in `R[X]`, for `f ≠ 0` and a degree bound `d`, either a factor `g` with
  `0 < deg g ≤ d` is found, or every divisor of degree `≤ d` is constant.
* `FactorialField K`: a zero test and `FactorSearch K`. `factorialField_rat` (M1).
  Generic consequences: `FactorialField.irreducible_or_split`, `.exists_factorisation`, `.dvdDec`.
* `exists_sublist_associated`: a divisor of a product of irreducibles of `K[X]` is associated to a
  subproduct (decidable divisibility + Bézout).
* `factorSearch_fraction` (Gauss): `FactorSearch A → FactorSearch (Frac A)` for a GCD domain `A` with
  a zero test (uses the propositional `exists_clear`, `exists_primPart`, `dvd_of_map_dvd`).
* Kronecker substitution `ksub N : K[t][X] → K[t]`, `X ↦ t^N`, with the additive inverse `kinv N`
  (`t^m ↦ t^(m mod N) X^(m div N)`), `kinv_ksub` on polynomials whose coefficients have
  `t`-degree `< N`; the `t`-degree is the degree of `Bivariate.swap`.
* `kron_search`: `FactorialField K → FactorSearch K[t]`: with `N > deg_t f`, a factor `g` of `f`
  gives `ksub g ∣ ksub f`, hence `ksub g` associated to a subproduct of a factorisation of
  `ksub f`; the unit is a constant, so `kinv` of that subproduct is `g` times a constant.
  Candidates are tested by exact division in `K[t][X]`.
* `factorialField_fraction`: `FactorialField K → FactorialField L` for any fraction field `L` of
  `K[t]`.
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open Polynomial

/-- Factor search with a degree bound in `R[X]`. -/
def FactorSearch (R : Type*) [CommRing R] : Prop :=
  ∀ f : R[X], f ≠ 0 → ∀ d : ℕ, (∃ g : R[X], 0 < g.natDegree ∧ g.natDegree ≤ d ∧ g ∣ f) ∨
    ∀ g : R[X], g ∣ f → g.natDegree ≤ d → g.natDegree = 0

/-- A **factorial field**: a discrete field with factor search in `K[X]`. -/
structure FactorialField (K : Type*) [Field K] : Prop where
  zero : ∀ x : K, x = 0 ∨ x ≠ 0
  search : FactorSearch K

theorem factorialField_rat : FactorialField ℚ :=
  ⟨fun a => deq a 0, fun _ hf d => factor_search hf d⟩

section Field

variable {K : Type*} [Field K]

lemma dvdDec_of_field (hz : ∀ x : K, x = 0 ∨ x ≠ 0) : DvdDec K := by
  intro a b
  rcases hz a with rfl | ha
  · rcases hz b with rfl | hb
    · exact Or.inl dvd_rfl
    · exact Or.inr fun h => hb (zero_dvd_iff.1 h)
  · exact Or.inl ⟨a⁻¹ * b, by rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]⟩

lemma isUnit_of_natDegree_eq_zero_field {g : K[X]} (hg : g ≠ 0) (h : g.natDegree = 0) :
    IsUnit g := by
  rw [eq_C_of_natDegree_eq_zero h] at hg ⊢
  exact (IsUnit.mk0 _ fun h0 => hg (by rw [h0, C_0])).map C

namespace FactorialField

variable (hK : FactorialField K)
include hK

lemma dvdDec : DvdDec K[X] := dvdDec_polynomial hK.zero (dvdDec_of_field hK.zero)

/-- Decidable irreducibility in `K[X]`. -/
theorem irreducible_or_split {f : K[X]} (hf : 0 < f.natDegree) :
    Irreducible f ∨ ∃ g h : K[X], f = g * h ∧ 0 < g.natDegree ∧ 0 < h.natDegree := by
  have hf0 : f ≠ 0 := fun h => by rw [h, natDegree_zero] at hf; exact lt_irrefl 0 hf
  rcases hK.search f hf0 (f.natDegree - 1) with ⟨g, h1, h2, ⟨h, hh⟩⟩ | hn
  · have hg0 : g ≠ 0 := fun h => by rw [h, natDegree_zero] at h1; exact lt_irrefl 0 h1
    have hh0 : h ≠ 0 := fun h' => hf0 (by rw [hh, h', mul_zero])
    have := natDegree_mul hg0 hh0
    rw [← hh] at this
    exact Or.inr ⟨g, h, hh, h1, by omega⟩
  refine Or.inl ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu; omega
  have ha0 : a ≠ 0 := fun h => hf0 (by rw [hab, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hf0 (by rw [hab, h, mul_zero])
  have hdeg := natDegree_mul ha0 hb0
  rw [← hab] at hdeg
  rcases Decidable.em (a.natDegree ≤ f.natDegree - 1) with hle | hle
  · exact Or.inl (isUnit_of_natDegree_eq_zero_field ha0 (hn a ⟨b, hab⟩ hle))
  · exact Or.inr (isUnit_of_natDegree_eq_zero_field hb0 (by omega))

/-- Factorisation in `K[X]`: a unit times a product of irreducibles. -/
theorem exists_factorisation {f : K[X]} (hf : f ≠ 0) :
    ∃ (u : K[X]) (l : List K[X]), IsUnit u ∧ (∀ p ∈ l, Irreducible p) ∧ f = u * l.prod := by
  suffices H : ∀ n, ∀ f : K[X], f ≠ 0 → f.natDegree = n →
      ∃ (u : K[X]) (l : List K[X]), IsUnit u ∧ (∀ p ∈ l, Irreducible p) ∧ f = u * l.prod from
    H _ f hf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf hn
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · exact ⟨f, [], isUnit_of_natDegree_eq_zero_field hf h0, by simp, by simp⟩
  rcases hK.irreducible_or_split hpos with hirr | ⟨g, h, hgh, hg, hh⟩
  · exact ⟨1, [f], isUnit_one, by simpa using hirr, by simp⟩
  have hg0 : g ≠ 0 := fun h' => hf (by rw [hgh, h', zero_mul])
  have hh0 : h ≠ 0 := fun h' => hf (by rw [hgh, h', mul_zero])
  have hdeg := natDegree_mul hg0 hh0
  rw [← hgh] at hdeg
  obtain ⟨u, l, hu, hl, rfl⟩ := ih g.natDegree (by omega) g hg0 rfl
  obtain ⟨v, m, hv, hm, rfl⟩ := ih h.natDegree (by omega) h hh0 rfl
  refine ⟨u * v, l ++ m, hu.mul hv, fun p hp => ?_, ?_⟩
  · rcases List.mem_append.1 hp with hp | hp
    · exact hl p hp
    · exact hm p hp
  · rw [hgh, List.prod_append]; ring

/-- A divisor of a product of irreducibles is associated to a subproduct. -/
theorem exists_sublist_associated :
    ∀ (l : List K[X]), (∀ p ∈ l, Irreducible p) → ∀ a : K[X], a ∣ l.prod →
      ∃ J ∈ l.sublists, Associated a J.prod := by
  intro l
  induction l with
  | nil =>
    intro _ a ha
    exact ⟨[], by simp, by simpa [associated_one_iff_isUnit] using isUnit_of_dvd_one ha⟩
  | cons p l ih =>
    intro hl a ha
    have hp : Irreducible p := hl p (List.mem_cons_self ..)
    have hl' : ∀ q ∈ l, Irreducible q := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rw [List.prod_cons] at ha
    rcases hK.dvdDec p a with ⟨a', rfl⟩ | hpa
    · have : a' ∣ l.prod := (mul_dvd_mul_iff_left hp.ne_zero).1 ha
      obtain ⟨J, hJ, hJa⟩ := ih hl' a' this
      refine ⟨p :: J, List.mem_sublists.2 ((List.mem_sublists.1 hJ).cons_cons p), ?_⟩
      rw [List.prod_cons]
      exact hJa.mul_left p
    · have hc : IsCoprime p a := (hp.coprime_iff_not_dvd).2 hpa
      have : a ∣ l.prod := hc.symm.dvd_of_dvd_mul_left ha
      obtain ⟨J, hJ, hJa⟩ := ih hl' a this
      exact ⟨J, List.mem_sublists.2 ((List.mem_sublists.1 hJ).cons p), hJa⟩

end FactorialField

end Field

section Gauss

variable {A : Type*} [CommRing A] [IsDomain A] (L : Type*) [Field L] [Algebra A L]
  [IsFractionRing A L]

/-- **Gauss**: factor search passes from `A[X]` to `Frac(A)[X]`. -/
theorem factorSearch_fraction (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0)
    (hS : FactorSearch A) : FactorSearch L := by
  have hinj := IsFractionRing.injective A L
  have hunit : ∀ {s : A}, s ≠ 0 → IsUnit (C (algebraMap A L s)) := fun hs =>
    (IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).2 hs)).map C
  intro f hf d
  obtain ⟨s, hs, F, hF⟩ := exists_clear (A := A) L f
  have hF0 : F ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hF
    exact hf (((hunit hs).mul_right_eq_zero).1 hF.symm)
  have hdvd : ∀ {g : L[X]}, g ∣ F.map (algebraMap A L) ↔ g ∣ f := by
    intro g; rw [hF]; exact (hunit hs).dvd_mul_left
  rcases hS F hF0 d with ⟨G, h1, h2, h3⟩ | hn
  · refine Or.inl ⟨G.map (algebraMap A L), ?_, ?_, hdvd.1 (Polynomial.map_dvd _ h3)⟩ <;>
      rwa [natDegree_map_eq_of_injective hinj]
  refine Or.inr fun g hg hgd => ?_
  have hg0 : g ≠ 0 := fun h => hf (zero_dvd_iff.1 (h ▸ hg))
  obtain ⟨s', hs', g₁, hg₁⟩ := exists_clear (A := A) L g
  have hg₁0 : g₁ ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hg₁
    exact hg0 (((hunit hs').mul_right_eq_zero).1 hg₁.symm)
  obtain ⟨c, g₀, rfl, hc, hprim⟩ := exists_primPart hG hg₁0
  have hdeg₁ : (C c * g₀).natDegree = g.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj, hg₁, natDegree_C_mul
      ((map_ne_zero_iff _ hinj).2 hs')]
  have hdeg₀ : g₀.natDegree = g.natDegree := by
    rw [← hdeg₁, natDegree_C_mul hc]
  have hmap : g₀.map (algebraMap A L) ∣ F.map (algebraMap A L) := by
    refine (Polynomial.map_dvd _ (dvd_mul_left g₀ (C c))).trans ?_
    rw [hg₁]
    exact ((hunit hs').mul_left_dvd).2 (hdvd.2 hg)
  have := hn g₀ (dvd_of_map_dvd L hG hz hprim hmap) (hdeg₀ ▸ hgd)
  omega

end Gauss

section Subst

variable {K : Type*} [Field K]

/-- Kronecker substitution `X ↦ t^N`. -/
def ksub (N : ℕ) (g : K[X][X]) : K[X] := g.eval ((X : K[X]) ^ N)

/-- Its inverse on bounded polynomials: `t^m ↦ t^(m mod N) X^(m div N)`. -/
def kinv (N : ℕ) : K[X] →+ K[X][X] where
  toFun p := p.sum fun m a => monomial (m / N) (monomial (m % N) a)
  map_zero' := sum_zero_index _
  map_add' p q := sum_add_index p q _ (fun _ => by simp) fun _ _ _ => by
    rw [map_add, map_add]

lemma kinv_monomial (N m : ℕ) (a : K) :
    kinv N (monomial m a) = monomial (m / N) (monomial (m % N) a) :=
  sum_monomial_index (n := m) a (fun m a => monomial (m / N) (monomial (m % N) a)) (by simp)

lemma ksub_mul (N : ℕ) (a b : K[X][X]) : ksub N (a * b) = ksub N a * ksub N b := eval_mul

lemma ksub_C (N : ℕ) (a : K[X]) : ksub N (C a) = a := eval_C

lemma kinv_ksub {N : ℕ} (hN : 0 < N) (g : K[X][X]) (hg : ∀ j, (g.coeff j).natDegree < N) :
    kinv N (ksub N g) = g := by
  have key : ∀ j, kinv N (g.coeff j * ((X : K[X]) ^ N) ^ j) = monomial j (g.coeff j) := by
    intro j
    conv_lhs => rw [(g.coeff j).as_sum_support]
    conv_rhs => rw [(g.coeff j).as_sum_support, map_sum]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N := lt_of_le_of_lt (le_natDegree_of_mem_supp i hi) (hg j)
    rw [← pow_mul, monomial_mul_X_pow, kinv_monomial, Nat.add_mul_div_left _ _ hN,
      Nat.div_eq_of_lt hi', zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi']
  rw [ksub, eval_eq_sum, Polynomial.sum, map_sum]
  simp_rw [key]
  exact g.as_sum_support.symm

open Polynomial.Bivariate in
lemma coeff_coeff_swap (p : K[X][X]) (i j : ℕ) :
    ((swap p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, coeff_add, ha, hb]
    | monomial m r =>
      rw [swap_monomial_monomial]
      simp only [coeff_monomial]
      by_cases h1 : m = i <;> by_cases h2 : n = j <;> simp [h1, h2, coeff_monomial]

open Polynomial.Bivariate in
lemma natDegree_coeff_le_swap (p : K[X][X]) (j : ℕ) :
    (p.coeff j).natDegree ≤ (swap p).natDegree :=
  natDegree_le_iff_coeff_eq_zero.2 fun i hi => by
    rw [← coeff_coeff_swap, coeff_eq_zero_of_natDegree_lt hi, coeff_zero]

open Polynomial.Bivariate in
/-- **Kronecker substitution**: factor search in `K[t][X]` from factorisation in `K[t]`. -/
theorem kron_search (hK : FactorialField K) : FactorSearch K[X] := by
  -- the projection instance (otherwise inference goes through `Field.henselian`)
  letI : Nontrivial K := DivisionRing.toNontrivial
  intro f hf d
  set N := (swap f).natDegree + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos _
  have hsw0 : swap f ≠ 0 := fun h => hf (by rw [← swap_swap_apply f, h, map_zero])
  have hb : ∀ g : K[X][X], g ∣ f → ∀ j, (g.coeff j).natDegree < N := by
    intro g hg j
    have := natDegree_le_of_dvd (map_dvd swap hg) hsw0
    have := natDegree_coeff_le_swap g j
    omega
  have hq : ksub N f ≠ 0 := fun h => hf (by
    rw [← kinv_ksub hN f (hb f dvd_rfl), h, map_zero])
  obtain ⟨u, l, hu, hl, hql⟩ := hK.exists_factorisation hq
  let P : List K[X] → Prop := fun J =>
    0 < (kinv N J.prod).natDegree ∧ (kinv N J.prod).natDegree ≤ d ∧ kinv N J.prod ∣ f
  have hdec : DvdDec K[X][X] := dvdDec_polynomial (polynomial_eq_zero_or hK.zero) hK.dvdDec
  have hP : ∀ J, P J ∨ ¬ P J := by
    intro J
    rcases Decidable.em (0 < (kinv N J.prod).natDegree) with h1 | h1
    · rcases Decidable.em ((kinv N J.prod).natDegree ≤ d) with h2 | h2
      · rcases hdec (kinv N J.prod) f with h3 | h3
        · exact Or.inl ⟨h1, h2, h3⟩
        · exact Or.inr fun h => h3 h.2.2
      · exact Or.inr fun h => h2 h.2.1
    · exact Or.inr fun h => h1 h.1
  rcases Multiset.exists_or_forall_not' (l.sublists : Multiset (List K[X])) hP with
    ⟨J, -, hJ⟩ | hn
  · exact Or.inl ⟨_, hJ⟩
  refine Or.inr fun g hg hgd => ?_
  rcases Nat.eq_zero_or_pos g.natDegree with h0 | hpos
  · exact h0
  exfalso
  have hsg : ksub N g ∣ l.prod := by
    have : ksub N g ∣ ksub N f := eval_dvd hg
    rw [hql] at this
    exact hu.dvd_mul_left.1 this
  obtain ⟨J, hJ, v, hv⟩ := hK.exists_sublist_associated l hl _ hsg
  obtain ⟨c, hc, hcv⟩ := Polynomial.isUnit_iff.1 v.isUnit
  have hc0 : c ≠ 0 := hc.ne_zero
  set g' := g * C (C c) with hg'
  have hCC : (C c : K[X]) ≠ 0 := by simpa using hc0
  have hks : ksub N g' = J.prod := by
    rw [hg', ksub_mul, ksub_C, hcv, hv]
  have hb' : ∀ j, (g'.coeff j).natDegree < N := by
    intro j
    rw [hg', coeff_mul_C, natDegree_mul_C hc0]
    exact hb g hg j
  have hinv : kinv N J.prod = g' := by rw [← hks, kinv_ksub hN g' hb']
  have hdeg : g'.natDegree = g.natDegree := natDegree_mul_C hCC
  refine hn J (Multiset.mem_coe.2 hJ) ⟨?_, ?_, ?_⟩
  · rw [hinv, hdeg]; exact hpos
  · rw [hinv, hdeg]; exact hgd
  · rw [hinv, hg']
    exact ((isUnit_C.2 (isUnit_C.2 (IsUnit.mk0 c hc0))).mul_right_dvd).2 hg

/-- **`K ↝ K(t)`**: a fraction field of `K[t]` is factorial when `K` is. -/
theorem factorialField_fraction (hK : FactorialField K) (L : Type*) [Field L] [Algebra K[X] L]
    [IsFractionRing K[X] L] : FactorialField L :=
  ⟨hzero_fraction L (polynomial_eq_zero_or hK.zero),
    factorSearch_fraction L (fun a b => exists_isGcd_polynomial_field K hK.zero a b)
      (polynomial_eq_zero_or hK.zero) (kron_search hK)⟩

end Subst

end BezoutCounterexample.Constructive
