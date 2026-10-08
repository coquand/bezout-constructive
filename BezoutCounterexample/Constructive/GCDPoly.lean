import BezoutCounterexample.Constructive.NagataGCD

/-!
# GCD domains: basic facts, Gauss's lemma, polynomial rings (`~/COLL/bezout-gcd.tex`, Lemma 2.1)

Everything is propositional (`HasGcd`, decidable zero test as `∀ a, a = 0 ∨ a ≠ 0`); no
normalisation of associates.

* `isGcd_mul_left`: `gcd(ca, cb) = c gcd(a, b)`.
* `dvd_of_isRelPrime_of_dvd_mul`: `gcd(a, b) = 1`, `a ∣ bc` ⇒ `a ∣ c`.
* `gauss`: if `t` is coprime to the coefficients of `f` and `t ∣ f k` (coefficientwise), then
  `t ∣ k`. Induction on `deg f + deg k`, peeling leading terms; no contents and no primitive
  parts are needed (compare Mathlib's `associated_content_mul`, which needs a
  `NormalizedGCDMonoid`).
* `hasGcd_polynomial`: `A[X]` has gcds, via Euclid in `Frac(A)[X]` (the one `@[cprim]`,
  `exists_isGcd_polynomial_field`: Euclid's algorithm over a field with decidable equality),
  clearing denominators and `gauss`.
* `hasGcd_of_isLocalization`, `hasGcd_of_ringEquiv`, `hasGcd_mvPolynomial`.
-/

namespace BezoutCounterexample.Constructive

open Polynomial

section Basic

variable {A : Type*} [CommRing A] [IsDomain A]

/-- `gcd(ca, cb) = c · gcd(a, b)`. -/
lemma isGcd_mul_left (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) {g a b : A}
    (hg : IsGcd g a b) (c : A) : IsGcd (c * g) (c * a) (c * b) := by
  obtain ⟨h, hha, hhb, hhc⟩ := hG (c * a) (c * b)
  have hgh : c * g ∣ h := hhc _ (mul_dvd_mul_left c hg.1) (mul_dvd_mul_left c hg.2.1)
  have hhg : h ∣ c * g := by
    rcases hz c with rfl | hc
    · rw [zero_mul]; exact dvd_zero h
    obtain ⟨h', rfl⟩ := hhc c (dvd_mul_right c a) (dvd_mul_right c b)
    exact mul_dvd_mul_left c (hg.2.2 h' ((mul_dvd_mul_iff_left hc).1 hha)
      ((mul_dvd_mul_iff_left hc).1 hhb))
  exact ⟨mul_dvd_mul_left c hg.1, mul_dvd_mul_left c hg.2.1,
    fun d hda hdb => (hhc d hda hdb).trans hhg⟩

/-- Coprime cancellation. -/
lemma dvd_of_isRelPrime_of_dvd_mul (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) {a b c : A}
    (h : IsRelPrime a b) (hd : a ∣ b * c) : a ∣ c := by
  obtain ⟨g, hg⟩ := hG a b
  have hu : IsUnit g := h hg.1 hg.2.1
  have hcg := isGcd_mul_left hG hz hg c
  have : a ∣ c * g := hcg.2.2 a (dvd_mul_left a c) (by rw [mul_comm]; exact hd)
  exact hu.dvd_mul_right.1 this

/-- Dividing by a nonzero gcd leaves a coprime pair. -/
lemma isRelPrime_of_isGcd {g a b a' b' : A} (hg : IsGcd g a b) (hg0 : g ≠ 0) (ha : a = g * a')
    (hb : b = g * b') : IsRelPrime a' b' := by
  intro d hda hdb
  have h1 : g * d ∣ g * 1 := by
    rw [mul_one]
    exact hg.2.2 _ (ha ▸ mul_dvd_mul_left g hda) (hb ▸ mul_dvd_mul_left g hdb)
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_left hg0).1 h1)

omit [IsDomain A] in
/-- Transport of gcds along a ring isomorphism. -/
lemma hasGcd_of_ringEquiv {B : Type*} [CommRing B] (e : A ≃+* B) (hB : HasGcd B) : HasGcd A := by
  intro a b
  obtain ⟨g, hga, hgb, hgc⟩ := hB (e a) (e b)
  have hdvd : ∀ {x y : B}, x ∣ y → e.symm x ∣ e.symm y := fun h => map_dvd e.symm h
  refine ⟨e.symm g, by simpa using hdvd hga, by simpa using hdvd hgb, fun c hca hcb => ?_⟩
  have := hdvd (hgc (e c) (map_dvd e hca) (map_dvd e hcb))
  simpa using this

end Basic

section Localization

variable {A : Type*} [CommRing A] [IsDomain A] (S : Submonoid A) (L : Type*) [CommRing L]
  [Algebra A L] [IsLocalization S L]

omit [IsDomain A] in
/-- If `algebraMap c ∣ algebraMap a` in `A_S`, then `c ∣ σ a` for some `σ ∈ S`. -/
lemma exists_dvd_of_dvd_localization {c a : A} (h : algebraMap A L c ∣ algebraMap A L a) :
    ∃ σ ∈ S, c ∣ σ * a := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨⟨e, v⟩, rfl⟩ := IsLocalization.mk'_surjective S w
  have h1 : algebraMap A L (a * v) = algebraMap A L (c * e) := by
    rw [map_mul, hw, map_mul, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨r, hr⟩ := (IsLocalization.eq_iff_exists S L).1 h1
  refine ⟨r * v, S.mul_mem r.2 v.2, ⟨r * e, ?_⟩⟩
  linear_combination hr

include S in
/-- **Localisations of GCD domains** have gcds, computed in `A`. -/
theorem hasGcd_of_isLocalization (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) :
    HasGcd L := by
  intro x y
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective S y
  obtain ⟨g, hg⟩ := hG a b
  have hus : IsUnit (algebraMap A L s) := IsLocalization.map_units L s
  have hut : IsUnit (algebraMap A L t) := IsLocalization.map_units L t
  -- `mk' a s` and `algebraMap a` divide each other
  have h1 : ∀ (a : A) (s : S), IsLocalization.mk' L a s ∣ algebraMap A L a := fun a s =>
    ⟨algebraMap A L s, (IsLocalization.mk'_spec L a s).symm⟩
  have h2 : ∀ (a : A) (s : S), algebraMap A L a ∣ IsLocalization.mk' L a s := fun a s => by
    rw [← (IsLocalization.map_units L s).dvd_mul_right, IsLocalization.mk'_spec]
  refine ⟨algebraMap A L g, (_root_.map_dvd _ hg.1).trans (h2 a s),
    (_root_.map_dvd _ hg.2.1).trans (h2 b t),
    fun z hza hzb => ?_⟩
  obtain ⟨⟨c, u⟩, rfl⟩ := IsLocalization.mk'_surjective S z
  have hc : ∀ {a : A} (s : S), IsLocalization.mk' L c u ∣ IsLocalization.mk' L a s →
      algebraMap A L c ∣ algebraMap A L a := fun s h => by
    rw [← IsLocalization.mk'_spec L c u, (IsLocalization.map_units L u).mul_right_dvd]
    exact h.trans (h1 _ s)
  obtain ⟨σ, hσ, hσa⟩ := exists_dvd_of_dvd_localization S L (hc s hza)
  obtain ⟨τ, hτ, hτb⟩ := exists_dvd_of_dvd_localization S L (hc t hzb)
  have hcg : c ∣ (σ * τ) * g :=
    (isGcd_mul_left hG hz hg (σ * τ)).2.2 c
      (by rw [mul_comm σ, mul_assoc]; exact dvd_mul_of_dvd_right hσa τ)
      (by rw [mul_assoc]; exact dvd_mul_of_dvd_right hτb σ)
  have hst : IsUnit (algebraMap A L (σ * τ)) :=
    IsLocalization.map_units L (⟨σ * τ, S.mul_mem hσ hτ⟩ : S)
  have : algebraMap A L c ∣ algebraMap A L g := by
    rw [← hst.dvd_mul_left, ← map_mul]; exact _root_.map_dvd _ hcg
  exact (h1 c u).trans this

end Localization

section Gauss

variable {A : Type*} [CommRing A] [IsDomain A]

/-- **Gauss's lemma** (content-free form): if `t` is coprime to the coefficients of `f` and
`C t ∣ f k`, then `C t ∣ k`. -/
theorem gauss (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) :
    ∀ (N : ℕ) (f k : A[X]), f.natDegree + k.natDegree ≤ N → ∀ t : A,
      (∀ d, d ∣ t → C d ∣ f → IsUnit d) → C t ∣ f * k → C t ∣ k := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro f k hN t hcop hdiv
  obtain ⟨u, hut, huk, hu⟩ := hG t k.leadingCoeff
  -- Step 1: `C u ∣ k`.
  have h1 : C u ∣ k := by
    rcases Nat.eq_zero_or_pos k.natDegree with hk0 | hk0
    · rw [eq_C_of_natDegree_eq_zero hk0]
      have : k.leadingCoeff = k.coeff 0 := by rw [leadingCoeff, hk0]
      exact map_dvd C (this ▸ huk)
    · have hlt : k.eraseLead.natDegree < k.natDegree :=
        lt_of_le_of_lt (eraseLead_natDegree_le k) (Nat.sub_lt hk0 one_pos)
      have hsplit := eraseLead_add_C_mul_X_pow k
      have hd : C u ∣ f * k.eraseLead := by
        have h2 : C u ∣ f * (C k.leadingCoeff * X ^ k.natDegree) :=
          dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (map_dvd C huk) _) f
        have h3 : f * k.eraseLead = f * k - f * (C k.leadingCoeff * X ^ k.natDegree) := by
          rw [eq_sub_iff_add_eq, ← mul_add, hsplit]
        rw [h3]
        exact dvd_sub (dvd_trans (map_dvd C hut) hdiv) h2
      have := ih (f.natDegree + k.eraseLead.natDegree) (by omega) f k.eraseLead le_rfl u
        (fun d hd hdf => hcop d (hd.trans hut) hdf) hd
      rw [← hsplit]
      exact dvd_add this (dvd_mul_of_dvd_left (map_dvd C huk) _)
  rcases hz u with rfl | hu0
  · rw [C_0, zero_dvd_iff] at h1
    rw [h1]; exact dvd_zero _
  obtain ⟨k', rfl⟩ := h1
  obtain ⟨t', rfl⟩ := hut
  have hlck : (C u * k').leadingCoeff = u * k'.leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_C]
  have hdegk : (C u * k').natDegree = k'.natDegree := natDegree_C_mul hu0
  have hrel : IsRelPrime t' k'.leadingCoeff :=
    isRelPrime_of_isGcd ⟨dvd_mul_right u t', hlck ▸ huk, hu⟩ hu0 rfl hlck
  have hdiv' : C t' ∣ f * k' := by
    have : C u * C t' ∣ C u * (f * k') := by
      rw [← C_mul]; convert hdiv using 1; ring
    exact (mul_dvd_mul_iff_left (by rwa [Ne, C_eq_zero])).1 this
  have hlc : t' ∣ f.leadingCoeff := by
    have := (C_dvd_iff_dvd_coeff _ _).1 hdiv' (f.natDegree + k'.natDegree)
    rw [coeff_mul_degree_add_degree] at this
    exact dvd_of_isRelPrime_of_dvd_mul hG hz hrel (by rwa [mul_comm])
  rw [C_mul]
  refine mul_dvd_mul_left (C u) ?_
  rcases Nat.eq_zero_or_pos f.natDegree with hf0 | hf0
  · have hlf : f.leadingCoeff = f.coeff 0 := by rw [leadingCoeff, hf0]
    have hunit : IsUnit t' := hcop t' (dvd_mul_left t' u) (by
      rw [eq_C_of_natDegree_eq_zero hf0]; exact map_dvd C (hlf ▸ hlc))
    exact (hunit.map C).dvd
  · have hlt : f.eraseLead.natDegree < f.natDegree :=
      lt_of_le_of_lt (eraseLead_natDegree_le f) (Nat.sub_lt hf0 one_pos)
    have hsplit := eraseLead_add_C_mul_X_pow f
    have hd : C t' ∣ f.eraseLead * k' := by
      have h3 : f.eraseLead * k' = f * k' - C f.leadingCoeff * X ^ f.natDegree * k' := by
        rw [eq_sub_iff_add_eq, ← add_mul, hsplit]
      rw [h3]
      exact dvd_sub hdiv' (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (map_dvd C hlc) _) _)
    refine ih (f.eraseLead.natDegree + k'.natDegree) (by omega) f.eraseLead k' le_rfl t'
      (fun d hd hdf => hcop d (hd.trans (dvd_mul_left t' u)) ?_) hd
    rw [← hsplit]
    exact dvd_add hdf (dvd_mul_of_dvd_left (map_dvd C (hd.trans hlc)) _)

/-- Gauss for a primitive polynomial. -/
lemma dvd_of_primitive (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) {f k : A[X]} {t : A}
    (hf : ∀ d, C d ∣ f → IsUnit d) (h : C t ∣ f * k) : C t ∣ k :=
  gauss hG hz _ f k le_rfl t (fun d _ hd => hf d hd) h

omit [IsDomain A] in
/-- Contents exist. -/
lemma exists_content (hG : HasGcd A) :
    ∀ (n : ℕ) (f : A[X]), (∀ i, n ≤ i → f.coeff i = 0) →
      ∃ c : A, C c ∣ f ∧ ∀ d, C d ∣ f → d ∣ c := by
  intro n
  induction n with
  | zero =>
    intro f hf
    have : f = 0 := Polynomial.ext fun i => by rw [hf i (Nat.zero_le i), coeff_zero]
    exact ⟨0, by rw [this]; exact dvd_zero _, fun d _ => dvd_zero d⟩
  | succ n ih =>
    intro f hf
    obtain ⟨c, hc, hcd⟩ := ih f.divX (fun i hi => by rw [coeff_divX]; exact hf _ (by omega))
    obtain ⟨g, hg0, hgc, hg⟩ := hG (f.coeff 0) c
    refine ⟨g, (C_dvd_iff_dvd_coeff _ _).2 fun i => ?_, fun d hd => ?_⟩
    · rcases i with _ | i
      · exact hg0
      · have := (C_dvd_iff_dvd_coeff _ _).1 hc i
        rw [coeff_divX] at this
        exact hgc.trans this
    · refine hg d ((C_dvd_iff_dvd_coeff _ _).1 hd 0) (hcd d ((C_dvd_iff_dvd_coeff _ _).2 ?_))
      intro i
      rw [coeff_divX]
      exact (C_dvd_iff_dvd_coeff _ _).1 hd (i + 1)

omit [IsDomain A] in
lemma exists_content' (hG : HasGcd A) (f : A[X]) :
    ∃ c : A, C c ∣ f ∧ ∀ d, C d ∣ f → d ∣ c :=
  exists_content hG (f.natDegree + 1) f fun _ hi => coeff_eq_zero_of_natDegree_lt (by omega)

/-- Primitive parts exist. -/
lemma exists_primPart (hG : HasGcd A) {f : A[X]} (hf : f ≠ 0) :
    ∃ c : A, ∃ f₀ : A[X], f = C c * f₀ ∧ c ≠ 0 ∧ ∀ d, C d ∣ f₀ → IsUnit d := by
  obtain ⟨c, ⟨f₀, rfl⟩, hcd⟩ := exists_content' hG f
  have hc : c ≠ 0 := by rintro rfl; exact hf (by rw [C_0, zero_mul])
  refine ⟨c, f₀, rfl, hc, fun d hd => isUnit_of_dvd_one ?_⟩
  have : c * d ∣ c * 1 := by
    rw [mul_one]; exact hcd _ (by rw [C_mul]; exact mul_dvd_mul_left _ hd)
  exact (mul_dvd_mul_iff_left hc).1 this

end Gauss

section Field

/-- **Euclid's algorithm** in `K[X]` over a field with decidable equality (trusted primitive:
constructively valid statement, classical Mathlib proof). -/
@[cprim]
theorem exists_isGcd_polynomial_field (K : Type*) [Field K] (_hK : ∀ x : K, x = 0 ∨ x ≠ 0)
    (f g : K[X]) : ∃ h : K[X], IsGcd h f g := by
  classical
  exact ⟨EuclideanDomain.gcd f g, EuclideanDomain.gcd_dvd_left f g,
    EuclideanDomain.gcd_dvd_right f g, fun c hcf hcg => EuclideanDomain.dvd_gcd hcf hcg⟩

end Field

section PolyGcd

variable {A : Type*} [CommRing A] [IsDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- Clearing denominators. -/
lemma exists_clear (m : K[X]) : ∃ s : A, s ≠ 0 ∧ ∃ m' : A[X],
    m'.map (algebraMap A K) = C (algebraMap A K s) * m := by
  obtain ⟨s, hs, h⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) m
  exact ⟨s, nonZeroDivisors.ne_zero hs, _, by
    rw [h, Algebra.smul_def, Polynomial.algebraMap_apply]⟩

/-- Divisibility by a primitive polynomial descends from `K[X]` to `A[X]`. -/
lemma dvd_of_map_dvd (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) {h₀ f : A[X]}
    (hp : ∀ d, C d ∣ h₀ → IsUnit d) (h : h₀.map (algebraMap A K) ∣ f.map (algebraMap A K)) :
    h₀ ∣ f := by
  have hinj : Function.Injective (Polynomial.map (algebraMap A K)) :=
    map_injective _ (IsFractionRing.injective A K)
  obtain ⟨m, hm⟩ := h
  obtain ⟨s, hs, m', hm'⟩ := exists_clear (A := A) K m
  have h1 : C s * f = h₀ * m' := hinj (by
    rw [Polynomial.map_mul, Polynomial.map_mul, map_C, hm, hm']; ring)
  obtain ⟨m'', rfl⟩ := dvd_of_primitive hG hz hp (h1 ▸ dvd_mul_right (C s) f)
  refine ⟨m'', mul_left_cancel₀ (by rwa [Ne, C_eq_zero]) ?_⟩
  rw [h1]; ring

lemma hzero_fraction (hz : ∀ a : A, a = 0 ∨ a ≠ 0) (x : K) : x = 0 ∨ x ≠ 0 := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) x
  rcases hz a with rfl | ha
  · exact Or.inl (IsLocalization.mk'_zero _)
  · refine Or.inr fun h => ha ?_
    have := (IsLocalization.mk'_eq_zero_iff a s).1 h
    obtain ⟨⟨m, hm⟩, hm0⟩ := this
    exact (mul_eq_zero.1 hm0).resolve_left (nonZeroDivisors.ne_zero hm)

omit [IsDomain A] in
/-- The zero test passes to `A[X]`. -/
lemma polynomial_eq_zero_or (hz : ∀ a : A, a = 0 ∨ a ≠ 0) (f : A[X]) : f = 0 ∨ f ≠ 0 := by
  have key : ∀ n, (∀ i < n, f.coeff i = 0) ∨ ∃ i < n, f.coeff i ≠ 0 := by
    intro n
    induction n with
    | zero => exact Or.inl fun i hi => absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      rcases ih with h | ⟨i, hi, hne⟩
      · rcases hz (f.coeff n) with h0 | h0
        · refine Or.inl fun i hi => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
          · exact h i h'
          · exact h0
        · exact Or.inr ⟨n, Nat.lt_succ_self n, h0⟩
      · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hne⟩
  rcases key (f.natDegree + 1) with h | ⟨i, -, hne⟩
  · refine Or.inl (Polynomial.ext fun i => ?_)
    rw [coeff_zero]
    rcases Nat.lt_or_ge i (f.natDegree + 1) with hi | hi
    · exact h i hi
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  · exact Or.inr fun h => hne (by rw [h, coeff_zero])

/-- **Polynomial rings over GCD domains have gcds.** -/
theorem hasGcd_polynomial (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) : HasGcd A[X] := by
  let K := FractionRing A
  have hinj : Function.Injective (Polynomial.map (algebraMap A K)) :=
    map_injective _ (IsFractionRing.injective A K)
  have hzX := polynomial_eq_zero_or hz
  intro f g
  rcases hzX f with rfl | hf
  · exact ⟨g, isGcd_zero_left g⟩
  rcases hzX g with rfl | hg
  · exact ⟨f, isGcd_zero_right f⟩
  obtain ⟨h, hhf, hhg, hhc⟩ := exists_isGcd_polynomial_field K (hzero_fraction K hz)
    (f.map (algebraMap A K)) (g.map (algebraMap A K))
  obtain ⟨s, hs, h', hh'⟩ := exists_clear (A := A) K h
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hf (hinj (by rw [zero_dvd_iff.1 hhf, Polynomial.map_zero]))
  have hh'0 : h' ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero, eq_comm, mul_eq_zero, C_eq_zero] at hh'
    rcases hh' with h1 | h1
    · exact hs ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective A K) s h1)
    · exact hh0 h1
  obtain ⟨c', h₀, rfl, hc', hprim⟩ := exists_primPart hG hh'0
  have hunit : ∀ a : A, a ≠ 0 → IsUnit (C (algebraMap A K a)) := fun a ha =>
    (IsUnit.mk0 _ (fun h0 => ha ((injective_iff_map_eq_zero _).1
      (IsFractionRing.injective A K) a h0))).map C
  rw [Polynomial.map_mul, map_C] at hh'
  -- `h` and `h₀` are associated in `K[X]`
  have hh₀ : h ∣ h₀.map (algebraMap A K) := by
    rw [← (hunit c' hc').dvd_mul_left, hh']; exact dvd_mul_left _ _
  have h₀h : h₀.map (algebraMap A K) ∣ h := by
    rw [← (hunit s hs).dvd_mul_left, ← hh']; exact dvd_mul_left _ _
  obtain ⟨cf, hcf, hcfd⟩ := exists_content' hG f
  obtain ⟨cg, hcg, hcgd⟩ := exists_content' hG g
  obtain ⟨c, hcf', hcg', hcc⟩ := hG cf cg
  have hdiv : ∀ {p : A[X]}, h ∣ p.map (algebraMap A K) → C c ∣ p → C c * h₀ ∣ p := by
    intro p hp hcp
    obtain ⟨m, rfl⟩ := dvd_of_map_dvd K hG hz hprim (h₀h.trans hp)
    rw [mul_comm h₀]
    exact mul_dvd_mul_right (dvd_of_primitive hG hz hprim hcp) h₀
  refine ⟨C c * h₀, hdiv hhf ((map_dvd C hcf').trans hcf), hdiv hhg ((map_dvd C hcg').trans hcg),
    fun D hDf hDg => ?_⟩
  have hD0 : D ≠ 0 := by rintro rfl; exact hf (zero_dvd_iff.1 hDf)
  obtain ⟨cD, D₀, rfl, -, hD₀⟩ := exists_primPart hG hD0
  have hcD : cD ∣ c := hcc _ (hcfd _ ((dvd_mul_right _ _).trans hDf))
    (hcgd _ ((dvd_mul_right _ _).trans hDg))
  have hmap : ∀ {p : A[X]}, C cD * D₀ ∣ p → D₀.map (algebraMap A K) ∣ p.map (algebraMap A K) :=
    fun hp => Polynomial.map_dvd _ ((dvd_mul_left _ _).trans hp)
  have : D₀ ∣ h₀ := dvd_of_map_dvd K hG hz hD₀ ((hhc _ (hmap hDf) (hmap hDg)).trans hh₀)
  exact mul_dvd_mul (map_dvd C hcD) this

end PolyGcd

section MvPoly

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
lemma eq_zero_or_of_ringEquiv {B : Type*} [CommRing B] (e : A ≃+* B)
    (hz : ∀ b : B, b = 0 ∨ b ≠ 0) (a : A) : a = 0 ∨ a ≠ 0 := by
  rcases hz (e a) with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr fun h' => h (by rw [h', map_zero])

/-- **Multivariate polynomial rings over GCD domains have gcds** (and a zero test). -/
theorem hasGcd_mvPolynomial (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) :
    ∀ n : ℕ, HasGcd (MvPolynomial (Fin n) A) ∧
      ∀ f : MvPolynomial (Fin n) A, f = 0 ∨ f ≠ 0 := by
  intro n
  induction n with
  | zero =>
    let e := MvPolynomial.isEmptyRingEquiv A (Fin 0)
    exact ⟨hasGcd_of_ringEquiv e hG, eq_zero_or_of_ringEquiv e hz⟩
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv A n).toRingEquiv
    exact ⟨hasGcd_of_ringEquiv e (hasGcd_polynomial ih.1 ih.2),
      eq_zero_or_of_ringEquiv e (polynomial_eq_zero_or ih.2)⟩

/-- **Laurent polynomial rings over GCD domains have gcds.** -/
theorem hasGcd_laurent (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) :
    HasGcd (LaurentPolynomial A) :=
  hasGcd_of_isLocalization (Submonoid.powers (X : A[X])) _ (hasGcd_polynomial hG hz)
    (polynomial_eq_zero_or hz)

end MvPoly

end BezoutCounterexample.Constructive
