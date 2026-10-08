import BezoutCounterexample.Constructive.GCDPoly
import BezoutCounterexample.Constructive.SGDQ

/-!
# GCD domains up to an escape (D5; `docs/d5-plan.md`, step 4, O6)

`GCDPoly.lean` with gcds only **up to `Q`** (`HasGcdQ Q A`): every conclusion that consumes a gcd
fact is weakened to `… ∨ Q`, and every unit/coprimality hypothesis that a Q-process produces is
read up to `Q`. Zero tests stay exact. Once an escape is met, any candidate is accepted
(`isGcdQ_of_Q`).

* `isGcdQ_mul_left`, `dvd_of_isRelPrimeQ_of_dvd_mul`, `isRelPrimeQ_of_isGcdQ`,
  `hasGcdQ_of_ringEquiv`, `hasGcdQ_of_isLocalization`;
* `gaussQ`, `exists_contentQ`, `exists_primPartQ`, `dvd_of_map_dvdQ`;
* `hasGcdQ_polynomial` (Euclid over the fraction field is exact: the cprim
  `exists_isGcd_polynomial_field`), `hasGcdQ_mvPolynomial`, `hasGcdQ_laurent`.
-/

namespace BezoutCounterexample.Constructive

open Polynomial

/-- Gcds up to `Q`. -/
def HasGcdQ (Q : Prop) (A : Type*) [CommRing A] : Prop := ∀ a b : A, ∃ g, IsGcdQ Q g a b

/-- Coprime up to `Q`. -/
def IsRelPrimeQ {A : Type*} [CommRing A] (Q : Prop) (a b : A) : Prop :=
  ∀ d, d ∣ a → d ∣ b → IsUnit d ∨ Q

lemma hasGcdQ_of_hasGcd {A : Type*} [CommRing A] (Q : Prop) (h : HasGcd A) : HasGcdQ Q A :=
  fun a b => let ⟨g, hg⟩ := h a b; ⟨g, isGcdQ_of_isGcd Q hg⟩

section Basic

variable {A : Type*} [CommRing A] [IsDomain A] {Q : Prop}

/-- `gcd(ca, cb) = c · gcd(a, b)`, up to `Q`. -/
lemma isGcdQ_mul_left (hG : HasGcdQ Q A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) {g a b : A}
    (hg : IsGcdQ Q g a b) (c : A) : IsGcdQ Q (c * g) (c * a) (c * b) := by
  obtain ⟨h, hha, hhb, hhc⟩ := hG (c * a) (c * b)
  refine ⟨hg.1.imp_left (mul_dvd_mul_left c), hg.2.1.imp_left (mul_dvd_mul_left c),
    fun d hda hdb => ?_⟩
  rcases hhc d hda hdb with hdh | hQ
  swap; · exact Or.inr hQ
  rcases hz c with rfl | hc
  · left; rw [zero_mul]; exact dvd_zero d
  rcases hhc c (dvd_mul_right c a) (dvd_mul_right c b) with ⟨h', rfl⟩ | hQ
  swap; · exact Or.inr hQ
  rcases hha with hha | hQ
  swap; · exact Or.inr hQ
  rcases hhb with hhb | hQ
  swap; · exact Or.inr hQ
  rcases hg.2.2 h' ((mul_dvd_mul_iff_left hc).1 hha) ((mul_dvd_mul_iff_left hc).1 hhb) with
    hh'g | hQ
  · exact Or.inl (hdh.trans (mul_dvd_mul_left c hh'g))
  · exact Or.inr hQ

/-- Coprime cancellation, up to `Q`. -/
lemma dvd_of_isRelPrimeQ_of_dvd_mul (hG : HasGcdQ Q A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0)
    {a b c : A} (h : IsRelPrimeQ Q a b) (hd : a ∣ b * c) : a ∣ c ∨ Q := by
  obtain ⟨g, hg⟩ := hG a b
  rcases hg.1 with hga | hQ
  swap; · exact Or.inr hQ
  rcases hg.2.1 with hgb | hQ
  swap; · exact Or.inr hQ
  rcases h g hga hgb with hu | hQ
  swap; · exact Or.inr hQ
  rcases (isGcdQ_mul_left hG hz hg c).2.2 a (dvd_mul_left a c) (by rw [mul_comm]; exact hd) with
    h1 | hQ
  · exact Or.inl (hu.dvd_mul_right.1 h1)
  · exact Or.inr hQ

/-- Dividing by a nonzero gcd leaves a pair coprime up to `Q`. -/
lemma isRelPrimeQ_of_isGcdQ {g a b a' b' : A} (hg : IsGcdQ Q g a b) (hg0 : g ≠ 0)
    (ha : a = g * a') (hb : b = g * b') : IsRelPrimeQ Q a' b' := by
  intro d hda hdb
  rcases hg.2.2 _ (ha ▸ mul_dvd_mul_left g hda) (hb ▸ mul_dvd_mul_left g hdb) with h1 | hQ
  · refine Or.inl (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hg0).1 ?_))
    rwa [mul_one]
  · exact Or.inr hQ

omit [IsDomain A] in
/-- Transport along a ring isomorphism. -/
lemma hasGcdQ_of_ringEquiv {B : Type*} [CommRing B] (e : A ≃+* B) (hB : HasGcdQ Q B) :
    HasGcdQ Q A := by
  intro a b
  obtain ⟨g, hga, hgb, hgc⟩ := hB (e a) (e b)
  have hdvd : ∀ {x y : B}, x ∣ y → e.symm x ∣ e.symm y := fun h => map_dvd e.symm h
  refine ⟨e.symm g, hga.imp_left fun h => by simpa using hdvd h,
    hgb.imp_left fun h => by simpa using hdvd h, fun c hca hcb => ?_⟩
  exact (hgc (e c) (map_dvd e hca) (map_dvd e hcb)).imp_left fun h => by simpa using hdvd h

end Basic

section Localization

variable {A : Type*} [CommRing A] [IsDomain A] (S : Submonoid A) (L : Type*) [CommRing L]
  [Algebra A L] [IsLocalization S L] {Q : Prop}

include S in
/-- **Localisations**, up to `Q`. -/
theorem hasGcdQ_of_isLocalization (hG : HasGcdQ Q A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) :
    HasGcdQ Q L := by
  intro x y
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective S y
  obtain ⟨g, hg⟩ := hG a b
  have h1 : ∀ (a : A) (s : S), IsLocalization.mk' L a s ∣ algebraMap A L a := fun a s =>
    ⟨algebraMap A L s, (IsLocalization.mk'_spec L a s).symm⟩
  have h2 : ∀ (a : A) (s : S), algebraMap A L a ∣ IsLocalization.mk' L a s := fun a s => by
    rw [← (IsLocalization.map_units L s).dvd_mul_right, IsLocalization.mk'_spec]
  refine ⟨algebraMap A L g, hg.1.imp_left fun h => (_root_.map_dvd _ h).trans (h2 a s),
    hg.2.1.imp_left fun h => (_root_.map_dvd _ h).trans (h2 b t), fun z hza hzb => ?_⟩
  obtain ⟨⟨c, u⟩, rfl⟩ := IsLocalization.mk'_surjective S z
  have hc : ∀ {a : A} (s : S), IsLocalization.mk' L c u ∣ IsLocalization.mk' L a s →
      algebraMap A L c ∣ algebraMap A L a := fun s h => by
    rw [← IsLocalization.mk'_spec L c u, (IsLocalization.map_units L u).mul_right_dvd]
    exact h.trans (h1 _ s)
  obtain ⟨σ, hσ, hσa⟩ := exists_dvd_of_dvd_localization S L (hc s hza)
  obtain ⟨τ, hτ, hτb⟩ := exists_dvd_of_dvd_localization S L (hc t hzb)
  rcases (isGcdQ_mul_left hG hz hg (σ * τ)).2.2 c
      (by rw [mul_comm σ, mul_assoc]; exact dvd_mul_of_dvd_right hσa τ)
      (by rw [mul_assoc]; exact dvd_mul_of_dvd_right hτb σ) with hcg | hQ
  swap; · exact Or.inr hQ
  have hst : IsUnit (algebraMap A L (σ * τ)) :=
    IsLocalization.map_units L (⟨σ * τ, S.mul_mem hσ hτ⟩ : S)
  have : algebraMap A L c ∣ algebraMap A L g := by
    rw [← hst.dvd_mul_left, ← map_mul]; exact _root_.map_dvd _ hcg
  exact Or.inl ((h1 c u).trans this)

end Localization

section Gauss

variable {A : Type*} [CommRing A] [IsDomain A] {Q : Prop}

/-- **Gauss's lemma**, up to `Q`. -/
theorem gaussQ (hG : HasGcdQ Q A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) :
    ∀ (N : ℕ) (f k : A[X]), f.natDegree + k.natDegree ≤ N → ∀ t : A,
      (∀ d, d ∣ t → C d ∣ f → IsUnit d ∨ Q) → C t ∣ f * k → C t ∣ k ∨ Q := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro f k hN t hcop hdiv
  obtain ⟨u, hut, huk, hu⟩ := hG t k.leadingCoeff
  rcases hut with hut | hQ
  swap; · exact Or.inr hQ
  rcases huk with huk | hQ
  swap; · exact Or.inr hQ
  -- Step 1: `C u ∣ k`, up to `Q`.
  have h1 : C u ∣ k ∨ Q := by
    rcases Nat.eq_zero_or_pos k.natDegree with hk0 | hk0
    · left
      rw [eq_C_of_natDegree_eq_zero hk0]
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
      rcases ih (f.natDegree + k.eraseLead.natDegree) (by omega) f k.eraseLead le_rfl u
          (fun d hd hdf => hcop d (hd.trans hut) hdf) hd with h | hQ
      · left
        rw [← hsplit]
        exact dvd_add h (dvd_mul_of_dvd_left (map_dvd C huk) _)
      · exact Or.inr hQ
  rcases h1 with h1 | hQ
  swap; · exact Or.inr hQ
  rcases hz u with rfl | hu0
  · rw [C_0, zero_dvd_iff] at h1
    rw [h1]; exact Or.inl (dvd_zero _)
  obtain ⟨k', rfl⟩ := h1
  obtain ⟨t', rfl⟩ := hut
  have hlck : (C u * k').leadingCoeff = u * k'.leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_C]
  have hdegk : (C u * k').natDegree = k'.natDegree := natDegree_C_mul hu0
  have hrel : IsRelPrimeQ Q t' k'.leadingCoeff :=
    isRelPrimeQ_of_isGcdQ ⟨Or.inl (dvd_mul_right u t'), Or.inl (hlck ▸ huk), hu⟩ hu0 rfl hlck
  have hdiv' : C t' ∣ f * k' := by
    have : C u * C t' ∣ C u * (f * k') := by
      rw [← C_mul]; convert hdiv using 1; ring
    exact (mul_dvd_mul_iff_left (by rwa [Ne, C_eq_zero])).1 this
  rcases dvd_of_isRelPrimeQ_of_dvd_mul hG hz hrel (by
      have := (C_dvd_iff_dvd_coeff _ _).1 hdiv' (f.natDegree + k'.natDegree)
      rw [coeff_mul_degree_add_degree] at this
      rwa [mul_comm]) with hlc | hQ
  swap; · exact Or.inr hQ
  rw [C_mul]
  rcases Nat.eq_zero_or_pos f.natDegree with hf0 | hf0
  · have hlf : f.leadingCoeff = f.coeff 0 := by rw [leadingCoeff, hf0]
    rcases hcop t' (dvd_mul_left t' u) (by
        rw [eq_C_of_natDegree_eq_zero hf0]; exact map_dvd C (hlf ▸ hlc)) with hunit | hQ
    · exact Or.inl (mul_dvd_mul_left (C u) (hunit.map C).dvd)
    · exact Or.inr hQ
  · have hlt : f.eraseLead.natDegree < f.natDegree :=
      lt_of_le_of_lt (eraseLead_natDegree_le f) (Nat.sub_lt hf0 one_pos)
    have hsplit := eraseLead_add_C_mul_X_pow f
    have hd : C t' ∣ f.eraseLead * k' := by
      have h3 : f.eraseLead * k' = f * k' - C f.leadingCoeff * X ^ f.natDegree * k' := by
        rw [eq_sub_iff_add_eq, ← add_mul, hsplit]
      rw [h3]
      exact dvd_sub hdiv' (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (map_dvd C hlc) _) _)
    rcases ih (f.eraseLead.natDegree + k'.natDegree) (by omega) f.eraseLead k' le_rfl t'
        (fun d hd hdf => hcop d (hd.trans (dvd_mul_left t' u)) (by
          rw [← hsplit]
          exact dvd_add hdf (dvd_mul_of_dvd_left (map_dvd C (hd.trans hlc)) _))) hd with h | hQ
    · exact Or.inl (mul_dvd_mul_left (C u) h)
    · exact Or.inr hQ

/-- Gauss for a primitive polynomial, up to `Q`. -/
lemma dvd_of_primitiveQ (hG : HasGcdQ Q A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) {f k : A[X]} {t : A}
    (hf : ∀ d, C d ∣ f → IsUnit d ∨ Q) (h : C t ∣ f * k) : C t ∣ k ∨ Q :=
  gaussQ hG hz _ f k le_rfl t (fun d _ hd => hf d hd) h

omit [IsDomain A] in
/-- Contents, up to `Q`. -/
lemma exists_contentQ (hG : HasGcdQ Q A) :
    ∀ (n : ℕ) (f : A[X]), (∀ i, n ≤ i → f.coeff i = 0) →
      ∃ c : A, (C c ∣ f ∨ Q) ∧ ∀ d, C d ∣ f → d ∣ c ∨ Q := by
  intro n
  induction n with
  | zero =>
    intro f hf
    have : f = 0 := Polynomial.ext fun i => by rw [hf i (Nat.zero_le i), coeff_zero]
    exact ⟨0, Or.inl (by rw [this]; exact dvd_zero _), fun d _ => Or.inl (dvd_zero d)⟩
  | succ n ih =>
    intro f hf
    obtain ⟨c, hc, hcd⟩ := ih f.divX (fun i hi => by rw [coeff_divX]; exact hf _ (by omega))
    obtain ⟨g, hg0, hgc, hg⟩ := hG (f.coeff 0) c
    refine ⟨g, ?_, fun d hd => ?_⟩
    · rcases hc with hc | hQ
      swap; · exact Or.inr hQ
      rcases hg0 with hg0 | hQ
      swap; · exact Or.inr hQ
      rcases hgc with hgc | hQ
      swap; · exact Or.inr hQ
      refine Or.inl ((C_dvd_iff_dvd_coeff _ _).2 fun i => ?_)
      rcases i with _ | i
      · exact hg0
      · have := (C_dvd_iff_dvd_coeff _ _).1 hc i
        rw [coeff_divX] at this
        exact hgc.trans this
    · rcases hcd d ((C_dvd_iff_dvd_coeff _ _).2 fun i => by
          rw [coeff_divX]; exact (C_dvd_iff_dvd_coeff _ _).1 hd (i + 1)) with hdc | hQ
      · exact hg d ((C_dvd_iff_dvd_coeff _ _).1 hd 0) hdc
      · exact Or.inr hQ

omit [IsDomain A] in
lemma exists_contentQ' (hG : HasGcdQ Q A) (f : A[X]) :
    ∃ c : A, (C c ∣ f ∨ Q) ∧ ∀ d, C d ∣ f → d ∣ c ∨ Q :=
  exists_contentQ hG (f.natDegree + 1) f fun _ hi => coeff_eq_zero_of_natDegree_lt (by omega)

/-- Primitive parts, up to `Q`. -/
lemma exists_primPartQ (hG : HasGcdQ Q A) {f : A[X]} (hf : f ≠ 0) :
    (∃ c : A, ∃ f₀ : A[X], f = C c * f₀ ∧ c ≠ 0 ∧ ∀ d, C d ∣ f₀ → IsUnit d ∨ Q) ∨ Q := by
  obtain ⟨c, hc, hcd⟩ := exists_contentQ' hG f
  rcases hc with ⟨f₀, rfl⟩ | hQ
  swap; · exact Or.inr hQ
  have hc : c ≠ 0 := by rintro rfl; exact hf (by rw [C_0, zero_mul])
  refine Or.inl ⟨c, f₀, rfl, hc, fun d hd => ?_⟩
  rcases hcd _ (by rw [C_mul]; exact mul_dvd_mul_left _ hd) with h | hQ
  · refine Or.inl (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hc).1 ?_))
    rwa [mul_one]
  · exact Or.inr hQ

end Gauss

section PolyGcd

variable {A : Type*} [CommRing A] [IsDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K] {Q : Prop}

/-- Divisibility by a primitive polynomial descends from `K[X]`, up to `Q`. -/
lemma dvd_of_map_dvdQ (hG : HasGcdQ Q A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) {h₀ f : A[X]}
    (hp : ∀ d, C d ∣ h₀ → IsUnit d ∨ Q) (h : h₀.map (algebraMap A K) ∣ f.map (algebraMap A K)) :
    h₀ ∣ f ∨ Q := by
  have hinj : Function.Injective (Polynomial.map (algebraMap A K)) :=
    map_injective _ (IsFractionRing.injective A K)
  obtain ⟨m, hm⟩ := h
  obtain ⟨s, hs, m', hm'⟩ := exists_clear (A := A) K m
  have h1 : C s * f = h₀ * m' := hinj (by
    rw [Polynomial.map_mul, Polynomial.map_mul, map_C, hm, hm']; ring)
  rcases dvd_of_primitiveQ hG hz hp (h1 ▸ dvd_mul_right (C s) f) with ⟨m'', rfl⟩ | hQ
  · refine Or.inl ⟨m'', mul_left_cancel₀ (by rwa [Ne, C_eq_zero]) ?_⟩
    rw [h1]; ring
  · exact Or.inr hQ

/-- **Polynomial rings**, gcds up to `Q`. -/
theorem hasGcdQ_polynomial (hG : HasGcdQ Q A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) :
    HasGcdQ Q A[X] := by
  let K := FractionRing A
  have hinj : Function.Injective (Polynomial.map (algebraMap A K)) :=
    map_injective _ (IsFractionRing.injective A K)
  have hzX := polynomial_eq_zero_or hz
  intro f g
  rcases hzX f with rfl | hf
  · exact ⟨g, isGcdQ_of_isGcd Q (isGcd_zero_left g)⟩
  rcases hzX g with rfl | hg
  · exact ⟨f, isGcdQ_of_isGcd Q (isGcd_zero_right f)⟩
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
  rcases exists_primPartQ hG hh'0 with ⟨c', h₀, rfl, hc', hprim⟩ | hQ
  swap; · exact ⟨0, isGcdQ_of_Q hQ _ _ _⟩
  have hunit : ∀ a : A, a ≠ 0 → IsUnit (C (algebraMap A K a)) := fun a ha =>
    (IsUnit.mk0 _ (fun h0 => ha ((injective_iff_map_eq_zero _).1
      (IsFractionRing.injective A K) a h0))).map C
  rw [Polynomial.map_mul, map_C] at hh'
  have hh₀ : h ∣ h₀.map (algebraMap A K) := by
    rw [← (hunit c' hc').dvd_mul_left, hh']; exact dvd_mul_left _ _
  have h₀h : h₀.map (algebraMap A K) ∣ h := by
    rw [← (hunit s hs).dvd_mul_left, ← hh']; exact dvd_mul_left _ _
  obtain ⟨cf, hcf, hcfd⟩ := exists_contentQ' hG f
  obtain ⟨cg, hcg, hcgd⟩ := exists_contentQ' hG g
  obtain ⟨c, hcf', hcg', hcc⟩ := hG cf cg
  rcases hcf with hcf | hQ
  swap; · exact ⟨0, isGcdQ_of_Q hQ _ _ _⟩
  rcases hcg with hcg | hQ
  swap; · exact ⟨0, isGcdQ_of_Q hQ _ _ _⟩
  rcases hcf' with hcf' | hQ
  swap; · exact ⟨0, isGcdQ_of_Q hQ _ _ _⟩
  rcases hcg' with hcg' | hQ
  swap; · exact ⟨0, isGcdQ_of_Q hQ _ _ _⟩
  have hdiv : ∀ {p : A[X]}, h ∣ p.map (algebraMap A K) → C c ∣ p → C c * h₀ ∣ p ∨ Q := by
    intro p hp hcp
    rcases dvd_of_map_dvdQ K hG hz hprim (h₀h.trans hp) with ⟨m, rfl⟩ | hQ
    swap; · exact Or.inr hQ
    rcases dvd_of_primitiveQ hG hz hprim hcp with hm | hQ
    · rw [mul_comm h₀]; exact Or.inl (mul_dvd_mul_right hm h₀)
    · exact Or.inr hQ
  refine ⟨C c * h₀, hdiv hhf ((map_dvd C hcf').trans hcf),
    hdiv hhg ((map_dvd C hcg').trans hcg), fun D hDf hDg => ?_⟩
  have hD0 : D ≠ 0 := by rintro rfl; exact hf (zero_dvd_iff.1 hDf)
  rcases exists_primPartQ hG hD0 with ⟨cD, D₀, rfl, -, hD₀⟩ | hQ
  swap; · exact Or.inr hQ
  rcases hcfd _ ((dvd_mul_right _ _).trans hDf) with h1 | hQ
  swap; · exact Or.inr hQ
  rcases hcgd _ ((dvd_mul_right _ _).trans hDg) with h2 | hQ
  swap; · exact Or.inr hQ
  rcases hcc _ h1 h2 with hcD | hQ
  swap; · exact Or.inr hQ
  have hmap : ∀ {p : A[X]}, C cD * D₀ ∣ p → D₀.map (algebraMap A K) ∣ p.map (algebraMap A K) :=
    fun hp => Polynomial.map_dvd _ ((dvd_mul_left _ _).trans hp)
  rcases dvd_of_map_dvdQ K hG hz hD₀ ((hhc _ (hmap hDf) (hmap hDg)).trans hh₀) with h3 | hQ
  · exact Or.inl (mul_dvd_mul (map_dvd C hcD) h3)
  · exact Or.inr hQ

end PolyGcd

section MvPoly

variable {A : Type*} [CommRing A] [IsDomain A] {Q : Prop}

/-- **Multivariate polynomial rings**, gcds up to `Q` (and a zero test). -/
theorem hasGcdQ_mvPolynomial (hG : HasGcdQ Q A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) :
    ∀ n : ℕ, HasGcdQ Q (MvPolynomial (Fin n) A) ∧
      ∀ f : MvPolynomial (Fin n) A, f = 0 ∨ f ≠ 0 := by
  intro n
  induction n with
  | zero =>
    let e := MvPolynomial.isEmptyRingEquiv A (Fin 0)
    exact ⟨hasGcdQ_of_ringEquiv e hG, eq_zero_or_of_ringEquiv e hz⟩
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv A n).toRingEquiv
    exact ⟨hasGcdQ_of_ringEquiv e (hasGcdQ_polynomial ih.1 ih.2),
      eq_zero_or_of_ringEquiv e (polynomial_eq_zero_or ih.2)⟩

/-- **Laurent polynomial rings**, gcds up to `Q`. -/
theorem hasGcdQ_laurent (hG : HasGcdQ Q A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) :
    HasGcdQ Q (LaurentPolynomial A) :=
  hasGcdQ_of_isLocalization (Submonoid.powers (X : A[X])) _ (hasGcdQ_polynomial hG hz)
    (polynomial_eq_zero_or hz)

end MvPoly

end BezoutCounterexample.Constructive
