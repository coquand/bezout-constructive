import BezoutCounterexample.Constructive.FactorialAlg
import BezoutCounterexample.Constructive.Colon
import BezoutCounterexample.Constructive.IdealOps

/-!
# Strong primality test in `ℚ[Y₁, …, Yₙ]` (option 2, M3; Perdry 2004, Thm 4.3)

`FLN n`: for every explicit ideal `I` of `Rₙ = ℚ[Y₁, …, Yₙ]`, either `1 ∈ I`, or explicit
`a, b ∉ I` with `ab ∈ I`, or `I` is prime and some fraction field of `Rₙ ⧸ I` is factorial of
characteristic `0`. Proof by induction on `n` (`fln`), the step `R ↝ R[X]` (`X` the variable `0`,
`R` embedded by `jY`) as in Perdry's Theorem 4.3:
* `P = I ∩ R` by elimination (`exists_elim0`); the test at `P` decides `1 ∈ P` / a split / `P`
  prime with factorial `K = Frac(R ⧸ P)`;
* `φ : R[X] → K[X]`; `ker φ = P R[X] ⊆ I` (`mem_ker_phi`); the extension `Iᵉ = (G)` with
  `G = φ ĝ`, `ĝ ∈ I` (`exists_gcd_list`, clearing denominators); `deg G > 0` since `I ∩ R = P`;
* saturation (Perdry, Lemma 4.1): `G ∣ φ f ⇒ aᵐ f ∈ I`, `a` the leading coefficient
  (pseudo-division by a truncation of `ĝ`);
* `G` reducible ⇒ a split (`aᵐ u₁ · u₂ ∈ I`, degrees `< deg G`); `G` irreducible: if
  `(I : a) ⊄ I`, a split `(a, x)`; otherwise `I = ker(R[X] → K[X] ⧸ (G))`, so `I` is prime with
  fraction field `K[X] ⧸ (G)` (`factorialField_adjoin`). If `Iᵉ = 0`, then `I = P R[X]` with
  fraction field `Frac(K[X])` (`factorialField_fraction`).
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open Polynomial

section Tools

/-- `finSuccEquiv` sends `jY h` to the constant `h`. -/
lemma finSuccEquiv_jY {n : ℕ} (h : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.finSuccEquiv ℚ n (jY h) = C h := by
  have : ((MvPolynomial.finSuccEquiv ℚ n).toAlgHom.comp (jY (n := n))) =
      (Polynomial.CAlgHom : MvPolynomial (Fin n) ℚ →ₐ[ℚ] (MvPolynomial (Fin n) ℚ)[X]) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.finSuccEquiv_X_succ]
  exact congrArg (fun F => F h) this

lemma finSuccEquiv_symm_C {n : ℕ} (h : MvPolynomial (Fin n) ℚ) :
    (MvPolynomial.finSuccEquiv ℚ n).symm (C h) = jY h := by
  rw [← finSuccEquiv_jY, AlgEquiv.symm_apply_apply]

lemma mem_lspan_map {A B F : Type*} [CommRing A] [CommRing B] [FunLike F A B] [RingHomClass F A B]
    (f : F) {l : List A} {x : A} (hx : x ∈ lspan l) : f x ∈ lspan (l.map f) := by
  have : lspan l ≤ (lspan (l.map f)).comap f := by
    rw [lspan, Ideal.span_le]
    intro y hy
    exact Ideal.subset_span (List.mem_map_of_mem hy)
  exact this hx

/-- A gcd of a list in `F[X]` lying in the ideal of the list (iterated Bézout). -/
lemma exists_gcd_list {F : Type*} [Field F] (hz : ∀ x : F, x = 0 ∨ x ≠ 0) :
    ∀ l : List F[X], ∃ g, (∀ x ∈ l, g ∣ x) ∧ g ∈ lspan l
  | [] => ⟨0, fun _ h => absurd h List.not_mem_nil, Ideal.zero_mem _⟩
  | x :: l => by
    obtain ⟨g, hg, hgl⟩ := exists_gcd_list hz l
    obtain ⟨h, u, v, hh, huv⟩ := bezout_field hz x g
    refine ⟨h, fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hh.1
      · exact hh.2.1.trans (hg y hy)
    · rw [← huv]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (List.mem_cons_self ..)))
        (Ideal.mul_mem_left _ _ ?_)
      exact (Ideal.span_mono fun z hz => List.mem_cons_of_mem _ hz) hgl

lemma dvd_of_mem_lspan {A : Type*} [CommRing A] {g : A} {l : List A} (hg : ∀ x ∈ l, g ∣ x)
    {y : A} (hy : y ∈ lspan l) : g ∣ y := by
  have : lspan l ≤ Ideal.span {g} := by
    rw [lspan, Ideal.span_le]
    intro x hx
    exact Ideal.mem_span_singleton.2 (hg x hx)
  exact Ideal.mem_span_singleton.1 (this hy)

/-- **Pseudo-division** by `g` with leading coefficient `a ≠ 0` and positive degree. -/
theorem pseudo_div {R : Type*} [CommRing R] [IsDomain R] (hz : ∀ x : R, x = 0 ∨ x ≠ 0)
    {g : R[X]} (hg : 0 < g.natDegree) :
    ∀ f : R[X], ∃ (m : ℕ) (q r : R[X]), C g.leadingCoeff ^ m * f = q * g + r ∧
      r.natDegree < g.natDegree := by
  have hg0 : g ≠ 0 := fun h => by rw [h, natDegree_zero] at hg; exact lt_irrefl 0 hg
  have ha : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hg0
  suffices H : ∀ N, ∀ f : R[X], f.natDegree ≤ N → ∃ (m : ℕ) (q r : R[X]),
      C g.leadingCoeff ^ m * f = q * g + r ∧ r.natDegree < g.natDegree from
    fun f => H _ f le_rfl
  intro N
  induction N with
  | zero =>
    intro f hf
    exact ⟨0, 0, f, by ring, by omega⟩
  | succ N ih =>
    intro f hf
    rcases Nat.lt_or_ge f.natDegree g.natDegree with hlt | hge
    · exact ⟨0, 0, f, by ring, hlt⟩
    rcases polynomial_eq_zero_or hz f with rfl | hf0
    · exact ⟨0, 0, 0, by ring, by rw [natDegree_zero]; exact hg⟩
    set k := f.natDegree - g.natDegree
    set f' := C g.leadingCoeff * f - C f.leadingCoeff * X ^ k * g with hf'
    have hdeg : f'.natDegree ≤ N := by
      rcases polynomial_eq_zero_or hz f' with h0 | h0
      · rw [h0, natDegree_zero]; exact Nat.zero_le _
      have hp : (C g.leadingCoeff * f).natDegree = f.natDegree := natDegree_C_mul ha
      have hq0 : C f.leadingCoeff * X ^ k ≠ 0 := by
        simpa using leadingCoeff_ne_zero.2 hf0
      have hq : (C f.leadingCoeff * X ^ k * g).natDegree = f.natDegree := by
        rw [natDegree_mul hq0 hg0, natDegree_C_mul_X_pow _ _ (leadingCoeff_ne_zero.2 hf0)]
        omega
      have hlc : (C g.leadingCoeff * f).leadingCoeff = (C f.leadingCoeff * X ^ k * g).leadingCoeff := by
        rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_C_mul_X_pow,
          mul_comm]
      have hpz : C g.leadingCoeff * f ≠ 0 := mul_ne_zero (by simpa using ha) hf0
      have hlt := degree_sub_lt (by rw [degree_eq_natDegree hpz,
        degree_eq_natDegree (mul_ne_zero hq0 hg0), hp, hq]) hpz hlc
      have := natDegree_lt_natDegree h0 hlt
      omega
    obtain ⟨m, q, r, hqr, hr⟩ := ih f' hdeg
    refine ⟨m + 1, q + C (g.leadingCoeff ^ m * f.leadingCoeff) * X ^ k, r, ?_, hr⟩
    rw [hf'] at hqr
    rw [C_mul, C_pow]
    linear_combination hqr

/-- Truncation at degree `d`. -/
def truncAt {R : Type*} [CommRing R] (u : R[X]) (d : ℕ) : R[X] :=
  ∑ i ∈ Finset.range (d + 1), monomial i (u.coeff i)

lemma coeff_truncAt {R : Type*} [CommRing R] (u : R[X]) (d i : ℕ) :
    (truncAt u d).coeff i = if i ≤ d then u.coeff i else 0 := by
  simp only [truncAt, finset_sum_coeff, coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single i (fun j _ hj => if_neg hj) (fun hi => absurd
      (Finset.mem_range.2 (Nat.lt_succ_of_le h)) hi), if_pos rfl]
  · refine Finset.sum_eq_zero fun j hj => if_neg fun hji => h ?_
    rw [← hji]; exact Nat.le_of_lt_succ (Finset.mem_range.1 hj)

lemma natDegree_truncAt_le {R : Type*} [CommRing R] (u : R[X]) (d : ℕ) :
    (truncAt u d).natDegree ≤ d :=
  natDegree_le_iff_coeff_eq_zero.2 fun i hi => by
    rw [coeff_truncAt, if_neg (by
      exact not_le.2 (by exact_mod_cast hi))]

end Tools

section Defs

/-- `P` is prime and `R ⧸ P` has a factorial fraction field of characteristic `0`. -/
def PrimeFF {R : Type} [CommRing R] (P : Ideal R) : Prop :=
  P.IsPrime ∧ ∃ (K : Type) (_ : Field K) (_ : Algebra (R ⧸ P) K),
    IsFractionRing (R ⧸ P) K ∧ FactorialField K ∧ CharZero K

/-- **Strong primality test** at an explicit ideal. -/
def SPrime {R : Type} [CommRing R] (I : List R) : Prop :=
  (1 : R) ∈ lspan I ∨ (∃ a b : R, a * b ∈ lspan I ∧ a ∉ lspan I ∧ b ∉ lspan I) ∨
    PrimeFF (lspan I)

/-- Perdry's **fully Lasker–Noether** property of `ℚ[Y₁, …, Yₙ]` (the strong primality test with
factorial residue fields). -/
def FLN (n : ℕ) : Prop := ∀ I : List (MvPolynomial (Fin n) ℚ), SPrime I

/-- A kernel description by a hom into a factorial field which reaches every element as a
fraction gives `PrimeFF`. -/
theorem primeFF_of_hom {R : Type} [CommRing R] {I : Ideal R} {K : Type} [Field K] (ψ : R →+* K)
    (hker : ∀ f, ψ f = 0 ↔ f ∈ I) (hsurj : ∀ z : K, ∃ u v : R, ψ v ≠ 0 ∧ z = ψ u / ψ v)
    (hFF : FactorialField K) (hchar : CharZero K) : PrimeFF I := by
  have hI : RingHom.ker ψ = I := by ext f; exact hker f
  let ψ' : R ⧸ I →+* K := Ideal.Quotient.lift I ψ fun f hf => (hker f).2 hf
  letI : Algebra (R ⧸ I) K := ψ'.toAlgebra
  have hinj : Function.Injective (algebraMap (R ⧸ I) K) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hker f).1 hx)
  have : FaithfulSMul (R ⧸ I) K := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine ⟨hI ▸ RingHom.ker_isPrime ψ, K, inferInstance, inferInstance,
    IsFractionRing.of_field _ _ fun z => ?_, hFF, hchar⟩
  obtain ⟨u, v, -, huv⟩ := hsurj z
  exact ⟨Ideal.Quotient.mk I u, Ideal.Quotient.mk I v, huv⟩

end Defs

section Step

variable {n : ℕ} (L : List (MvPolynomial (Fin n) ℚ)) {K : Type} [Field K]
  [Algebra (MvPolynomial (Fin n) ℚ ⧸ lspan L) K] [IsFractionRing (MvPolynomial (Fin n) ℚ ⧸ lspan L) K]

/-- `R → R ⧸ P → K`. -/
def iota : MvPolynomial (Fin n) ℚ →+* K :=
  (algebraMap (MvPolynomial (Fin n) ℚ ⧸ lspan L) K).comp (Ideal.Quotient.mk _)

/-- `φ : R[X] → K[X]` (the variable `X` is the variable `0`). -/
def phi : MvPolynomial (Fin (n + 1)) ℚ →+* K[X] :=
  (mapRingHom (iota L (K := K))).comp
    (MvPolynomial.finSuccEquiv ℚ n : MvPolynomial (Fin (n + 1)) ℚ →+* (MvPolynomial (Fin n) ℚ)[X])

variable {L}

lemma iota_eq_zero {h : MvPolynomial (Fin n) ℚ} : iota L (K := K) h = 0 ↔ h ∈ lspan L := by
  rw [iota, RingHom.comp_apply, ← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h0 => IsFractionRing.injective _ K (by rw [h0, map_zero]), fun h0 => by
    rw [h0, map_zero]⟩

lemma phi_apply (f : MvPolynomial (Fin (n + 1)) ℚ) :
    phi L (K := K) f = (MvPolynomial.finSuccEquiv ℚ n f).map (iota L) := rfl

lemma phi_symm (v : (MvPolynomial (Fin n) ℚ)[X]) :
    phi L (K := K) ((MvPolynomial.finSuccEquiv ℚ n).symm v) = v.map (iota L) := by
  rw [phi_apply, AlgEquiv.apply_symm_apply]

lemma phi_jY (h : MvPolynomial (Fin n) ℚ) : phi L (K := K) (jY h) = C (iota L h) := by
  rw [phi_apply, finSuccEquiv_jY, map_C]

/-- **`ker φ = P R[X]`.** -/
lemma mem_ker_phi (f : MvPolynomial (Fin (n + 1)) ℚ) :
    phi L (K := K) f = 0 ↔ f ∈ lspan (L.map jY) := by
  constructor
  · intro hf
    set E := MvPolynomial.finSuccEquiv ℚ n
    have hc : ∀ i, (E f).coeff i ∈ lspan L := fun i => by
      rw [← iota_eq_zero (K := K)]
      have := congrArg (fun F => F.coeff i) hf
      simpa [phi_apply, coeff_map] using this
    have hf' : f = E.symm (E f) := (AlgEquiv.symm_apply_apply E f).symm
    rw [hf', (E f).as_sum_range_C_mul_X_pow, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_mul, map_pow, finSuccEquiv_symm_C]
    refine Ideal.mul_mem_right _ _ ?_
    exact mem_lspan_map jY (hc i)
  · intro hf
    have : lspan (L.map jY) ≤ RingHom.ker (phi L (K := K)) := by
      rw [lspan, Ideal.span_le]
      intro x hx
      obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hx
      rw [SetLike.mem_coe, RingHom.mem_ker, phi_jY, (iota_eq_zero (K := K)).2
        (Ideal.subset_span hh), C_0]
    exact this hf

variable [(lspan L).IsPrime]

/-- **Lifting with a cleared denominator**: `C (ι d) · F = φ u`. -/
lemma exists_lift_phi (F : K[X]) : ∃ (u : MvPolynomial (Fin (n + 1)) ℚ) (d : MvPolynomial (Fin n) ℚ),
    d ∉ lspan L ∧ phi L (K := K) u = C (iota L d) * F := by
  obtain ⟨s, hs, m, hm⟩ := exists_clear (A := MvPolynomial (Fin n) ℚ ⧸ lspan L) K F
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨m', rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective m
  refine ⟨(MvPolynomial.finSuccEquiv ℚ n).symm m', d, fun h => hs
    (Ideal.Quotient.eq_zero_iff_mem.2 h), ?_⟩
  rw [phi_symm]
  rw [Polynomial.map_map] at hm
  exact hm

variable (I : List (MvPolynomial (Fin (n + 1)) ℚ))

omit [(lspan L).IsPrime] in
lemma ker_le (hLI : ∀ h, jY h ∈ lspan I ↔ h ∈ lspan L) : lspan (L.map jY) ≤ lspan I := by
  rw [lspan, Ideal.span_le]
  intro x hx
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hx
  exact (hLI h).2 (Ideal.subset_span hh)

variable {I}

/-- **Saturation** (Perdry, Lemma 4.1): for `ĝ ∈ I` with `deg φ ĝ > 0`, the leading coefficient
`a` of a truncation of `ĝ` satisfies: `φ ĝ ∣ φ f ⇒ aᵐ f ∈ I`. -/
theorem saturation (hzK : ∀ x : K, x = 0 ∨ x ≠ 0) (hLI : ∀ h, jY h ∈ lspan I ↔ h ∈ lspan L)
    {g : MvPolynomial (Fin (n + 1)) ℚ} (hg : g ∈ lspan I) (hdeg : 0 < (phi L (K := K) g).natDegree) :
    ∃ a : MvPolynomial (Fin n) ℚ, a ∉ lspan L ∧ iota L a = (phi L (K := K) g).leadingCoeff ∧
      ∀ f, phi L (K := K) g ∣ phi L f → ∃ m : ℕ, jY a ^ m * f ∈ lspan I := by
  set E := MvPolynomial.finSuccEquiv ℚ n
  set G := phi L (K := K) g with hG
  set d := G.natDegree
  set u := E g
  set a := u.coeff d
  have hcoeff : ∀ i, G.coeff i = iota L (u.coeff i) := fun i => by
    rw [hG, phi_apply, coeff_map]
  have ha : iota L (K := K) a = G.leadingCoeff := (hcoeff d).symm
  have ha0 : a ∉ lspan L := fun h => by
    have : G.leadingCoeff = 0 := by rw [← ha, (iota_eq_zero (K := K)).2 h]
    rw [leadingCoeff_eq_zero] at this
    have hd0 : d = 0 := by simp only [d, this, natDegree_zero]
    omega
  set u' := truncAt u d
  have hmap : u'.map (iota L) = G := by
    ext i
    rw [coeff_map, coeff_truncAt]
    split_ifs with h
    · exact (hcoeff i).symm
    · rw [map_zero, coeff_eq_zero_of_natDegree_lt (not_le.1 h)]
  have ha' : a ≠ 0 := fun h => ha0 (h ▸ Ideal.zero_mem _)
  have hu'd : u'.natDegree = d := le_antisymm (natDegree_truncAt_le u d)
    (le_natDegree_of_ne_zero (by rw [coeff_truncAt, if_pos le_rfl]; exact ha'))
  have hlc : u'.leadingCoeff = a := by
    rw [leadingCoeff, hu'd, coeff_truncAt, if_pos le_rfl]
  have hker := ker_le I hLI
  have hg₁ : E.symm u' ∈ lspan I := by
    have hdiff : g - E.symm u' ∈ lspan I := hker ((mem_ker_phi (K := K) _).1 (by
      rw [map_sub, phi_symm, hmap, ← hG, sub_self]))
    have := Ideal.sub_mem _ hg hdiff
    rwa [sub_sub_cancel] at this
  have hzR : ∀ x : MvPolynomial (Fin n) ℚ, x = 0 ∨ x ≠ 0 := (hasPres_mvPolynomial n).zeroTest
  refine ⟨a, ha0, ha, fun f hf => ?_⟩
  obtain ⟨m, q, r, hqr, hr⟩ := pseudo_div hzR (g := u') (by rw [hu'd]; exact hdeg) (E f)
  rw [hlc] at hqr
  have hrmap : r.map (iota L (K := K)) = 0 := by
    have hdvd : G ∣ r.map (iota L) := by
      have h1 := congrArg (Polynomial.map (iota L (K := K))) hqr
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, map_C,
        hmap, ← phi_apply] at h1
      have h2 : r.map (iota L) = C (iota L a) ^ m * phi L f - q.map (iota L) * G := by
        rw [h1]; ring
      rw [h2]
      exact dvd_sub (dvd_mul_of_dvd_right hf _) (dvd_mul_left _ _)
    rcases polynomial_eq_zero_or hzK (r.map (iota L)) with h0 | h0
    · exact h0
    exfalso
    have := natDegree_le_of_dvd hdvd h0
    have := natDegree_map_le (f := iota L (K := K)) (p := r)
    omega
  have hr' : E.symm r ∈ lspan I := hker ((mem_ker_phi (K := K) _).1 (by rw [phi_symm, hrmap]))
  refine ⟨m, ?_⟩
  have : jY a ^ m * f = E.symm q * E.symm u' + E.symm r := by
    rw [← map_mul, ← map_add, ← hqr, map_mul, map_pow, finSuccEquiv_symm_C,
      AlgEquiv.symm_apply_apply]
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hg₁) hr'

/-- Elements of the extension of `I` are images of elements of `I` up to a denominator. -/
lemma exists_mem_of_mem_span {y : K[X]} (hy : y ∈ lspan (I.map (phi L (K := K)))) :
    ∃ u ∈ lspan I, ∃ d : MvPolynomial (Fin n) ℚ, d ∉ lspan L ∧ phi L (K := K) u = C (iota L d) * y := by
  have hP : (lspan L).IsPrime := inferInstance
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hy
    exact ⟨f, Ideal.subset_span hf, 1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h),
      by rw [map_one, C_1, one_mul]⟩
  | zero => exact ⟨0, Ideal.zero_mem _, 1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h),
      by rw [map_zero, mul_zero]⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨u₁, hu₁, d₁, hd₁, h₁⟩ := ih₁
    obtain ⟨u₂, hu₂, d₂, hd₂, h₂⟩ := ih₂
    refine ⟨jY d₂ * u₁ + jY d₁ * u₂, Ideal.add_mem _ (Ideal.mul_mem_left _ _ hu₁)
      (Ideal.mul_mem_left _ _ hu₂), d₁ * d₂, fun h => (hP.mem_or_mem h).elim hd₁ hd₂, ?_⟩
    rw [map_add, map_mul, map_mul, phi_jY, phi_jY, h₁, h₂, map_mul, C_mul]; ring
  | smul k y _ ih =>
    obtain ⟨u, hu, d, hd, h⟩ := ih
    obtain ⟨w, e, he, hw⟩ := exists_lift_phi (L := L) (K := K) k
    refine ⟨w * u, Ideal.mul_mem_left _ _ hu, e * d, fun h' => (hP.mem_or_mem h').elim he hd, ?_⟩
    rw [map_mul, hw, h, smul_eq_mul, map_mul, C_mul]; ring

/-- **The step of Perdry's Theorem 4.3** at a prime contraction with factorial `K`. -/
theorem sprime_step (hFF : FactorialField K) [CharZero K]
    (hLI : ∀ h, jY h ∈ lspan I ↔ h ∈ lspan L) : SPrime I := by
  -- the projection instance (otherwise inference goes through `Field.henselian`)
  letI : Nontrivial K := DivisionRing.toNontrivial
  have hP : (lspan L).IsPrime := inferInstance
  have hzK := hFF.zero
  set E := MvPolynomial.finSuccEquiv ℚ n
  obtain ⟨g₀, hg₀d, hg₀m⟩ := exists_gcd_list hzK (I.map (phi L (K := K)))
  obtain ⟨g, hg, d₀, hd₀, hG⟩ := exists_mem_of_mem_span hg₀m
  set G := phi L (K := K) g with hGdef
  have hd₀' : iota L (K := K) d₀ ≠ 0 := fun h => hd₀ ((iota_eq_zero (K := K)).1 h)
  have hCu : IsUnit (C (iota L (K := K) d₀)) := (IsUnit.mk0 _ hd₀').map C
  -- `G` divides the image of every element of `I`
  have hGdvd : ∀ f ∈ lspan I, G ∣ phi L (K := K) f := by
    intro f hf
    have h1 : g₀ ∣ phi L (K := K) f := dvd_of_mem_lspan hg₀d (mem_lspan_map _ hf)
    rw [hG]; exact (hCu.mul_left_dvd).2 h1
  have hker := ker_le I hLI
  have hzS : ∀ x : MvPolynomial (Fin (n + 1)) ℚ, x ∈ lspan I ∨ x ∉ lspan I :=
    (hasPres_mvPolynomial (n + 1)).mem_dec I
  rcases polynomial_eq_zero_or hzK G with hG0 | hG0
  · -- `Iᵉ = 0`: `I = P R[X]`, fraction field `Frac(K[X])`
    have hIker : ∀ f, phi L (K := K) f = 0 ↔ f ∈ lspan I := fun f => ⟨fun h =>
      hker ((mem_ker_phi (K := K) f).1 h), fun h => by
        have := hGdvd f h; rw [hG0] at this; exact zero_dvd_iff.1 this⟩
    let K' := FractionRing K[X]
    let ψ : MvPolynomial (Fin (n + 1)) ℚ →+* K' := (algebraMap K[X] K').comp (phi L (K := K))
    have hinj := IsFractionRing.injective K[X] K'
    refine Or.inr (Or.inr (primeFF_of_hom ψ (fun f => ?_) (fun z => ?_)
      (factorialField_fraction hFF K') (charZero_of_injective_ringHom
        (f := (algebraMap K[X] K').comp Polynomial.C) (hinj.comp Polynomial.C_injective))))
    · rw [RingHom.comp_apply, map_eq_zero_iff _ hinj, hIker]
    · obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) z
      obtain ⟨ux, dx, hdx, hx⟩ := exists_lift_phi (L := L) (K := K) x
      obtain ⟨uy, dy, hdy, hyy⟩ := exists_lift_phi (L := L) (K := K) y
      have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
      have hdx' : iota L (K := K) dx ≠ 0 := fun h => hdx ((iota_eq_zero (K := K)).1 h)
      have hdy' : iota L (K := K) dy ≠ 0 := fun h => hdy ((iota_eq_zero (K := K)).1 h)
      refine ⟨ux * jY dy, uy * jY dx, ?_, ?_⟩
      · simp only [ψ, RingHom.comp_apply, map_mul, phi_jY, hyy]
        refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;>
          rw [Ne, map_eq_zero_iff _ hinj] <;> simpa
      · simp only [ψ, RingHom.comp_apply, map_mul, phi_jY, hx, hyy]
        have h1 : algebraMap K[X] K' (C (iota L dx)) ≠ 0 := by
          rw [Ne, map_eq_zero_iff _ hinj]; simpa
        have h2 : algebraMap K[X] K' (C (iota L dy)) ≠ 0 := by
          rw [Ne, map_eq_zero_iff _ hinj]; simpa
        have h3 : algebraMap K[X] K' y ≠ 0 := by rw [Ne, map_eq_zero_iff _ hinj]; exact hy0
        rw [div_eq_div_iff h3 (mul_ne_zero (mul_ne_zero h2 h3) h1)]
        ring
  -- `G ≠ 0`: positive degree, since `I ∩ R = P`
  have hcoef : ∀ i, G.coeff i = iota L (K := K) ((E g).coeff i) := fun i => by
    rw [hGdef, phi_apply, coeff_map]
  have hdegG : 0 < G.natDegree := by
    rcases Nat.eq_zero_or_pos G.natDegree with h0 | h0
    · exfalso
      have hGC : G = C (G.coeff 0) := eq_C_of_natDegree_eq_zero h0
      have hdiff : g - jY ((E g).coeff 0) ∈ lspan I := hker ((mem_ker_phi (K := K) _).1 (by
        rw [map_sub, phi_jY, ← hcoef 0, ← hGdef, ← hGC, sub_self]))
      have hc0I : jY ((E g).coeff 0) ∈ lspan I := by
        have := Ideal.sub_mem _ hg hdiff; rwa [sub_sub_cancel] at this
      apply hG0
      rw [hGC, hcoef 0, (iota_eq_zero (K := K)).2 ((hLI _).1 hc0I), C_0]
    · exact h0
  obtain ⟨a, ha, -, hsat⟩ := saturation hzK hLI hg hdegG
  have ha' : iota L (K := K) a ≠ 0 := fun h => ha ((iota_eq_zero (K := K)).1 h)
  have hne : ∀ (w : MvPolynomial (Fin (n + 1)) ℚ) (c : K) (H : K[X]), c ≠ 0 →
      phi L (K := K) w = C c * H → H ≠ 0 → H.natDegree < G.natDegree → w ∉ lspan I := by
    intro w c H hc hw hH hlt hwI
    have h1 := hGdvd w hwI
    rw [hw] at h1
    have := natDegree_le_of_dvd h1 (mul_ne_zero (by simpa using hc) hH)
    rw [natDegree_C_mul hc] at this
    omega
  rcases hFF.irreducible_or_split hdegG with hirr | ⟨G₁, G₂, h12, hG₁, hG₂⟩
  swap
  · -- `G` reducible: a split
    obtain ⟨u₁, d₁, hd₁, hu₁⟩ := exists_lift_phi (L := L) (K := K) G₁
    obtain ⟨u₂, d₂, hd₂, hu₂⟩ := exists_lift_phi (L := L) (K := K) G₂
    have hd₁' : iota L (K := K) d₁ ≠ 0 := fun h => hd₁ ((iota_eq_zero (K := K)).1 h)
    have hd₂' : iota L (K := K) d₂ ≠ 0 := fun h => hd₂ ((iota_eq_zero (K := K)).1 h)
    have hG₁0 : G₁ ≠ 0 := fun h => by rw [h, natDegree_zero] at hG₁; exact lt_irrefl 0 hG₁
    have hG₂0 : G₂ ≠ 0 := fun h => by rw [h, natDegree_zero] at hG₂; exact lt_irrefl 0 hG₂
    have hdeg12 := natDegree_mul hG₁0 hG₂0
    rw [← h12] at hdeg12
    have hdvd : G ∣ phi L (K := K) (u₁ * u₂) :=
      ⟨C (iota L d₁) * C (iota L d₂), by rw [map_mul, hu₁, hu₂, h12]; ring⟩
    obtain ⟨m, hm⟩ := hsat _ hdvd
    refine Or.inr (Or.inl ⟨jY a ^ m * u₁, u₂, by rw [mul_assoc]; exact hm, ?_,
      hne u₂ _ G₂ hd₂' hu₂ hG₂0 (by omega)⟩)
    refine hne _ (iota L a ^ m * iota L d₁) G₁ (mul_ne_zero (pow_ne_zero _ ha') hd₁') ?_ hG₁0
      (by omega)
    rw [map_mul, map_pow, phi_jY, hu₁, C_mul, C_pow]; ring
  -- `G` irreducible: the colon test `(I : a) ⊆ I`
  obtain ⟨Cl, hCl⟩ := exists_colon I [jY a]
  have hdecP : ∀ x, x ∉ lspan I ∨ ¬ x ∉ lspan I := fun x =>
    (hzS x).elim (fun h => Or.inr fun h' => h' h) Or.inl
  rcases Multiset.exists_or_forall_not' (Cl : Multiset _) hdecP with ⟨x, hxC, hxI⟩ | hall
  · have hxa : x * jY a ∈ lspan I :=
      (hCl x).1 (Ideal.subset_span (Multiset.mem_coe.1 hxC)) (jY a) (List.mem_singleton_self _)
    exact Or.inr (Or.inl ⟨x, jY a, hxa, hxI, fun h => ha ((hLI a).1 h)⟩)
  have hle : lspan Cl ≤ lspan I := by
    rw [lspan, Ideal.span_le]
    intro y hy
    rcases hzS y with h | h
    · exact h
    · exact absurd h (hall y (Multiset.mem_coe.2 hy))
  have hClI : ∀ x, x * jY a ∈ lspan I → x ∈ lspan I := fun x hx =>
    hle ((hCl x).2 fun g' hg' => by rw [List.mem_singleton.1 hg']; exact hx)
  have hsatI : ∀ (m : ℕ) (f : MvPolynomial (Fin (n + 1)) ℚ), jY a ^ m * f ∈ lspan I →
      f ∈ lspan I := by
    intro m
    induction m with
    | zero => intro f hf; simpa using hf
    | succ m ih =>
      intro f hf
      apply hClI
      apply ih
      have : jY a ^ m * (f * jY a) = jY a ^ (m + 1) * f := by ring
      rw [this]; exact hf
  haveI : Fact (Irreducible G) := ⟨hirr⟩
  letI : Nontrivial (AdjoinRoot G) := DivisionRing.toNontrivial
  let ψ : MvPolynomial (Fin (n + 1)) ℚ →+* AdjoinRoot G := (AdjoinRoot.mk G).comp (phi L (K := K))
  refine Or.inr (Or.inr (primeFF_of_hom ψ (fun f => ?_) (fun z => ?_)
    (factorialField_adjoin hFF)
    (charZero_of_injective_algebraMap (algebraMap K (AdjoinRoot G)).injective)))
  · simp only [ψ, RingHom.comp_apply, AdjoinRoot.mk_eq_zero]
    exact ⟨fun h => by obtain ⟨m, hm⟩ := hsat f h; exact hsatI m f hm, hGdvd f⟩
  · obtain ⟨h, rfl⟩ := AdjoinRoot.mk_surjective z
    obtain ⟨u, d, hd, hu⟩ := exists_lift_phi (L := L) (K := K) h
    have hd' : iota L (K := K) d ≠ 0 := fun h' => hd ((iota_eq_zero (K := K)).1 h')
    have hψd : ψ (jY d) = AdjoinRoot.of G (iota L d) := by
      simp only [ψ, RingHom.comp_apply, phi_jY, AdjoinRoot.mk_C]
    have hne' : AdjoinRoot.of G (iota L (K := K) d) ≠ 0 :=
      (map_ne_zero_iff _ (AdjoinRoot.of G).injective).2 hd'
    refine ⟨u, jY d, by rw [hψd]; exact hne', ?_⟩
    rw [hψd, eq_div_iff hne']
    simp only [ψ, RingHom.comp_apply, hu, map_mul, AdjoinRoot.mk_C]
    ring

end Step

section Induction

/-- The base case `ℚ[∅] ≅ ℚ`. -/
theorem fln_zero : FLN 0 := by
  intro I
  let e := MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)
  have hz : ∀ f : MvPolynomial (Fin 0) ℚ, f = 0 ∨ f ≠ 0 := (hasPres_mvPolynomial 0).zeroTest
  have hdec : ∀ f : MvPolynomial (Fin 0) ℚ, f ≠ 0 ∨ ¬ f ≠ 0 := fun f =>
    (hz f).elim (fun h => Or.inr fun h' => h' h) Or.inl
  rcases Multiset.exists_or_forall_not' (I : Multiset _) hdec with ⟨f, hfI, hf⟩ | hall
  · left
    have hef : e f ≠ 0 := fun h => hf (e.injective (by rw [h, map_zero]))
    have : f * e.symm (e f)⁻¹ = 1 := e.injective (by
      rw [map_mul, AlgEquiv.apply_symm_apply, mul_inv_cancel₀ hef, map_one])
    rw [← this]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Multiset.mem_coe.1 hfI))
  have hbot : ∀ f ∈ lspan I, f = 0 := by
    have : lspan I ≤ ⊥ := by
      rw [lspan, Ideal.span_le]
      intro x hx
      rcases hz x with h | h
      · exact h
      · exact absurd h (hall x (Multiset.mem_coe.2 hx))
    exact fun f hf => (Ideal.mem_bot.1 (this hf))
  refine Or.inr (Or.inr (primeFF_of_hom (e : MvPolynomial (Fin 0) ℚ →+* ℚ) (fun f => ?_)
    (fun z => ⟨e.symm z, 1, by simp, by simp⟩) factorialField_rat inferInstance))
  constructor
  · intro h
    have : f = 0 := e.injective (by rw [map_zero]; exact h)
    rw [this]; exact Ideal.zero_mem _
  · intro h
    rw [hbot f h]; exact map_zero _

/-- The step `ℚ[Y₁, …, Yₙ] ↝ ℚ[X, Y₁, …, Yₙ]`. -/
theorem fln_succ {n : ℕ} (h : FLN n) : FLN (n + 1) := by
  intro I
  obtain ⟨L, hLI⟩ := exists_elim0 I
  rcases h L with h1 | ⟨a, b, hab, ha, hb⟩ | ⟨hP, K, _, _, hK, hFF, hchar⟩
  · exact Or.inl (by simpa using (hLI 1).2 h1)
  · exact Or.inr (Or.inl ⟨jY a, jY b, by rw [← map_mul]; exact (hLI _).2 hab,
      fun h => ha ((hLI a).1 h), fun h => hb ((hLI b).1 h)⟩)
  · haveI := hP
    haveI := hchar
    exact sprime_step hFF hLI

/-- **Perdry's Theorem 4.3** for `ℚ[Y₁, …, Yₙ]`: the strong primality test, with factorial residue
fields. -/
theorem fln : ∀ n, FLN n
  | 0 => fln_zero
  | n + 1 => fln_succ (fln n)

end Induction

end BezoutCounterexample.Constructive
