import BezoutCounterexample.Constructive.FactorialField

/-!
# A primitive shift, constructively (the `∂_T` trick)

Replaces the trusted primitive `exists_primitive_shift` of `FactorialAlg` (plan:
`docs/pending/primitive-shift-plan.md`). Part 1 (milestone 2): the algebra over a field `F` with a
zero test and characteristic `0`.

* `bezout_field`: extended Euclid in `F[X]` (moved here from `FactorialAlg`);
* `dvd_of_dvd_pow`: for `f` coprime to `f'`, `f ∣ gⁿ → f ∣ g` (`gcd(f, g)` and `e² ∣ f → e ∣ f'`);
* `pow_dvd_radical`: `P ∣ (P / gcd(P, P'))^(2 deg P + 1)` (strong induction on `deg P`, char `0`);
* `polynomial_pow_eq_zero`: a polynomial ring over a reduced ring is reduced (trailing coefficients);
* `eq_zero_of_map_mul_eq_zero`: `B[T]` is torsion-free over `K[T]` for a `K`-algebra `B`.
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open Polynomial

-- Nontriviality of fields by projection (otherwise inference goes through `Field.henselian`).
attribute [local instance 2000] DivisionRing.toNontrivial

section Euclid

variable {F : Type*} [Field F] (hz : ∀ x : F, x = 0 ∨ x ≠ 0)
include hz

/-- **Extended Euclid** in `F[X]`, constructively (division with remainder and the zero test). -/
theorem bezout_field (f g : F[X]) : ∃ h u v : F[X], IsGcd h f g ∧ u * f + v * g = h := by
  suffices H : ∀ n, ∀ f g : F[X], g ≠ 0 → g.natDegree = n →
      ∃ h u v : F[X], IsGcd h f g ∧ u * f + v * g = h by
    rcases polynomial_eq_zero_or hz g with rfl | hg
    · exact ⟨f, 1, 0, isGcd_zero_right f, by ring⟩
    · exact H _ f g hg rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f g hg hn
  rcases polynomial_eq_zero_or hz (f % g) with hr | hr
  · have hgf : g ∣ f := (EuclideanDomain.mod_eq_zero).1 hr
    exact ⟨g, 0, 1, ⟨hgf, dvd_rfl, fun _ _ h => h⟩, by ring⟩
  have hlt : (f % g).natDegree < g.natDegree :=
    natDegree_lt_natDegree hr (EuclideanDomain.mod_lt f hg)
  obtain ⟨h, u, v, hh, huv⟩ := ih _ (hn ▸ hlt) g (f % g) hr rfl
  have hf : f = g * (f / g) + f % g := (EuclideanDomain.div_add_mod f g).symm
  refine ⟨h, v, u - v * (f / g), ⟨?_, hh.1, fun d hdf hdg => hh.2.2 d hdg ?_⟩, ?_⟩
  · rw [hf]; exact dvd_add (dvd_mul_of_dvd_left hh.1 _) hh.2.1
  · have : f % g = f - g * (f / g) := by linear_combination -hf
    rw [this]; exact dvd_sub hdf (dvd_mul_of_dvd_left hdg _)
  · linear_combination v * hf + huv

omit hz in
/-- A unit gcd gives coprimality. -/
lemma isCoprime_of_isGcd_unit {a b G u v : F[X]} (huv : u * a + v * b = G) (hG : IsUnit G) :
    IsCoprime a b := by
  obtain ⟨w, hw⟩ := isUnit_iff_dvd_one.1 hG
  exact ⟨w * u, w * v, by linear_combination w * huv - hw⟩

omit hz in
/-- The cofactors of a nonzero Bézout gcd are coprime. -/
lemma isCoprime_cofactors {a b d a₁ b₁ u v : F[X]} (hd : d ≠ 0) (ha : a = d * a₁)
    (hb : b = d * b₁) (huv : u * a + v * b = d) : IsCoprime a₁ b₁ :=
  ⟨u, v, mul_left_cancel₀ hd (by rw [mul_one]; linear_combination huv - u * ha - v * hb)⟩

/-- **`f ∣ g² → f ∣ g`** for `f` coprime to its derivative. -/
theorem dvd_of_dvd_sq {f g : F[X]} (hf : IsCoprime f (derivative f)) (h : f ∣ g ^ 2) : f ∣ g := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [derivative_zero] at hf
    exact not_isCoprime_zero_zero hf
  obtain ⟨d, u, v, hd, huv⟩ := bezout_field hz f g
  have hd0 : d ≠ 0 := fun h0 => hf0 (zero_dvd_iff.1 (h0 ▸ hd.1))
  obtain ⟨e, he⟩ := hd.1
  obtain ⟨g₁, hg₁⟩ := hd.2.1
  have hcop : IsCoprime e g₁ := isCoprime_cofactors hd0 he hg₁ huv
  -- `e ∣ d`
  have hed : e ∣ d := by
    obtain ⟨k, hk⟩ := h
    have : d * (e * k) = d * (d * g₁ ^ 2) := by
      rw [← mul_assoc, ← he, ← hk, hg₁]; ring
    have h2 : e ∣ d * g₁ ^ 2 := ⟨k, (mul_left_cancel₀ hd0 this).symm⟩
    exact (hcop.pow_right (n := 2)).dvd_of_dvd_mul_right h2
  -- `e ∣ f'`, so `e` is a unit
  obtain ⟨t, ht⟩ := hed
  have hf2 : f = e ^ 2 * t := by rw [he, ht]; ring
  have hef' : e ∣ derivative f := by
    rw [hf2, derivative_mul, derivative_sq]
    exact ⟨C 2 * derivative e * t + e * derivative t, by ring⟩
  have heu : IsUnit e := hf.isUnit_of_dvd' ⟨d, by rw [he]; ring⟩ hef'
  obtain ⟨w, hw⟩ := isUnit_iff_dvd_one.1 heu
  exact ⟨w * g₁, by rw [he, hg₁]; linear_combination (d * g₁) * hw⟩

/-- **`f ∣ gⁿ → f ∣ g`** for `f` coprime to its derivative. -/
theorem dvd_of_dvd_pow {f g : F[X]} (hf : IsCoprime f (derivative f)) :
    ∀ n, f ∣ g ^ n → f ∣ g := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h
  rcases n with _ | _ | n
  · exact (isUnit_of_dvd_one (by simpa using h)).dvd
  · simpa using h
  · have h1 := Nat.div_add_mod (n + 3) 2
    have h2 := Nat.mod_lt (n + 3) two_pos
    have hlt : (n + 3) / 2 < n + 2 := (Nat.div_lt_iff_lt_mul two_pos).2 (by
      generalize (n + 3) / 2 = q at *; generalize (n + 3) % 2 = r at *; omega)
    have hle : n + 2 ≤ (n + 3) / 2 * 2 := by
      generalize (n + 3) / 2 = q at *; generalize (n + 3) % 2 = r at *; omega
    have h2 : f ∣ (g ^ ((n + 3) / 2)) ^ 2 :=
      h.trans (by rw [← pow_mul]; exact pow_dvd_pow g hle)
    exact ih ((n + 3) / 2) hlt (dvd_of_dvd_sq hz hf h2)

variable [CharZero F]

/-- **The radical divides a power**: `P ∣ (P / gcd(P, P'))^(2 deg P + 1)`. -/
theorem pow_dvd_radical : ∀ (P g r : F[X]), P ≠ 0 → IsGcd g P (derivative P) → P = r * g →
    P ∣ r ^ (2 * P.natDegree + 1) := by
  intro P
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
  intro g r hP hg hPrg
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    exact (isUnit_of_natDegree_eq_zero_field hP hn).dvd
  have hP' : derivative P ≠ 0 := fun h => by
    have := derivative_eq_zero.1 h; omega
  have hg0 : g ≠ 0 := fun h => hP' (zero_dvd_iff.1 (h ▸ hg.2.1))
  have hgdeg : g.natDegree < n := by
    have := natDegree_le_of_dvd hg.2.1 hP'
    have := natDegree_derivative_lt (p := P) (by omega)
    omega
  -- `g ∣ r g'`
  have hgrg : g ∣ r * derivative g := by
    have : r * derivative g = derivative P - derivative r * g := by
      rw [hPrg, derivative_mul]; ring
    rw [this]; exact dvd_sub hg.2.1 (dvd_mul_left g _)
  -- `e = gcd(g, g')`, `g = s e`, `g' = s₁ e`
  obtain ⟨e, u, v, he, huv⟩ := bezout_field hz g (derivative g)
  have he0 : e ≠ 0 := fun h => hg0 (zero_dvd_iff.1 (h ▸ he.1))
  obtain ⟨s, hs⟩ := he.1
  obtain ⟨s₁, hs₁⟩ := he.2.1
  have hcop : IsCoprime s s₁ := isCoprime_cofactors he0 hs hs₁ huv
  -- `s ∣ r`
  have hsr : s ∣ r := by
    obtain ⟨k, hk⟩ := hgrg
    have : e * (s * k) = e * (r * s₁) := by
      linear_combination -hk + r * hs₁ - k * hs
    exact hcop.dvd_of_dvd_mul_right ⟨k, (mul_left_cancel₀ he0 this).symm⟩
  -- induction on `g`
  have hIH := ih g.natDegree (hn ▸ hgdeg) g rfl e s hg0 he (hs.trans (mul_comm _ _))
  have he_r : e ∣ r ^ (2 * g.natDegree + 1) :=
    (dvd_trans ⟨s, hs⟩ hIH).trans (pow_dvd_pow_of_dvd hsr _)
  have hP_dvd : P ∣ r ^ (2 * g.natDegree + 3) := by
    rw [hPrg]
    calc r * g = r * (s * e) := by rw [hs, mul_comm e s]
      _ ∣ r * (r * r ^ (2 * g.natDegree + 1)) := mul_dvd_mul_left r (mul_dvd_mul hsr he_r)
      _ = r ^ (2 * g.natDegree + 3) := by ring
  exact hP_dvd.trans (pow_dvd_pow r (by omega))

end Euclid

section Reduced

variable {R : Type*} [CommRing R]

/-- **A polynomial ring over a reduced ring is reduced** (the trailing coefficient of `Pⁿ`). -/
theorem polynomial_pow_eq_zero (hR : ∀ (x : R) (n : ℕ), x ^ n = 0 → x = 0) (P : R[X]) (n : ℕ)
    (h : P ^ n = 0) : P = 0 := by
  set t := P.natTrailingDegree with ht
  obtain ⟨Q, hQ⟩ : X ^ t ∣ P :=
    X_pow_dvd_iff.2 fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd
  have hQ0 : Q.coeff 0 = P.trailingCoeff := by
    rw [trailingCoeff, ← ht]
    nth_rewrite 1 [hQ]
    rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
  have hQn : Q ^ n = 0 := by
    have : X ^ (t * n) * Q ^ n = 0 := by
      rw [pow_mul, ← mul_pow, ← hQ, h]
    exact ((monic_X_pow _).mul_right_eq_zero_iff).1 this
  have hc : Q.coeff 0 ^ n = 0 := by
    rw [coeff_zero_eq_eval_zero, ← eval_pow, hQn, eval_zero]
  have := hR _ n hc
  rw [hQ0] at this
  exact trailingCoeff_eq_zero.1 this

/-- **`B[T]` is torsion-free over `K[T]`** for a `K`-algebra `B` (`K` a field, `B` nontrivial). -/
theorem eq_zero_of_map_mul_eq_zero {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    {s : K[X]} (hs : s ≠ 0) {b : B[X]} (h : s.map (algebraMap K B) * b = 0) : b = 0 := by
  have hm : (C s.leadingCoeff⁻¹ * s).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one
    (inv_mul_cancel₀ (leadingCoeff_ne_zero.2 hs))
  have hm' := hm.map (algebraMap K B)
  refine (hm'.mul_right_eq_zero_iff).1 ?_
  rw [Polynomial.map_mul, map_C, mul_assoc, h, mul_zero]

end Reduced

section Descent

/-! ## The separable descent over `K[T]` -/

variable {K : Type*} [Field K] [CharZero K] (hz : ∀ x : K, x = 0 ∨ x ≠ 0)
  {E : Type*} [CommRing E] (φ : K[X] →+* E) (θ : E)
  (hred : ∀ (e : E) (n : ℕ), e ^ n = 0 → e = 0)
  (htf : ∀ s : K[X], s ≠ 0 → ∀ e : E, φ s * e = 0 → e = 0)


omit [CharZero K] in
lemma map_ι_injective : Function.Injective (Polynomial.map (R := K[X]) (algebraMap K[X] (FractionRing K[X]))) :=
  map_injective _ (IsFractionRing.injective K[X] (FractionRing K[X]))

include hz hred htf in
/-- **A separable annihilator**: from any nonzero `Q₀ ∈ K[T][S]` with `Q₀(θ) = 0`, a nonzero `Q` with
`Q(θ) = 0` and `u Q + v ∂_S Q = d ≠ 0` in `K[T]`. -/
theorem exists_separable_annihilator : ∀ (Q₀ : K[X][X]), Q₀ ≠ 0 → eval₂ φ θ Q₀ = 0 →
    ∃ (Q u v : K[X][X]) (d : K[X]), Q ≠ 0 ∧ eval₂ φ θ Q = 0 ∧ d ≠ 0 ∧
      u * Q + v * derivative Q = C d := by
  letI : Nontrivial K := DivisionRing.toNontrivial
  letI : Nontrivial (FractionRing K[X]) := DivisionRing.toNontrivial
  have hzF : ∀ x : (FractionRing K[X]), x = 0 ∨ x ≠ 0 := hzero_fraction (FractionRing K[X]) (polynomial_eq_zero_or hz)
  have : CharZero (FractionRing K[X]) := charZero_of_injective_algebraMap (IsFractionRing.injective K[X] (FractionRing K[X]))
  intro Q₀
  induction hn : Q₀.natDegree using Nat.strong_induction_on generalizing Q₀ with
  | _ n ih =>
  intro hQ0 hQθ
  set Qf := Q₀.map (algebraMap K[X] (FractionRing K[X])) with hQf
  have hQf0 : Qf ≠ 0 := fun h => hQ0 (map_ι_injective (by rw [← hQf, h, Polynomial.map_zero]))
  have hdegf : Qf.natDegree = n := by
    rw [hQf, natDegree_map_eq_of_injective (IsFractionRing.injective K[X] (FractionRing K[X])), hn]
  obtain ⟨g, u, v, hg, huv⟩ := bezout_field hzF Qf (derivative Qf)
  have hg0 : g ≠ 0 := fun h => hQf0 (zero_dvd_iff.1 (h ▸ hg.1))
  rcases Nat.eq_zero_or_pos g.natDegree with hg1 | hg1
  · -- a unit gcd: Bézout over `F`, cleared
    obtain ⟨c, hc⟩ : ∃ c, g = C c := ⟨g.coeff 0, eq_C_of_natDegree_eq_zero hg1⟩
    have hc0 : c ≠ 0 := fun h => hg0 (by rw [hc, h, C_0])
    obtain ⟨s₁, hs₁, u₁, hu₁⟩ := exists_clear (A := K[X]) (FractionRing K[X]) (C c⁻¹ * u)
    obtain ⟨s₂, hs₂, v₁, hv₁⟩ := exists_clear (A := K[X]) (FractionRing K[X]) (C c⁻¹ * v)
    refine ⟨Q₀, C s₂ * u₁, C s₁ * v₁, s₁ * s₂, hQ0, hQθ, mul_ne_zero hs₁ hs₂, ?_⟩
    apply map_ι_injective
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hu₁, hv₁, derivative_map, ← hQf,
      map_mul]
    have : C c⁻¹ * u * Qf + C c⁻¹ * v * derivative Qf = 1 := by
      rw [mul_assoc, mul_assoc, ← mul_add, huv, hc, ← C_mul, inv_mul_cancel₀ hc0, C_1]
    rw [← derivative_map, ← hQf]
    linear_combination (C ((algebraMap K[X] (FractionRing K[X])) s₁) * C ((algebraMap K[X] (FractionRing K[X])) s₂)) * this
  · -- a nonconstant gcd: pass to the radical
    obtain ⟨r, hr⟩ := hg.1
    have hr0 : r ≠ 0 := fun h => hQf0 (by rw [hr, h, mul_zero])
    have hdvd := pow_dvd_radical hzF Qf g r hQf0 hg (by rw [hr, mul_comm])
    obtain ⟨w, hw⟩ := hdvd
    obtain ⟨s, hs, r₁, hr₁⟩ := exists_clear (A := K[X]) (FractionRing K[X]) r
    obtain ⟨s', hs', w₁, hw₁⟩ := exists_clear (A := K[X]) (FractionRing K[X]) w
    set k := 2 * Qf.natDegree + 1
    -- `s' r₁^k = s^k Q₀ w₁`
    have hrel : C s' * r₁ ^ k = C (s ^ k) * Q₀ * w₁ := by
      apply map_ι_injective
      simp only [Polynomial.map_mul, Polynomial.map_pow, map_C, hr₁, hw₁, ← hQf, map_pow]
      rw [mul_pow, hw, ← C_pow]; ring
    have hr₁θ : eval₂ φ θ r₁ = 0 := by
      have h1 : φ s' * eval₂ φ θ r₁ ^ k = 0 := by
        have := congrArg (eval₂ φ θ) hrel
        simp only [eval₂_mul, eval₂_C, eval₂_pow, hQθ, mul_zero, zero_mul] at this
        exact this
      exact hred _ k (htf s' hs' _ h1)
    have hr₁0 : r₁ ≠ 0 := fun h => by
      have := congrArg (Polynomial.map (algebraMap K[X] (FractionRing K[X]))) h
      rw [hr₁, Polynomial.map_zero] at this
      exact hr0 ((mul_eq_zero.1 this).resolve_left
        (C_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (FractionRing K[X]))).2 hs)))
    have hdeg₁ : r₁.natDegree < n := by
      have h1 : r₁.natDegree = r.natDegree := by
        rw [← natDegree_map_eq_of_injective (IsFractionRing.injective K[X] (FractionRing K[X])) r₁, hr₁,
          natDegree_C_mul ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (FractionRing K[X]))).2 hs)]
      have h2 : Qf.natDegree = g.natDegree + r.natDegree := by rw [hr, natDegree_mul hg0 hr0]
      omega
    exact ih _ hdeg₁ r₁ rfl hr₁0 hr₁θ

end Descent

section DerivT

/-! ## The `∂_T` identity -/

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]

/-- Coefficientwise `∂_T` of `Q ∈ K[T][S]`. -/
def dT (Q : K[X][X]) : K[X][X] := Q.sum fun n a => monomial n (derivative a)

lemma dT_add (P Q : K[X][X]) : dT (P + Q) = dT P + dT Q :=
  sum_add_index _ _ _ (fun n => by simp) (fun n a b => by simp [derivative_add])

lemma dT_monomial (n : ℕ) (a : K[X]) : dT (monomial n a) = monomial n (derivative a) :=
  sum_monomial_index _ _ (by simp)

/-- **The `∂_T` identity**: `∂_T (Q(θ)) = (∂_S Q)(θ) · ∂_T θ + (∂_T Q)(θ)` in `B[T]`. -/
theorem derivative_eval₂ (θ : B[X]) (Q : K[X][X]) :
    derivative (eval₂ (mapRingHom (algebraMap K B)) θ Q) =
      eval₂ (mapRingHom (algebraMap K B)) θ (derivative Q) * derivative θ +
        eval₂ (mapRingHom (algebraMap K B)) θ (dT Q) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [eval₂_add, derivative_add, hP, hQ, derivative_add, eval₂_add, dT_add, eval₂_add]; ring
  | monomial n a =>
    rw [eval₂_monomial, derivative_monomial, eval₂_monomial, dT_monomial, eval₂_monomial,
      derivative_mul, derivative_pow, coe_mapRingHom, derivative_map, Polynomial.map_mul,
      Polynomial.map_natCast, C_eq_natCast]
    ring

end DerivT

section Shift

/-! ## The primitive shift -/

variable {K : Type*} [Field K] {p : K[X]} [Fact (Irreducible p)]

/-- The zero test of `K[Y] ⧸ (p)`. -/
lemma zeroTest_adjoin (hK : FactorialField K) (x : AdjoinRoot p) : x = 0 ∨ x ≠ 0 := by
  obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective x
  rcases hK.dvdDec p a with h | h
  · exact Or.inl (AdjoinRoot.mk_eq_zero.2 h)
  · exact Or.inr fun h' => h (AdjoinRoot.mk_eq_zero.1 h')

/-- `θ_c = X + c α` in `B = L[X] ⧸ (f)`. -/
def theta (f : (AdjoinRoot p)[X]) (c : K) : AdjoinRoot f :=
  AdjoinRoot.root f + AdjoinRoot.of f (algebraMap K (AdjoinRoot p) c * AdjoinRoot.root p)

/-- A nonzero polynomial over a field of characteristic `0` is nonzero at one of `0, …, deg`. -/
lemma exists_nat_eval_ne_zero [CharZero K] (hz : ∀ x : K, x = 0 ∨ x ≠ 0) {d : K[X]} (hd : d ≠ 0) :
    ∃ c : ℕ, d.eval (c : K) ≠ 0 := by
  rcases Finset.exists_or_forall_not' (Finset.range (d.natDegree + 1))
      (P := fun c : ℕ => d.eval (c : K) ≠ 0)
      (fun c => (hz (d.eval (c : K))).symm.imp id fun h h' => h' h) with ⟨c, -, hc⟩ | hall
  · exact ⟨c, hc⟩
  · exfalso; apply hd
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero d
      (f := fun i : Fin (d.natDegree + 1) => ((i : ℕ) : K))
      (fun i j h => Fin.ext (Nat.cast_injective h)) (fun i => ?_) (by simp)
    exact (hz _).resolve_right (hall i (Finset.mem_range.2 i.2))

/-- **A primitive shift** (constructive replacement of the former trusted primitive): for `f`
coprime to `f'`, some `θ_c = X + cα` (`c ∈ ℕ`) generates `B = L[X] ⧸ (f)` over `K` and is annihilated
by a nonzero polynomial. -/
theorem exists_primitive_shift' [CharZero K] (hK : FactorialField K) {f : (AdjoinRoot p)[X]}
    (hf : IsCoprime f (derivative f)) (hdeg : 0 < f.natDegree) :
    ∃ c : ℕ, (∃ μ : K[X], μ ≠ 0 ∧ aeval (theta f (c : K)) μ = 0) ∧
      ∀ b : AdjoinRoot f, ∃ q : K[X], aeval (theta f (c : K)) q = b := by
  have hzL := zeroTest_adjoin (p := p) hK
  have hp : Irreducible p := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  have hf0 : f ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; exact lt_irrefl 0 hdeg
  let pbL := AdjoinRoot.powerBasis hp0
  let pbB := AdjoinRoot.powerBasis hf0
  have : Module.Finite K (AdjoinRoot p) := pbL.finite
  have : Module.Finite (AdjoinRoot p) (AdjoinRoot f) := pbB.finite
  have : Module.Finite K (AdjoinRoot f) := Module.Finite.trans (AdjoinRoot p) (AdjoinRoot f)
  have hint : ∀ b : AdjoinRoot f, IsIntegral K b := fun b => Algebra.IsIntegral.isIntegral b
  -- reducedness of `B` and `B[T]`
  have hredB : ∀ (b : AdjoinRoot f) (n : ℕ), b ^ n = 0 → b = 0 := by
    intro b n hb
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective b
    rw [← map_pow, AdjoinRoot.mk_eq_zero] at hb
    exact AdjoinRoot.mk_eq_zero.2 (dvd_of_dvd_pow hzL hf n hb)
  have hredE := polynomial_pow_eq_zero hredB
  set φ : K[X] →+* (AdjoinRoot f)[X] := mapRingHom (algebraMap K (AdjoinRoot f)) with hφ
  have htf : ∀ s : K[X], s ≠ 0 → ∀ e : (AdjoinRoot f)[X], φ s * e = 0 → e = 0 :=
    fun s hs e h => eq_zero_of_map_mul_eq_zero hs h
  set αB : AdjoinRoot f := AdjoinRoot.of f (AdjoinRoot.root p) with hαB
  set xB : AdjoinRoot f := AdjoinRoot.root f with hxB
  set θ : (AdjoinRoot f)[X] := C xB + X * C αB with hθ
  -- a first annihilator: `θ` is integral over `K[T]`
  have hCint : ∀ b : AdjoinRoot f, ∃ m : K[X][X], m.Monic ∧ eval₂ φ (C b) m = 0 := by
    intro b
    obtain ⟨m, hm, hmb⟩ := hint b
    refine ⟨m.map C, hm.map C, ?_⟩
    rw [eval₂_map]
    have : φ.comp C = C.comp (algebraMap K (AdjoinRoot f)) := by
      ext a; simp [φ]
    rw [this, ← hom_eval₂, hmb, map_zero]
  letI : Algebra K[X] (AdjoinRoot f)[X] := φ.toAlgebra
  have hIC : ∀ b : AdjoinRoot f, IsIntegral K[X] (C b) := fun b => by
    obtain ⟨m, hm, h⟩ := hCint b; exact ⟨m, hm, h⟩
  have hIX : IsIntegral K[X] (X : (AdjoinRoot f)[X]) :=
    ⟨X - C X, monic_X_sub_C _, by
      show eval₂ φ X (X - C X) = 0
      simp [φ]⟩
  obtain ⟨Q₀, hQ₀m, hQ₀⟩ := (hIC xB).add (hIX.mul (hIC αB))
  obtain ⟨Q, u, v, d, -, hQθ, hd, huv⟩ :=
    exists_separable_annihilator hK.zero φ θ hredE htf Q₀ hQ₀m.ne_zero hQ₀
  -- the `∂_T` identity
  have hdθ : derivative θ = C αB := by
    simp [θ, derivative_mul]
  have hder := derivative_eval₂ θ Q
  rw [hQθ, derivative_zero, hdθ] at hder
  have hev := congrArg (eval₂ φ θ) huv
  simp only [eval₂_add, eval₂_mul, eval₂_C, hQθ, mul_zero, zero_add] at hev
  set Pα : K[X][X] := -(v * dT Q) with hPα
  have hPαθ : eval₂ φ θ Pα = φ d * C αB := by
    rw [hPα, eval₂_neg, eval₂_mul, ← hev]
    linear_combination (eval₂ φ θ v) * hder
  set Px : K[X][X] := C d * X - C X * Pα with hPx
  have hPxθ : eval₂ φ θ Px = φ d * C xB := by
    rw [hPx, eval₂_sub, eval₂_mul, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, hPαθ, hθ]
    simp only [φ, coe_mapRingHom, map_X]; ring
  -- specialisation at `c` with `d(c) ≠ 0`
  obtain ⟨c, hc⟩ := exists_nat_eval_ne_zero hK.zero hd
  set θc := theta f (c : K) with hθc
  set ev : (AdjoinRoot f)[X] →+* AdjoinRoot f := evalRingHom (algebraMap K (AdjoinRoot f) (c : K))
  have hevφ : ev.comp φ = (algebraMap K (AdjoinRoot f)).comp (evalRingHom (c : K)) := by
    ext a
    · simp [ev, φ]
    · simp [ev, φ]
  have hevθ : ev θ = θc := by
    simp only [ev, hθ, hθc, theta, coe_evalRingHom, eval_add, eval_C, eval_mul, eval_X, map_mul]
    simp only [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, hxB, hαB]
  have hkey : ∀ P : K[X][X], ev (eval₂ φ θ P) = aeval θc (P.map (evalRingHom (c : K))) := by
    intro P
    rw [hom_eval₂, hevφ, hevθ, aeval_def, eval₂_map]
  have hdc : ev (φ d) = algebraMap K (AdjoinRoot f) (d.eval (c : K)) := by
    have := congrArg (fun g : K[X] →+* AdjoinRoot f => g d) hevφ
    simpa using this
  have hmem : ∀ y : AdjoinRoot f, ∀ P : K[X][X], eval₂ φ θ P = φ d * C y →
      ∃ q : K[X], aeval θc q = y := by
    intro y P hP
    refine ⟨C (d.eval (c : K))⁻¹ * P.map (evalRingHom (c : K)), ?_⟩
    rw [map_mul, aeval_C, ← hkey, hP, map_mul, hdc]
    simp only [ev, coe_evalRingHom, eval_C]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  obtain ⟨qα, hqα⟩ := hmem αB Pα hPαθ
  obtain ⟨qx, hqx⟩ := hmem xB Px hPxθ
  refine ⟨c, ?_, fun b => ?_⟩
  · obtain ⟨μ, hμ, hμθ⟩ := hint θc
    exact ⟨μ, hμ.ne_zero, hμθ⟩
  · obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective b
    induction g using Polynomial.induction_on with
    | C l =>
      obtain ⟨h, rfl⟩ := AdjoinRoot.mk_surjective l
      refine ⟨h.comp qα, ?_⟩
      rw [aeval_comp, hqα, AdjoinRoot.mk_C, ← AdjoinRoot.aeval_eq h, hαB]
      rw [← AdjoinRoot.algebraMap_eq]
      exact (aeval_algHom_apply (IsScalarTower.toAlgHom K (AdjoinRoot p) (AdjoinRoot f))
        (AdjoinRoot.root p) h)
    | add g₁ g₂ h₁ h₂ =>
      obtain ⟨q₁, hq₁⟩ := h₁
      obtain ⟨q₂, hq₂⟩ := h₂
      exact ⟨q₁ + q₂, by rw [map_add, hq₁, hq₂, map_add]⟩
    | monomial n l h =>
      obtain ⟨q, hq⟩ := h
      exact ⟨q * qx, by
        rw [map_mul, hq, hqx, hxB, ← AdjoinRoot.mk_X, ← map_mul]; congr 1; ring⟩

end Shift

end BezoutCounterexample.Constructive
