import BezoutCounterexample.Constructive.DynPoly
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Jouanolou rings over an ideal that is prime up to `Q` (D5; `docs/d5-plan.md`, step 3)

Dynamical form of `Jou.isPrime_map` (`𝔞 J_B(c)` is prime when `𝔞` is prime and `c_l ∉ 𝔞`), the input
of `torsor_s_prime`. Here `𝔞` has decidable membership and is prime up to `Q` (`hpr`); in the D5 use
`𝔞 = (s)` in the Rees algebra and `Q = RadSplit P` (`span_s_dyn_split`). The index is `l = 0`.

Everything is stated in `B[σ₀, …, σ_r]` with `K = 𝔞[σ] + (q_c)`, `q_c = Σ cᵢ σᵢ - 1` (`relC`), so
that `u ∈ 𝔞 J_B(c)` reads `p ∈ K` for a lift `p`. No localization:

* `relC_nzd`: `q_c` is a non-zero-divisor over any ring (constant coefficient `-1`, a unit in the
  power series ring), as `Jou.rel_nzd`.
* `torsion_dyn` (`c_0`-torsion-freeness of `J/𝔞J`): `b ∉ 𝔞`, `b p ∈ K` give `p ∈ K` or `Q`. Reduce
  `b p = a + w q_c` modulo `𝔞 + (b)`: `q_c` is a non-zero-divisor, so `w ∈ (𝔞, b)[σ]`, and
  `polyIn_cancel` cancels `b`.
* `elim_dyn` (`J/𝔞J ↪ (B/𝔞)[1/c_0][σ_{>0}]`): a `σ_0`-free `h ∈ K` lies in `𝔞[σ]`, or `Q`. Write
  `h = a + w q_c`, strip `w = w₁ + w₂`; in lex order (`σ_0` most significant) the coefficient of
  `w₁ q_c` at `deg w₁ + e₀` is `lc(w₁) c_0`, and it lies in `𝔞` since `h` has no `σ_0`.
* `pseudo0`: pseudo-division by `q_c` eliminating `σ_0` (as `Jou.exists_pseudo`).
* `jou_dyn`: `p q ∈ K` gives `p ∈ K`, `q ∈ K`, or `Q` (pseudo-divide, `elim_dyn`, `gauss_dyn`,
  `torsion_dyn`).
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {B : Type*} [CommRing B] {r : ℕ}

/-- The Jouanolou relation `Σ cᵢ σᵢ - 1`. -/
noncomputable def relC (c : Fin (r + 1) → B) : MvPolynomial (Fin (r + 1)) B := ∑ i, C (c i) * X i - 1

/-- `K = 𝔞[σ] + (q_c)`: the lifts of `𝔞 J_B(c)`. -/
noncomputable def KJ (𝔞 : Ideal B) (c : Fin (r + 1) → B) : Ideal (MvPolynomial (Fin (r + 1)) B) :=
  Ideal.map C 𝔞 ⊔ Ideal.span {relC c}

lemma relC_mem_KJ (𝔞 : Ideal B) (c : Fin (r + 1) → B) : relC c ∈ KJ 𝔞 c :=
  Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

lemma map_C_le_KJ (𝔞 : Ideal B) (c : Fin (r + 1) → B) : Ideal.map C 𝔞 ≤ KJ 𝔞 c := le_sup_left

lemma mem_KJ_iff {𝔞 : Ideal B} {c : Fin (r + 1) → B} {p : MvPolynomial (Fin (r + 1)) B} :
    p ∈ KJ 𝔞 c ↔ ∃ a w, PolyIn 𝔞 a ∧ p = a + w * relC c := by
  constructor
  · intro h
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    exact ⟨a, w, (polyIn_iff_mem_map 𝔞 a).2 ha, rfl⟩
  · rintro ⟨a, w, ha, rfl⟩
    exact add_mem (map_C_le_KJ 𝔞 c ((polyIn_iff_mem_map 𝔞 a).1 ha))
      (Ideal.mul_mem_left _ _ (relC_mem_KJ 𝔞 c))

/-! ### `q_c` is a non-zero-divisor -/

lemma map_relC {D : Type*} [CommRing D] (f : B →+* D) (c : Fin (r + 1) → B) :
    MvPolynomial.map f (relC c) = relC (f ∘ c) := by
  simp [relC]

lemma relC_nzd {D : Type*} [CommRing D] (c : Fin (r + 1) → D) {p : MvPolynomial (Fin (r + 1)) D}
    (h : p * relC c = 0) : p = 0 := by
  have hu : IsUnit ((relC c : MvPolynomial (Fin (r + 1)) D) : MvPowerSeries (Fin (r + 1)) D) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPolynomial.coeff_coe, ← MvPolynomial.constantCoeff_eq]
    have : MvPolynomial.constantCoeff (relC c) = -1 := by rw [relC]; simp
    rw [this]; exact isUnit_one.neg
  have h2 : ((p : MvPolynomial (Fin (r + 1)) D) : MvPowerSeries (Fin (r + 1)) D) *
      ((relC c : MvPolynomial (Fin (r + 1)) D) : MvPowerSeries (Fin (r + 1)) D) = 0 := by
    rw [← MvPolynomial.coe_mul, h, MvPolynomial.coe_zero]
  exact MvPolynomial.coe_injective _ _ ((hu.mul_left_eq_zero.1 h2).trans MvPolynomial.coe_zero.symm)

/-! ### Torsion-freeness -/

variable {𝔞 : Ideal B} (hdec : ∀ x, x ∈ 𝔞 ∨ x ∉ 𝔞) {Q : Prop}
  (hpr : ∀ x y, x * y ∈ 𝔞 → x ∈ 𝔞 ∨ y ∈ 𝔞 ∨ Q)

include hdec hpr in
/-- **Torsion-freeness up to `Q`**: `b ∉ 𝔞`, `b p ∈ K` give `p ∈ K` or `Q`. -/
theorem torsion_dyn (c : Fin (r + 1) → B) {b : B} (hb : b ∉ 𝔞) {p : MvPolynomial (Fin (r + 1)) B}
    (h : C b * p ∈ KJ 𝔞 c) : p ∈ KJ 𝔞 c ∨ Q := by
  obtain ⟨a, w, ha, haw⟩ := mem_KJ_iff.1 h
  set 𝔟 : Ideal B := 𝔞 ⊔ Ideal.span {b}
  set π := Ideal.Quotient.mk 𝔟
  -- `w ∈ 𝔟[σ]`
  have h1 : MvPolynomial.map π w * relC (π ∘ c) = 0 := by
    have hb𝔟 : π b = 0 := Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
    have ha𝔟 : MvPolynomial.map π a = 0 := by
      ext d; rw [coeff_map]
      exact (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (ha d))).trans (by simp)
    have := congrArg (MvPolynomial.map π) haw
    rw [map_mul, map_C, hb𝔟, C_0, zero_mul, map_add, ha𝔟, zero_add, map_mul, map_relC] at this
    exact this.symm
  have h2 : w ∈ Ideal.map (C : B →+* MvPolynomial (Fin (r + 1)) B) 𝔟 := by
    have := relC_nzd _ h1
    rw [← Ideal.mk_ker (I := 𝔟), ← MvPolynomial.ker_map]; exact this
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton] at h2
  obtain ⟨w𝔞, hw𝔞, y, hy, rfl⟩ := Submodule.mem_sup.1 h2
  obtain ⟨w', rfl⟩ := Ideal.mem_span_singleton'.1 hy
  -- cancel `b`
  have h3 : PolyIn 𝔞 (C b * (p - w' * relC c)) := by
    have : C b * (p - w' * relC c) = a + w𝔞 * relC c := by rw [mul_sub, haw]; ring
    rw [this, polyIn_iff_mem_map]
    exact add_mem ((polyIn_iff_mem_map 𝔞 a).1 ha) (Ideal.mul_mem_right _ _ hw𝔞)
  rcases polyIn_cancel hdec hpr hb h3 with h4 | h4
  · refine Or.inl ?_
    have : p = (p - w' * relC c) + w' * relC c := by ring
    rw [this]
    exact add_mem (map_C_le_KJ 𝔞 c ((polyIn_iff_mem_map 𝔞 _).1 h4))
      (Ideal.mul_mem_left _ _ (relC_mem_KJ 𝔞 c))
  · exact Or.inr h4

/-! ### Elimination of `σ_0` -/

lemma coeff_relC_e0 (c : Fin (r + 1) → B) : (relC c).coeff (Finsupp.single 0 1) = c 0 := by
  have hne : ∀ j : Fin r, Finsupp.single (Fin.succ j) 1 ≠ (Finsupp.single 0 1 : Fin (r + 1) →₀ ℕ) :=
    fun j h => Fin.succ_ne_zero j ((Finsupp.single_left_inj one_ne_zero).1 h)
  have h0 : (0 : Fin (r + 1) →₀ ℕ) ≠ Finsupp.single 0 1 := fun h => by
    have := congrArg (fun f => f 0) h; simp at this
  rw [relC, MvPolynomial.coeff_sub, coeff_one, if_neg h0, sub_zero, MvPolynomial.coeff_sum,
    Fin.sum_univ_succ, coeff_C_mul, coeff_X', if_pos rfl, mul_one,
    Finset.sum_eq_zero fun j _ => by rw [coeff_C_mul, coeff_X', if_neg (hne j), mul_zero], add_zero]

lemma coeff_relC_of_ne (c : Fin (r + 1) → B) {m : Fin (r + 1) →₀ ℕ} (hm : m 0 ≠ 0)
    (hne : Finsupp.single 0 1 ≠ m) : (relC c).coeff m = 0 := by
  have h1 : ∀ j : Fin r, Finsupp.single (Fin.succ j) 1 ≠ m := fun j h => hm (by
    rw [← h, Finsupp.single_eq_of_ne (Fin.succ_ne_zero j).symm])
  have h0 : (0 : Fin (r + 1) →₀ ℕ) ≠ m := fun h => hm (by rw [← h]; rfl)
  rw [relC, MvPolynomial.coeff_sub, coeff_one, if_neg h0, sub_zero, MvPolynomial.coeff_sum,
    Fin.sum_univ_succ, coeff_C_mul, coeff_X', if_neg hne, mul_zero,
    Finset.sum_eq_zero fun j _ => by rw [coeff_C_mul, coeff_X', if_neg (h1 j), mul_zero], add_zero]

lemma degree_relC_le (c : Fin (r + 1) → B) :
    (MonomialOrder.lex : MonomialOrder (Fin (r + 1))).toSyn
        ((MonomialOrder.lex : MonomialOrder (Fin (r + 1))).degree (relC c)) ≤
      (MonomialOrder.lex : MonomialOrder (Fin (r + 1))).toSyn (Finsupp.single 0 1) := by
  rw [MonomialOrder.degree_le_iff]
  intro m hm
  rw [MonomialOrder.lex_le_iff]
  rcases Nat.decEq (m 0) 0 with hm0 | hm0
  · rcases decEq (Finsupp.single (0 : Fin (r + 1)) 1) m with hne | rfl
    · exact absurd (coeff_relC_of_ne c hm0 hne) (mem_support_iff.1 hm)
    · exact le_rfl
  · refine le_of_lt (Finsupp.Lex.lt_iff.2 ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩)
    simp [hm0]

/-- `σ_0`-free: no monomial with a positive power of `σ_0`. -/
def Free0 (h : MvPolynomial (Fin (r + 1)) B) : Prop := ∀ d, d 0 ≠ 0 → h.coeff d = 0

lemma free0_rename (h₀ : MvPolynomial (Fin r) B) : Free0 (rename Fin.succ h₀) := by
  intro d hd
  refine coeff_rename_eq_zero _ _ _ fun u hu => absurd ?_ hd
  rw [← hu, Finsupp.mapDomain_notin_range]
  rintro ⟨j, hj⟩; exact Fin.succ_ne_zero j hj

include hdec hpr in
/-- **Elimination up to `Q`**: a `σ_0`-free element of `K` lies in `𝔞[σ]`, or `Q`. -/
theorem elim_dyn (c : Fin (r + 1) → B) (hc0 : c 0 ∉ 𝔞) {h : MvPolynomial (Fin (r + 1)) B}
    (hfree : Free0 h) (hK : h ∈ KJ 𝔞 c) : PolyIn 𝔞 h ∨ Q := by
  obtain ⟨a, w, ha, rfl⟩ := mem_KJ_iff.1 hK
  obtain ⟨w₁, w₂, rfl, hw₂, hw₁⟩ := polyIn_strip hdec w
  set m := (MonomialOrder.lex : MonomialOrder (Fin (r + 1)))
  set e₀ : Fin (r + 1) →₀ ℕ := Finsupp.single 0 1
  -- the coefficient `lc(w₁) c_0`
  have hcoeff : (w₁ * relC c).coeff (m.degree w₁ + e₀) = m.leadingCoeff w₁ * c 0 := by
    rw [m.coeff_mul_of_add_of_degree_le le_rfl (degree_relC_le c), coeff_relC_e0]; rfl
  have hmem : (w₁ * relC c).coeff (m.degree w₁ + e₀) ∈ 𝔞 := by
    have heq : w₁ * relC c = (a + (w₁ + w₂) * relC c) - a - w₂ * relC c := by ring
    rw [heq, coeff_sub, coeff_sub, hfree _ (by simp [e₀]), zero_sub]
    refine sub_mem (neg_mem (ha _)) ?_
    have : PolyIn 𝔞 (w₂ * relC c) := by
      rw [polyIn_iff_mem_map] at hw₂ ⊢; exact Ideal.mul_mem_right _ _ hw₂
    exact this _
  rw [hcoeff] at hmem
  rcases hpr _ _ hmem with hlc | hc | hq
  · have hw0 : w₁ = 0 := m.leadingCoeff_eq_zero_iff.1 (hw₁ _ hlc)
    subst hw0
    refine Or.inl ?_
    rw [zero_add]
    rw [polyIn_iff_mem_map] at ha hw₂ ⊢
    exact add_mem ha (Ideal.mul_mem_right _ _ hw₂)
  · exact absurd hc hc0
  · exact Or.inr hq

/-! ### Pseudo-division and the main lemma -/

/-- **Pseudo-division** by `q_c`, eliminating `σ_0`. -/
lemma pseudo0 (c : Fin (r + 1) → B) (p : MvPolynomial (Fin (r + 1)) B) :
    ∃ (N : ℕ) (q : MvPolynomial (Fin (r + 1)) B) (p₀ : MvPolynomial (Fin r) B),
      C (c 0) ^ N * p = q * relC c + rename Fin.succ p₀ := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, 0, C a, by simp⟩
  | add p p' ih ih' =>
    obtain ⟨N, q, p₀, h⟩ := ih
    obtain ⟨N', q', p₀', h'⟩ := ih'
    refine ⟨N + N', C (c 0) ^ N' * q + C (c 0) ^ N * q',
      C (c 0) ^ N' * p₀ + C (c 0) ^ N * p₀', ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, rename_C, pow_add, mul_add]
    calc C (c 0) ^ N * C (c 0) ^ N' * p + C (c 0) ^ N * C (c 0) ^ N' * p'
        = C (c 0) ^ N' * (C (c 0) ^ N * p) + C (c 0) ^ N * (C (c 0) ^ N' * p') := by ring
      _ = _ := by rw [h, h']; ring
  | mul_X p i ih =>
    obtain ⟨N, q, p₀, h⟩ := ih
    induction i using Fin.cases with
    | zero =>
      set g₀ : MvPolynomial (Fin r) B := 1 - ∑ j, C (c (Fin.succ j)) * X j
      have hg : X 0 * C (c 0) = relC c + rename Fin.succ g₀ := by
        simp only [g₀, relC, map_sub, map_one, map_sum, map_mul, rename_X, rename_C]
        rw [Fin.sum_univ_succ]; ring
      refine ⟨N + 1, q * (relC c + rename Fin.succ g₀) + rename Fin.succ p₀, p₀ * g₀, ?_⟩
      calc C (c 0) ^ (N + 1) * (p * X 0) = (C (c 0) ^ N * p) * (X 0 * C (c 0)) := by ring
        _ = _ := by rw [h, hg, map_mul]; ring
    | succ j =>
      refine ⟨N, q * X (Fin.succ j), p₀ * X j, ?_⟩
      calc C (c 0) ^ N * (p * X (Fin.succ j)) = (C (c 0) ^ N * p) * X (Fin.succ j) := by ring
        _ = _ := by rw [h, map_mul, rename_X]; ring

include hdec hpr in
/-- `c_0 ∉ 𝔞` gives `c_0ᴺ ∉ 𝔞`, up to `Q`. -/
lemma pow_not_mem_dyn {x : B} (hx : x ∉ 𝔞) : ∀ N : ℕ, x ^ N ∉ 𝔞 ∨ Q
  | 0 => Or.inl fun h => hx (by simpa using 𝔞.mul_mem_left x h)
  | N + 1 => by
    rcases pow_not_mem_dyn hx N with hN | hN
    · rcases hdec (x ^ (N + 1)) with h | h
      · rw [pow_succ] at h
        rcases hpr _ _ h with h' | h' | h'
        · exact absurd h' hN
        · exact absurd h' hx
        · exact Or.inr h'
      · exact Or.inl h
    · exact Or.inr hN

include hdec hpr in
/-- From `C(c_0)ᴺ p = q q_c + P₀` with `P₀ ∈ 𝔞[σ]`: `p ∈ K`, or `Q`. -/
lemma mem_KJ_of_pseudo (c : Fin (r + 1) → B) (hc0 : c 0 ∉ 𝔞) {N : ℕ}
    {p q P₀ : MvPolynomial (Fin (r + 1)) B} (h : C (c 0) ^ N * p = q * relC c + P₀)
    (hP₀ : PolyIn 𝔞 P₀) : p ∈ KJ 𝔞 c ∨ Q := by
  rcases pow_not_mem_dyn hdec hpr hc0 N with hN | hN
  · refine torsion_dyn hdec hpr c hN ?_
    rw [map_pow, h]
    exact add_mem (Ideal.mul_mem_left _ _ (relC_mem_KJ 𝔞 c))
      (map_C_le_KJ 𝔞 c ((polyIn_iff_mem_map 𝔞 _).1 hP₀))
  · exact Or.inr hN

include hdec hpr in
/-- **`𝔞 J_B(c)` is prime up to `Q`** (`c_0 ∉ 𝔞`). -/
theorem jou_dyn (c : Fin (r + 1) → B) (hc0 : c 0 ∉ 𝔞)
    {p q : MvPolynomial (Fin (r + 1)) B} (hpq : p * q ∈ KJ 𝔞 c) :
    p ∈ KJ 𝔞 c ∨ q ∈ KJ 𝔞 c ∨ Q := by
  obtain ⟨N, q₁, p₀, hp⟩ := pseudo0 c p
  obtain ⟨M, q₂, q₀, hq⟩ := pseudo0 c q
  set P₀ := rename Fin.succ p₀
  set Q₀ := rename Fin.succ q₀
  -- `P₀ Q₀ ∈ K`
  have hPQ : P₀ * Q₀ ∈ KJ 𝔞 c := by
    have : P₀ * Q₀ = C (c 0) ^ (N + M) * (p * q) -
        (q₁ * Q₀ + P₀ * q₂ + q₁ * q₂ * relC c) * relC c := by
      rw [pow_add]
      linear_combination (-(C (c 0) ^ M * q)) * hp - (q₁ * relC c + P₀) * hq
    rw [this]
    exact sub_mem (Ideal.mul_mem_left _ _ hpq) (Ideal.mul_mem_left _ _ (relC_mem_KJ 𝔞 c))
  have hfree : Free0 (P₀ * Q₀) := by
    rw [show P₀ * Q₀ = rename Fin.succ (p₀ * q₀) by rw [map_mul]]
    exact free0_rename _
  rcases elim_dyn hdec hpr c hc0 hfree hPQ with hin | hQ
  · rcases gauss_dyn MonomialOrder.lex hdec hpr hin with hP | hQ' | hQ
    · rcases mem_KJ_of_pseudo hdec hpr c hc0 hp hP with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rcases mem_KJ_of_pseudo hdec hpr c hc0 hq hQ' with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inr hQ)
  · exact Or.inr (Or.inr hQ)

/-! ### Any index `l` -/

omit [CommRing B] in
lemma rename_relC {B : Type*} [CommRing B] (e : Fin (r + 1) ≃ Fin (r + 1)) (c : Fin (r + 1) → B) :
    rename e (relC c) = relC (c ∘ e.symm) := by
  simp only [relC, map_sub, map_one, map_sum, map_mul, rename_C, rename_X, Function.comp_apply]
  congr 1
  exact (Finset.sum_congr rfl fun i _ => by rw [Equiv.symm_apply_apply]).trans
    (Equiv.sum_comp e (fun j => C (c (e.symm j)) * X j))

lemma polyIn_rename (e : Fin (r + 1) ≃ Fin (r + 1)) {a : MvPolynomial (Fin (r + 1)) B}
    (ha : PolyIn 𝔞 a) : PolyIn 𝔞 (rename e a) := by
  rw [polyIn_iff_mem_map] at ha ⊢
  set φ : MvPolynomial (Fin (r + 1)) B →+* MvPolynomial (Fin (r + 1)) B := (rename e).toRingHom
  have h := Ideal.mem_map_of_mem φ ha
  rw [Ideal.map_map, show φ.comp C = C by ext b : 1; simp [φ, rename_C]] at h
  exact h

lemma rename_mem_KJ (e : Fin (r + 1) ≃ Fin (r + 1)) (c : Fin (r + 1) → B)
    {p : MvPolynomial (Fin (r + 1)) B} (hp : p ∈ KJ 𝔞 c) : rename e p ∈ KJ 𝔞 (c ∘ e.symm) := by
  obtain ⟨a, w, ha, rfl⟩ := mem_KJ_iff.1 hp
  exact mem_KJ_iff.2 ⟨rename e a, rename e w, polyIn_rename e ha,
    by rw [map_add, map_mul, rename_relC]⟩

lemma mem_KJ_rename (e : Fin (r + 1) ≃ Fin (r + 1)) (c : Fin (r + 1) → B)
    (p : MvPolynomial (Fin (r + 1)) B) :
    rename e p ∈ KJ 𝔞 (c ∘ e.symm) ↔ p ∈ KJ 𝔞 c := by
  refine ⟨fun h => ?_, rename_mem_KJ e c⟩
  have h2 := rename_mem_KJ e.symm (c ∘ e.symm) h
  rwa [rename_rename, show (e.symm ∘ e : Fin (r + 1) → Fin (r + 1)) = id from
    funext e.symm_apply_apply, rename_id_apply, Equiv.symm_symm, Function.comp_assoc,
    show (e.symm ∘ e : Fin (r + 1) → Fin (r + 1)) = id from funext e.symm_apply_apply,
    Function.comp_id] at h2

include hdec hpr in
/-- **`𝔞 J_B(c)` is prime up to `Q`**, for any index `l` with `c_l ∉ 𝔞`. -/
theorem jou_dyn_l (c : Fin (r + 1) → B) (l : Fin (r + 1)) (hcl : c l ∉ 𝔞)
    {p q : MvPolynomial (Fin (r + 1)) B} (hpq : p * q ∈ KJ 𝔞 c) :
    p ∈ KJ 𝔞 c ∨ q ∈ KJ 𝔞 c ∨ Q := by
  set e := Equiv.swap (0 : Fin (r + 1)) l
  have hc0 : (c ∘ e.symm) 0 ∉ 𝔞 := by
    simp only [Function.comp_apply, e, Equiv.symm_swap, Equiv.swap_apply_left]; exact hcl
  have h := jou_dyn hdec hpr (c ∘ e.symm) hc0 (p := rename e p) (q := rename e q)
    (by rw [← map_mul, mem_KJ_rename]; exact hpq)
  rw [mem_KJ_rename, mem_KJ_rename] at h
  exact h

end BezoutCounterexample.Constructive
