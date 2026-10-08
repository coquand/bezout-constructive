import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Gauss's lemma with an escape (D5; `docs/d5-plan.md`, step 3)

An ideal `𝔞` of a commutative ring `B` with decidable membership (`hdec`) is **prime up to `Q`**
(`hpr`): `x y ∈ 𝔞` gives `x ∈ 𝔞`, `y ∈ 𝔞`, or `Q`. In the D5 use `Q` is a split of the radical
ideal `(P)` (`RadSplit P`), and `𝔞` is `(s)` in the Rees algebra (`span_s_dyn_split`).

* `PolyIn 𝔞 f`: every coefficient of `f` lies in `𝔞` (i.e. `f ∈ 𝔞[σ]`, `polyIn_iff_mem_map`).
* `polyIn_dec`: decided by a search over the support.
* `polyIn_strip`: `f = f₁ + f₂` with `f₂ ∈ 𝔞[σ]` and no nonzero coefficient of `f₁` in `𝔞`.
* `polyIn_cancel`: `b ∉ 𝔞`, `b p ∈ 𝔞[σ]` give `p ∈ 𝔞[σ]` or `Q`.
* `gauss_dyn`: `f g ∈ 𝔞[σ]` gives `f ∈ 𝔞[σ]`, `g ∈ 𝔞[σ]`, or `Q`. Leading coefficients for any
  monomial order: strip both factors, then `lc(f₁) lc(g₁)` is a coefficient of
  `f₁ g₁ ∈ 𝔞[σ]` (`MonomialOrder.coeff_mul_of_degree_add`).
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {σ : Type*} {B : Type*} [CommRing B] (𝔞 : Ideal B)

/-- All coefficients of `f` lie in `𝔞`. -/
def PolyIn (f : MvPolynomial σ B) : Prop := ∀ d, f.coeff d ∈ 𝔞

lemma polyIn_iff_mem_map (f : MvPolynomial σ B) :
    PolyIn 𝔞 f ↔ f ∈ Ideal.map (C : B →+* MvPolynomial σ B) 𝔞 :=
  (mem_map_C_iff).symm

/-- Finite search over a finset (no decidable equality needed). -/
lemma finset_search {α : Type*} (S : Finset α) (p : α → Prop) (hdec : ∀ a, p a ∨ ¬ p a) :
    (∀ a ∈ S, p a) ∨ ∃ a ∈ S, ¬ p a := by
  obtain ⟨s, hs⟩ := S
  simp only [Finset.mem_mk]
  clear hs
  induction s using Multiset.induction_on with
  | empty => exact Or.inl fun a ha => absurd ha (Multiset.notMem_zero a)
  | cons b s ih =>
    rcases hdec b with hb | hb
    · rcases ih with hall | ⟨a, ha, hna⟩
      · exact Or.inl fun a ha => (Multiset.mem_cons.1 ha).elim (· ▸ hb) (hall a)
      · exact Or.inr ⟨a, Multiset.mem_cons_of_mem ha, hna⟩
    · exact Or.inr ⟨b, Multiset.mem_cons_self b s, hb⟩

variable {𝔞}

/-- Membership in `𝔞[σ]` is decidable. -/
lemma polyIn_dec [DecidableEq σ] (hdec : ∀ x, x ∈ 𝔞 ∨ x ∉ 𝔞) (f : MvPolynomial σ B) :
    PolyIn 𝔞 f ∨ ∃ d, f.coeff d ∉ 𝔞 := by
  rcases finset_search f.support (fun d => f.coeff d ∈ 𝔞) (fun d => hdec _) with hall | ⟨d, -, hd⟩
  · refine Or.inl fun d => ?_
    rcases Finset.decidableMem d f.support with h | h
    · rw [notMem_support_iff.1 h]; exact zero_mem _
    · exact hall d h
  · exact Or.inr ⟨d, hd⟩

/-- Cancellation of `b ∉ 𝔞`, up to `Q`. -/
lemma polyIn_cancel [DecidableEq σ] (hdec : ∀ x, x ∈ 𝔞 ∨ x ∉ 𝔞) {Q : Prop}
    (hpr : ∀ x y, x * y ∈ 𝔞 → x ∈ 𝔞 ∨ y ∈ 𝔞 ∨ Q) {b : B} (hb : b ∉ 𝔞)
    {p : MvPolynomial σ B} (h : PolyIn 𝔞 (C b * p)) : PolyIn 𝔞 p ∨ Q := by
  rcases polyIn_dec hdec p with hp | ⟨d, hd⟩
  · exact Or.inl hp
  have := h d
  rw [coeff_C_mul] at this
  rcases hpr _ _ this with h1 | h1 | h1
  · exact absurd h1 hb
  · exact absurd h1 hd
  · exact Or.inr h1

/-- **Stripping**: `f = f₁ + f₂` with `f₂ ∈ 𝔞[σ]` and no nonzero coefficient of `f₁` in `𝔞`. -/
lemma polyIn_strip [DecidableEq σ] (hdec : ∀ x, x ∈ 𝔞 ∨ x ∉ 𝔞) (f : MvPolynomial σ B) :
    ∃ f₁ f₂ : MvPolynomial σ B, f = f₁ + f₂ ∧ PolyIn 𝔞 f₂ ∧
      ∀ d, f₁.coeff d ∈ 𝔞 → f₁.coeff d = 0 := by
  have key : ∀ S : Finset (σ →₀ ℕ), ∃ f₁ f₂ : MvPolynomial σ B,
      ∑ d ∈ S, monomial d (f.coeff d) = f₁ + f₂ ∧ PolyIn 𝔞 f₂ ∧
      (∀ d, f₁.coeff d ∈ 𝔞 → f₁.coeff d = 0) ∧ ∀ d ∉ S, f₁.coeff d = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨0, 0, by simp, fun d => by simp, fun d _ => rfl,
        fun d _ => rfl⟩
    | insert e S he ih =>
      obtain ⟨f₁, f₂, hsum, h₂, hgood, hout⟩ := ih
      rw [Finset.sum_insert he, hsum]
      rcases hdec (f.coeff e) with hfe | hfe
      · refine ⟨f₁, monomial e (f.coeff e) + f₂, by ring, fun d => ?_, hgood,
          fun d hd => hout d fun h => hd (Finset.mem_insert_of_mem h)⟩
        rw [MvPolynomial.coeff_add, coeff_monomial]
        rcases decEq e d with hne | rfl
        · rw [if_neg hne, zero_add]; exact h₂ d
        · rw [if_pos rfl]; exact add_mem hfe (h₂ _)
      · refine ⟨monomial e (f.coeff e) + f₁, f₂, by ring, h₂, fun d hd => ?_, fun d hd => ?_⟩
        · rw [MvPolynomial.coeff_add, coeff_monomial] at hd ⊢
          rcases decEq e d with hne | rfl
          · rw [if_neg hne, zero_add] at hd ⊢; exact hgood d hd
          · rw [if_pos rfl, hout e he, add_zero] at hd; exact absurd hd hfe
        · have hne : e ≠ d := fun h => hd (h ▸ Finset.mem_insert_self e S)
          rw [MvPolynomial.coeff_add, coeff_monomial, if_neg hne, zero_add]
          exact hout d fun h => hd (Finset.mem_insert_of_mem h)
  obtain ⟨f₁, f₂, hsum, h₂, hgood, -⟩ := key f.support
  exact ⟨f₁, f₂, by rw [← hsum]; exact f.as_sum, h₂, hgood⟩

/-- **Gauss's lemma, prime-up-to-`Q` form.** -/
theorem gauss_dyn [DecidableEq σ] (m : MonomialOrder σ) (hdec : ∀ x, x ∈ 𝔞 ∨ x ∉ 𝔞) {Q : Prop}
    (hpr : ∀ x y, x * y ∈ 𝔞 → x ∈ 𝔞 ∨ y ∈ 𝔞 ∨ Q) {f g : MvPolynomial σ B}
    (hfg : PolyIn 𝔞 (f * g)) : PolyIn 𝔞 f ∨ PolyIn 𝔞 g ∨ Q := by
  rcases polyIn_dec hdec f with hf | ⟨d, hd⟩
  · exact Or.inl hf
  rcases polyIn_dec hdec g with hg | ⟨e, he⟩
  · exact Or.inr (Or.inl hg)
  obtain ⟨f₁, f₂, rfl, hf₂, hf₁⟩ := polyIn_strip hdec f
  obtain ⟨g₁, g₂, rfl, hg₂, hg₁⟩ := polyIn_strip hdec g
  -- `f₁ g₁ ∈ 𝔞[σ]`
  have h11 : PolyIn 𝔞 (f₁ * g₁) := by
    rw [polyIn_iff_mem_map] at hfg hf₂ hg₂ ⊢
    have : f₁ * g₁ = (f₁ + f₂) * (g₁ + g₂) - f₁ * g₂ - f₂ * (g₁ + g₂) := by ring
    rw [this]
    exact sub_mem (sub_mem hfg (Ideal.mul_mem_left _ _ hg₂)) (Ideal.mul_mem_right _ _ hf₂)
  -- the leading coefficients are not in `𝔞`
  have hlc : ∀ {p₁ p₂ : MvPolynomial σ B} {d : σ →₀ ℕ}, PolyIn 𝔞 p₂ →
      (∀ d, p₁.coeff d ∈ 𝔞 → p₁.coeff d = 0) → (p₁ + p₂).coeff d ∉ 𝔞 →
      m.leadingCoeff p₁ ∉ 𝔞 := by
    intro p₁ p₂ d hp₂ hp₁ hd hlc
    have h0 : p₁ = 0 := m.leadingCoeff_eq_zero_iff.1 (hp₁ _ hlc)
    rw [h0, zero_add] at hd
    exact hd (hp₂ d)
  have hmul := h11 (m.degree f₁ + m.degree g₁)
  rw [m.coeff_mul_of_degree_add] at hmul
  rcases hpr _ _ hmul with h | h | h
  · exact absurd h (hlc hf₂ hf₁ hd)
  · exact absurd h (hlc hg₂ hg₁ he)
  · exact Or.inr (Or.inr h)

end BezoutCounterexample.Constructive
