import BezoutCounterexample.Constructive.DynPrime
import BezoutCounterexample.Constructive.ValBar

/-!
# Lemma gcd1, prime-or-split (D5; `docs/d5-plan.md`, step 3)

Dynamical form of `Principalization.gens_gcd_isUnit` (`~/COLL/bezout-gcd.tex`, Lemma gcd1). There,
`𝔭` is prime, `b` divides every generator of `𝔭`, `b ∉ 𝔭`, and Nakayama gives `b` a unit. Here
`𝔭 = (P)` is only an explicit **radical** ideal of a presented, inductively Noetherian domain.

* `gens_search`: write each generator `g = b tᵍ` and decide `tᵍ ∈ (P)` (finite search).
* If every `tᵍ ∈ (P)`, then `(P) ⊆ b (P)`, so `bⁿ ∣ g₀` for all `n`; the valuation from the bar
  (`IndNoeth.exists_val`) makes `b` a unit (no Nakayama, no finite generation argument).
* Otherwise `b tᵍ ∈ (P)` with `b, tᵍ ∉ (P)`: the radical split of `dynPrimeRad`.

`gcd1_dyn`: `IsUnit b`, or `(P) = (L₁) ∩ (L₂)` with `L₁, L₂` radical and strictly larger.
-/

namespace BezoutCounterexample.Constructive

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
/-- Finite search: either every generator is `b` times an element of `(P)`, or one is `b t` with
`t ∉ (P)`. -/
lemma gens_search (h : HasPres A) (P : List A) {b : A} (Q : List A) (hQ : ∀ g ∈ Q, b ∣ g) :
    (∀ g ∈ Q, ∃ t ∈ lspan P, g = b * t) ∨ ∃ g ∈ Q, ∃ t, g = b * t ∧ t ∉ lspan P := by
  induction Q with
  | nil => exact Or.inl fun g hg => absurd hg List.not_mem_nil
  | cons g Q ih =>
    obtain ⟨t, ht⟩ := hQ g (List.mem_cons_self ..)
    rcases h.mem_dec P t with htP | htP
    · rcases ih fun x hx => hQ x (List.mem_cons_of_mem g hx) with hall | ⟨g', hg', t', h1, h2⟩
      · refine Or.inl fun x hx => ?_
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨t, htP, ht⟩
        · exact hall x hx
      · exact Or.inr ⟨g', List.mem_cons_of_mem g hg', t', h1, h2⟩
    · exact Or.inr ⟨g, List.mem_cons_self .., t, ht, htP⟩

omit [IsDomain A] in
/-- If every generator is `b` times an element of `(P)`, then `(P) ⊆ b (P)`. -/
lemma mem_mul_of_gens {P : List A} {b : A} (hall : ∀ g ∈ P, ∃ t ∈ lspan P, g = b * t) :
    ∀ x ∈ lspan P, ∃ y ∈ lspan P, x = b * y := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz => exact hall z hz
  | zero => exact ⟨0, zero_mem _, (mul_zero b).symm⟩
  | add x z _ _ hx hz =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hz
    exact ⟨y + y', add_mem hy hy', (mul_add b y y').symm⟩
  | smul c z _ hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨c * y, Ideal.mul_mem_left _ c hy, by rw [smul_eq_mul, mul_left_comm]⟩

omit [IsDomain A] in
lemma pow_dvd_of_gens {P : List A} {b g₀ : A} (hall : ∀ g ∈ P, ∃ t ∈ lspan P, g = b * t)
    (hg₀ : g₀ ∈ lspan P) : ∀ n : ℕ, ∃ y ∈ lspan P, g₀ = b ^ n * y := by
  intro n
  induction n with
  | zero => exact ⟨g₀, hg₀, by rw [pow_zero, one_mul]⟩
  | succ n ih =>
    obtain ⟨y, hy, rfl⟩ := ih
    obtain ⟨y', hy', rfl⟩ := mem_mul_of_gens hall y hy
    exact ⟨y', hy', by rw [pow_succ, mul_assoc]⟩

/-- **Lemma gcd1, prime-or-split.** -/
theorem gcd1_dyn (h : HasPres A) (hN : IndNoeth A) {P : List A} (hP : IsRadL P) {b g₀ : A}
    (hb : ∀ g ∈ P, b ∣ g) (hbP : b ∉ lspan P) (hg₀ : g₀ ∈ lspan P) (hg₀0 : g₀ ≠ 0) :
    IsUnit b ∨ ∃ L₁ L₂ : List A, IsRadL L₁ ∧ IsRadL L₂ ∧
      lspan P ≤ lspan L₁ ∧ lspan P ≤ lspan L₂ ∧
      (∃ x ∈ lspan L₁, x ∉ lspan P) ∧ (∃ x ∈ lspan L₂, x ∉ lspan P) ∧
      ∀ x, x ∈ lspan P ↔ x ∈ lspan L₁ ∧ x ∈ lspan L₂ := by
  rcases h.dvdDec b 1 with hu | hu
  · exact Or.inl (isUnit_of_dvd_one hu)
  rcases gens_search h P P hb with hall | ⟨g, hg, t, hgt, htP⟩
  · exfalso
    have hnu : ¬ IsUnit b := fun h' => hu h'.dvd
    obtain ⟨n, c, hc, hbc⟩ := hN.exists_val hnu h.dvdDec hg₀0
    obtain ⟨y, -, hy⟩ := pow_dvd_of_gens hall hg₀ (n + 1)
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hg₀0 (by rw [hy, zero_pow (Nat.succ_ne_zero n), zero_mul])
    refine hbc ⟨y, mul_left_cancel₀ (pow_ne_zero n hb0) ?_⟩
    rw [← hc, hy, pow_succ, mul_assoc]
  · have hmem : b * t ∈ lspan P := hgt ▸ Ideal.subset_span hg
    rcases dynPrimeRad h hP hmem with hbP' | htP' | ⟨-, -, L₁, L₂, r₁, r₂, l₁, l₂, m₁, m₂, hs⟩
    · exact absurd hbP' hbP
    · exact absurd htP' htP
    · exact Or.inr ⟨L₁, L₂, r₁, r₂, l₁, l₂, ⟨t, m₁, htP⟩, ⟨b, m₂, hbP⟩, hs⟩

end BezoutCounterexample.Constructive
