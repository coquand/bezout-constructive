import BezoutCounterexample.Constructive.DynPrime
import BezoutCounterexample.Constructive.InvPrinc

/-!
# The divisorial step, prime-or-split (D5; `docs/d5-plan.md`, step 3)

Dynamical form of `Principalization.div_eq_span_G`. There, `𝔭` is a prime component in the
divisorial case, `𝔭 A_𝔪 = (x)` at a maximal `𝔪 ⊇ 𝔭` (from `LocData`), and the gcd `δ` of the
generators lies in `𝔭` because `𝔭` is prime and contracted from `A_𝔪`.

Here no `LocData` is used. The divisorial hypothesis is stated as **local principality with a
denominator outside `(P)`**: an `x ∈ (P)` and an `s ∉ (P)` with `x ∣ s g` for every generator `g`
(classically: `s` clears the denominators of `g / x` in `A_𝔪`, so `s ∉ 𝔪 ⊇ 𝔭`). Then

* `x ∣ gcd(s g) = s δ` (`isGcdFam_mul_left`), so `s δ ∈ (P)`;
* `dynPrimeRad` on `s δ`: `s ∈ (P)` is excluded, `δ ∈ (P)` gives `(P) = (δ)`, and otherwise
  `(P) = (L₁) ∩ (L₂)` with radical pieces, strictly larger (`δ ∈ L₁`, `s ∈ L₂`).

`div_dyn`: `(P) = (δ)`, or such a split. `(P)` radical is used only in the split branch.
-/

namespace BezoutCounterexample.Constructive

variable {A : Type*} [CommRing A] [IsDomain A]

/-- `x ∣ s g` for all generators gives `x ∣ s δ`, hence `s δ ∈ (P)` when `x ∈ (P)`. -/
lemma mul_gcd_mem (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) {P : List A} {s x δ : A}
    (hx : x ∈ lspan P) (hxs : ∀ g ∈ P, x ∣ s * g) (hδ : IsGcdFam δ P.get) :
    s * δ ∈ lspan P := by
  obtain ⟨c, hc⟩ := (isGcdFam_mul_left hG hz hδ s).2 x fun j => hxs _ (List.get_mem P j)
  rw [hc]; exact Ideal.mul_mem_right _ _ hx

omit [IsDomain A] in
/-- A gcd of the generators that lies in `(P)` generates `(P)`. -/
lemma lspan_eq_span_gcd {P : List A} {δ : A} (hδ : IsGcdFam δ P.get) (hδP : δ ∈ lspan P) :
    lspan P = Ideal.span {δ} := by
  refine le_antisymm (Ideal.span_le.2 fun g hg => ?_) ((Ideal.span_singleton_le_iff_mem _).2 hδP)
  obtain ⟨j, rfl⟩ := List.get_of_mem hg
  exact Ideal.mem_span_singleton.2 (hδ.1 j)

/-- **Divisorial step, prime-or-split.** -/
theorem div_dyn (h : HasPres A) (hG : HasGcd A) {P : List A} (hP : IsRadL P) {s x δ : A}
    (hs : s ∉ lspan P) (hx : x ∈ lspan P) (hxs : ∀ g ∈ P, x ∣ s * g) (hδ : IsGcdFam δ P.get) :
    lspan P = Ideal.span {δ} ∨ ∃ L₁ L₂ : List A, IsRadL L₁ ∧ IsRadL L₂ ∧
      lspan P ≤ lspan L₁ ∧ lspan P ≤ lspan L₂ ∧
      (∃ y ∈ lspan L₁, y ∉ lspan P) ∧ (∃ y ∈ lspan L₂, y ∉ lspan P) ∧
      ∀ y, y ∈ lspan P ↔ y ∈ lspan L₁ ∧ y ∈ lspan L₂ := by
  have hsδ := mul_gcd_mem hG h.zeroTest hx hxs hδ
  rcases dynPrimeRad h hP hsδ with hsP | hδP | ⟨-, hδP, L₁, L₂, r₁, r₂, l₁, l₂, m₁, m₂, hsp⟩
  · exact absurd hsP hs
  · exact Or.inl (lspan_eq_span_gcd hδ hδP)
  · exact Or.inr ⟨L₁, L₂, r₁, r₂, l₁, l₂, ⟨δ, m₁, hδP⟩, ⟨s, m₂, hs⟩, hsp⟩

end BezoutCounterexample.Constructive
