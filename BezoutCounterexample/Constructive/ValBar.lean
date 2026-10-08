import BezoutCounterexample.Constructive.PolyNoeth

/-!
# Valuations from the bar (`~/COLL/bezout-gcd.tex`, Lemma 2.2)

In an inductively Noetherian domain with decidable divisibility, every nonzero non-unit `p` has a
computable `p`-adic valuation: every `a ≠ 0` is `pⁿ a°` with `p ∤ a°`. The search
`a, a/p, a/p², …` runs along the bar on the lists `[aₖ, …, a₀]`; a good list would give
`aₖ ∈ (aₖ₋₁) = (p aₖ)`, so `p` would be a unit. No Markov principle: the bar is the termination
proof. This supplies the finiteness input of Nagata's criterion in GCD form (`NagataGCD`), in place
of `FiniteMultiplicity` (which HM derive from `IsNoetherianRing`).
-/

namespace BezoutCounterexample.Constructive

variable {A : Type*} [CommRing A] [IsDomain A]

/-- Decidable divisibility, as a propositional decision. -/
def DvdDec (A : Type*) [CommRing A] : Prop := ∀ a b : A, a ∣ b ∨ ¬ a ∣ b

/-- The bar invariant: the head `b` is nonzero and `p b` divides all older entries. -/
theorem NBar.exists_val {p : A} (hp : ¬ IsUnit p) (hdec : ∀ b : A, p ∣ b ∨ ¬ p ∣ b)
    {L : List A} (hL : NBar L) :
    ∀ (b : A) (t : List A), L = b :: t → b ≠ 0 → (∀ x ∈ t, p * b ∣ x) →
      ∃ n : ℕ, ∃ c : A, b = p ^ n * c ∧ ¬ p ∣ c := by
  induction hL with
  | @good a l ha =>
    intro b t hL hb ht
    exfalso
    obtain ⟨hab, hlt⟩ := List.cons.inj hL
    rw [hab, hlt] at ha
    have hle : lspan t ≤ Ideal.span {p * b} :=
      Ideal.span_le.2 fun x hx => Ideal.mem_span_singleton.2 (ht x hx)
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (hle ha)
    apply hp
    have h1 : (y * p - 1) * b = 0 := by rw [sub_mul, one_mul, mul_assoc, hy, sub_self]
    have h2 : y * p - 1 = 0 := (mul_eq_zero.1 h1).resolve_right hb
    exact IsUnit.of_mul_eq_one (b := y) (by rw [mul_comm]; exact sub_eq_zero.1 h2)
  | @step l _ ih =>
    intro b t hL hb ht
    rcases hdec b with ⟨c, hc⟩ | hnd
    · have hc0 : c ≠ 0 := by rintro rfl; exact hb (by rw [hc, mul_zero])
      obtain ⟨n, e, he, hne⟩ := ih c c l rfl hc0 (by
        intro x hx
        rw [hL] at hx
        rcases List.mem_cons.1 hx with rfl | hxt
        · exact ⟨1, by rw [hc, mul_one]⟩
        · obtain ⟨w, hw⟩ := ht x hxt
          exact ⟨p * w, by rw [hw, hc]; ring⟩)
      exact ⟨n + 1, e, by rw [hc, he]; ring, hne⟩
    · exact ⟨0, b, by rw [pow_zero, one_mul], hnd⟩

/-- **Valuations from the bar.** -/
theorem IndNoeth.exists_val (hA : IndNoeth A) {p : A} (hp : ¬ IsUnit p) (hdec : DvdDec A)
    {a : A} (ha : a ≠ 0) : ∃ n : ℕ, ∃ c : A, a = p ^ n * c ∧ ¬ p ∣ c :=
  match hA with
  | .step h => (h a).exists_val hp (hdec p) a [] rfl ha (fun _ hx => absurd hx List.not_mem_nil)

end BezoutCounterexample.Constructive
