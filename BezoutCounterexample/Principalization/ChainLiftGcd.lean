import Mathlib
import BezoutCounterexample.Construction

/-!
# The gcd ideal and the coprime part (Task A, C3)

A gcd is unique only up to units, so `coprimeFactors` (a choice) is replaced by ideals:

* `IsGcdIdeal a b P`: `P` is the least principal ideal containing `(a, b)`;
  `existsUnique_gcdIdeal`: there is exactly one (existence from `hasGcd`), so it can be extracted
  by unique choice.
* `coprimePart a b P := (a, b) : P`; `coprimePart_eq_span`: it is `(a', b')` for every
  factorisation `a = g a'`, `b = g b'` with `P = (g)`, `g ≠ 0`; `span_eq_mul_coprimePart`:
  `(a, b) = P · coprimePart`; `coprimePart_ne_bot`.
-/

namespace BezoutCounterexample

variable {A : SmoothGCDDomain}

/-- `P` is the least principal ideal containing `(a, b)` (the ideal of a gcd). -/
def IsGcdIdeal (a b : A) (P : Ideal A) : Prop :=
  P.IsPrincipal ∧ Ideal.span {a, b} ≤ P ∧
    ∀ Q : Ideal A, Q.IsPrincipal → Ideal.span {a, b} ≤ Q → P ≤ Q

/-- **The gcd ideal exists and is unique.** -/
theorem existsUnique_gcdIdeal (a b : A) : ∃! P : Ideal A, IsGcdIdeal a b P := by
  obtain ⟨g, hga, hgb, hg⟩ := A.hasGcd a b
  refine ⟨Ideal.span {g}, ⟨⟨⟨g, rfl⟩⟩, ?_, ?_⟩, fun P hP => le_antisymm (hP.2.2 _ ⟨⟨g, rfl⟩⟩ ?_) ?_⟩
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.mem_span_singleton.2 hga
    · exact Ideal.mem_span_singleton.2 hgb
  · rintro Q ⟨⟨q, rfl⟩⟩ hQ
    have hqa : q ∣ a := Ideal.mem_span_singleton.1 (hQ (Ideal.subset_span (by simp)))
    have hqb : q ∣ b := Ideal.mem_span_singleton.1 (hQ (Ideal.subset_span (by simp)))
    rw [Ideal.submodule_span_eq, Ideal.span_singleton_le_span_singleton]
    exact hg q hqa hqb
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.mem_span_singleton.2 hga
    · exact Ideal.mem_span_singleton.2 hgb
  · obtain ⟨⟨p, hp⟩⟩ := hP.1
    have hp' : P = Ideal.span {p} := hp
    have hpa : p ∣ a := Ideal.mem_span_singleton.1 (hp' ▸ hP.2.1 (Ideal.subset_span (by simp)))
    have hpb : p ∣ b := Ideal.mem_span_singleton.1 (hp' ▸ hP.2.1 (Ideal.subset_span (by simp)))
    rw [hp', Ideal.span_singleton_le_span_singleton]
    exact hg p hpa hpb

/-- The coprime part `(a, b) : P`, to be applied to the gcd ideal. -/
def coprimePart (a b : A) (P : Ideal A) : Ideal A :=
  (Ideal.span {a, b}).colon (P : Set A)

/-- **The coprime part is `(a', b')`** for every factorisation `a = g a'`, `b = g b'` with
`P = (g)`, `g ≠ 0`. -/
theorem coprimePart_eq_span {a b : A} {P : Ideal A} {g a' b' : A} (ha : a = g * a')
    (hb : b = g * b') (hg : P = Ideal.span {g}) (hg0 : g ≠ 0) :
    coprimePart a b P = Ideal.span {a', b'} := by
  ext x
  rw [coprimePart, Submodule.mem_colon, hg]
  constructor
  · intro h
    have hx := h g (Ideal.mem_span_singleton_self g)
    rw [smul_eq_mul, Ideal.mem_span_pair] at hx
    obtain ⟨u, v, huv⟩ := hx
    rw [Ideal.mem_span_pair]
    refine ⟨u, v, mul_left_cancel₀ hg0 ?_⟩
    rw [mul_comm g x, ← huv, ha, hb]
    ring
  · intro h s hs
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    rw [Ideal.mem_span_pair] at h
    obtain ⟨u, v, rfl⟩ := h
    rw [smul_eq_mul, Ideal.mem_span_pair]
    exact ⟨c * u, c * v, by rw [ha, hb]; ring⟩

/-- The generator of a gcd ideal divides `a` and `b`, and is nonzero if `b ≠ 0`. -/
theorem IsGcdIdeal.exists_gen {a b : A} {P : Ideal A} (hP : IsGcdIdeal a b P) (hb : b ≠ 0) :
    ∃ g a' b' : A, a = g * a' ∧ b = g * b' ∧ P = Ideal.span {g} ∧ g ≠ 0 := by
  obtain ⟨⟨g, hg⟩⟩ := hP.1
  have hg' : P = Ideal.span {g} := hg
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton.1
    (hg' ▸ hP.2.1 (Ideal.subset_span (show a ∈ ({a, b} : Set A) by simp)))
  obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton.1
    (hg' ▸ hP.2.1 (Ideal.subset_span (show b ∈ ({a, b} : Set A) by simp)))
  refine ⟨g, a', b', ha', hb', hg', ?_⟩
  rintro rfl
  rw [zero_mul] at hb'
  exact hb hb'

/-- **`(a, b) = P · coprimePart`** for the gcd ideal `P` (`b ≠ 0`). -/
theorem span_eq_mul_coprimePart {a b : A} {P : Ideal A} (hP : IsGcdIdeal a b P) (hb : b ≠ 0) :
    Ideal.span {a, b} = P * coprimePart a b P := by
  obtain ⟨g, a', b', ha, hb', hg, hg0⟩ := hP.exists_gen hb
  rw [coprimePart_eq_span ha hb' hg hg0, hg, Ideal.span_mul_span, Set.singleton_mul,
    Set.image_pair, ← ha, ← hb']

/-- The coprime part is nonzero (`b ≠ 0`). -/
theorem coprimePart_ne_bot {a b : A} {P : Ideal A} (hP : IsGcdIdeal a b P) (hb : b ≠ 0) :
    coprimePart a b P ≠ ⊥ := by
  obtain ⟨g, a', b', ha, hb', hg, hg0⟩ := hP.exists_gen hb
  rw [coprimePart_eq_span ha hb' hg hg0]
  intro h
  have hmem : b' ∈ (Ideal.span {a', b'} : Ideal A) := Ideal.subset_span (by simp)
  rw [h, Ideal.mem_bot] at hmem
  rw [hb', hmem, mul_zero] at hb
  exact hb rfl

end BezoutCounterexample
