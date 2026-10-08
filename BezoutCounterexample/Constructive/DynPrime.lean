import BezoutCounterexample.Constructive.PresentedOps
import BezoutCounterexample.Constructive.Colon

/-!
# Dynamical primes (D5; `docs/d5-plan.md`, step 2)

An explicitly generated ideal `𝔭 = (P)` of a presented ring is used *as if* its radical were prime.
When a proof needs `ab ∈ √𝔭 → a ∈ √𝔭 ∨ b ∈ √𝔭`, the two memberships are decided; if both fail,
`√𝔭 = √(𝔭 + (a)) ∩ √(𝔭 + (b))` with both pieces strictly larger. No factorisation, no primary
decomposition, no radical computation: only radical *membership* is decided.

* `InRad P x`: `x ∈ √(P)`, i.e. `xⁿ ∈ (P)` for some `n`.
* `isNilpotent_dec`: nilpotency is decidable in a presented ring (Rabinowitsch: `b` is nilpotent iff
  `1 ∈ (1 - bX)` in `B[X]`, decided by `HasPres.mem_dec`).
* `HasPres.inRad_dec`: radical membership is decidable (`b = x mod (P)` in `A ⧸ (P)`).
* `inRad_split`: `√(P) = √(P, a) ∩ √(P, b)` when `ab ∈ √(P)`.
* `dynPrime`: `a ∈ √𝔭`, or `b ∈ √𝔭`, or a proper split.

The pieces `(P, a)`, `(P, b)` of `inRad_split` are not radical. When the ideal itself (not its
radical) matters (Nakayama-type arguments, generators for presentations), use the **radical
split** instead: for `(P)` radical, `ab ∈ (P)`, `a, b ∉ (P)`,

* `(P) = (P : a) ∩ (P : (P : a))` (`colon_split`), both pieces radical (`isRadL_of_colon`),
  computed by `HasPres.exists_colon`, and strictly larger: `b ∈ (P : a)`, `a ∈ (P : (P : a))`.
* `dynPrimeRad`: `a ∈ (P)`, or `b ∈ (P)`, or such a split.
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open Polynomial

variable {A : Type*} [CommRing A]

/-- `x ∈ √(P)`. -/
def InRad (P : List A) (x : A) : Prop := ∃ n : ℕ, x ^ n ∈ lspan P

lemma inRad_iff_isNilpotent (P : List A) (x : A) :
    InRad P x ↔ IsNilpotent (Ideal.Quotient.mk (lspan P) x) := by
  refine exists_congr fun n => ?_
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]

/-- Rabinowitsch: `b` is nilpotent iff `1 - bX` generates `(1)` in `B[X]`. -/
lemma isNilpotent_iff_one_mem {B : Type*} [CommRing B] (b : B) :
    IsNilpotent b ↔ (1 : B[X]) ∈ lspan [1 - C b * X] := by
  rw [lspan_singleton, ← Ideal.eq_top_iff_one, Ideal.span_singleton_eq_top]
  constructor
  · intro hb
    obtain ⟨n, hn⟩ := hb
    exact IsNilpotent.isUnit_one_sub ⟨n, by rw [mul_pow, ← C_pow, hn, C_0, zero_mul]⟩
  · intro hu
    have := (coeff_isUnit_isNilpotent_of_isUnit hu).2 1 one_ne_zero
    rw [coeff_sub, coeff_one, coeff_C_mul_X, ite_eq_right_iff.2 (fun h => absurd h one_ne_zero),
      ite_eq_left_iff.2 (fun h => absurd rfl h), zero_sub] at this
    exact neg_neg b ▸ this.neg

/-- **Nilpotency is decidable** in a presented ring. -/
theorem isNilpotent_dec {B : Type*} [CommRing B] (h : HasPres B) (b : B) :
    IsNilpotent b ∨ ¬ IsNilpotent b := by
  rw [isNilpotent_iff_one_mem]
  exact h.polynomial.mem_dec _ _

/-- **Radical membership is decidable** for explicitly generated ideals of a presented ring. -/
theorem HasPres.inRad_dec (h : HasPres A) (P : List A) (x : A) : InRad P x ∨ ¬ InRad P x := by
  rw [inRad_iff_isNilpotent]
  exact isNilpotent_dec (h.quotient P) _

lemma mem_lspan_append_singleton {P : List A} {a x : A} (hx : x ∈ lspan (P ++ [a])) :
    ∃ p ∈ lspan P, ∃ r : A, x = p + r * a := by
  have hs : {y | y ∈ P ++ [a]} = {y | y ∈ P} ∪ {a} := by
    ext y; simp [List.mem_append, or_comm]
  rw [lspan, hs, Ideal.span_union, Submodule.mem_sup] at hx
  obtain ⟨p, hp, q, hq, rfl⟩ := hx
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hq
  exact ⟨p, hp, r, rfl⟩

lemma lspan_le_append (P Q : List A) : lspan P ≤ lspan (P ++ Q) :=
  Ideal.span_mono fun _ hy => List.mem_append_left Q hy

lemma InRad.mono {P : List A} (Q : List A) {x : A} (h : InRad P x) : InRad (P ++ Q) x :=
  let ⟨n, hn⟩ := h; ⟨n, lspan_le_append P Q hn⟩

lemma inRad_append_self (P : List A) (a : A) : InRad (P ++ [a]) a :=
  ⟨1, by rw [pow_one]; exact Ideal.subset_span (List.mem_append_right P (List.mem_singleton_self a))⟩

/-- **The splitting**: if `ab ∈ √(P)` then `√(P) = √(P, a) ∩ √(P, b)`. -/
theorem inRad_split {P : List A} {a b : A} (hab : InRad P (a * b)) (x : A) :
    InRad P x ↔ InRad (P ++ [a]) x ∧ InRad (P ++ [b]) x := by
  refine ⟨fun h => ⟨h.mono _, h.mono _⟩, fun ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ => ?_⟩
  obtain ⟨p, hp, r, hr⟩ := mem_lspan_append_singleton hn
  obtain ⟨q, hq, s, hs⟩ := mem_lspan_append_singleton hm
  rw [inRad_iff_isNilpotent] at hab ⊢
  have hp0 : Ideal.Quotient.mk (lspan P) p = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hp
  have hq0 : Ideal.Quotient.mk (lspan P) q = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hq
  have key : Ideal.Quotient.mk (lspan P) x ^ (n + m) =
      Ideal.Quotient.mk (lspan P) (r * s) * Ideal.Quotient.mk (lspan P) (a * b) := by
    rw [pow_add, ← map_pow, ← map_pow, hr, hs, map_add, map_add, hp0, hq0, zero_add, zero_add,
      ← map_mul, ← map_mul]
    congr 1; ring
  refine IsNilpotent.of_pow (m := n + m) ?_
  rw [key, mul_comm]
  exact (Commute.all _ _).isNilpotent_mul_right hab

/-- **Dynamical primality** of `√(P)`, decided in a presented ring. -/
theorem dynPrime (h : HasPres A) (P : List A) {a b : A} (hab : InRad P (a * b)) :
    InRad P a ∨ InRad P b ∨
      (¬ InRad P a ∧ ¬ InRad P b ∧ ∀ x, InRad P x ↔ InRad (P ++ [a]) x ∧ InRad (P ++ [b]) x) := by
  rcases h.inRad_dec P a with ha | ha
  · exact Or.inl ha
  rcases h.inRad_dec P b with hb | hb
  · exact Or.inr (Or.inl hb)
  exact Or.inr (Or.inr ⟨ha, hb, inRad_split hab⟩)

/-- `(P)` is radical. -/
def IsRadL (P : List A) : Prop := ∀ (x : A) (n : ℕ), x ^ n ∈ lspan P → x ∈ lspan P

/-- A colon of a radical ideal is radical. -/
lemma isRadL_of_colon {P J L : List A} (hP : IsRadL P)
    (hL : ∀ x, x ∈ lspan L ↔ ∀ y ∈ lspan J, x * y ∈ lspan P) : IsRadL L := by
  intro x n hx
  rw [hL] at hx ⊢
  intro y hy
  have h := hx y hy
  cases n with
  | zero => rw [pow_zero, one_mul] at h; exact Ideal.mul_mem_left _ x h
  | succ n =>
    refine hP _ (n + 1) ?_
    rw [mul_pow, pow_succ y, ← mul_assoc, mul_comm _ y, ← mul_assoc, mul_comm y]
    exact Ideal.mul_mem_right _ _ h

/-- **The radical split**: `(P) = (P : a) ∩ (P : (P : a))` for `(P)` radical. -/
lemma colon_split {P L₁ L₂ : List A} {a : A} (hP : IsRadL P)
    (h₁ : ∀ x, x ∈ lspan L₁ ↔ ∀ y ∈ lspan [a], x * y ∈ lspan P)
    (h₂ : ∀ x, x ∈ lspan L₂ ↔ ∀ y ∈ lspan L₁, x * y ∈ lspan P) (x : A) :
    x ∈ lspan P ↔ x ∈ lspan L₁ ∧ x ∈ lspan L₂ := by
  refine ⟨fun hx => ⟨(h₁ x).2 fun y _ => Ideal.mul_mem_right _ _ hx,
    (h₂ x).2 fun y _ => Ideal.mul_mem_right _ _ hx⟩, fun ⟨hx₁, hx₂⟩ => ?_⟩
  exact hP x 2 (by rw [sq]; exact (h₂ x).1 hx₂ x hx₁)

/-- **Dynamical primality** of a radical ideal, with radical pieces. -/
theorem dynPrimeRad (h : HasPres A) {P : List A} (hP : IsRadL P) {a b : A}
    (hab : a * b ∈ lspan P) :
    a ∈ lspan P ∨ b ∈ lspan P ∨
      (a ∉ lspan P ∧ b ∉ lspan P ∧ ∃ L₁ L₂ : List A, IsRadL L₁ ∧ IsRadL L₂ ∧
        lspan P ≤ lspan L₁ ∧ lspan P ≤ lspan L₂ ∧ b ∈ lspan L₁ ∧ a ∈ lspan L₂ ∧
        ∀ x, x ∈ lspan P ↔ x ∈ lspan L₁ ∧ x ∈ lspan L₂) := by
  rcases h.mem_dec P a with ha | ha
  · exact Or.inl ha
  rcases h.mem_dec P b with hb | hb
  · exact Or.inr (Or.inl hb)
  obtain ⟨L₁, h₁⟩ := h.exists_colon P [a]
  obtain ⟨L₂, h₂⟩ := h.exists_colon P L₁
  have hs := colon_split hP h₁ h₂
  refine Or.inr (Or.inr ⟨ha, hb, L₁, L₂, isRadL_of_colon hP h₁, isRadL_of_colon hP h₂,
    fun x hx => ((hs x).1 hx).1, fun x hx => ((hs x).1 hx).2, (h₁ b).2 fun y hy => ?_,
    (h₂ a).2 fun y hy => ?_, hs⟩)
  · rw [lspan_singleton] at hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    rw [mul_left_comm, mul_comm b a]; exact Ideal.mul_mem_left _ c hab
  · rw [mul_comm]; exact (h₁ y).1 hy a (by rw [lspan_singleton]; exact Ideal.mem_span_singleton_self a)

end BezoutCounterexample.Constructive
