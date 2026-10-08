import BezoutCounterexample.Principalization.DynGrBridge
import BezoutCounterexample.Constructive.DynRees

/-!
# The exceptional divisor, prime-or-split, on the Rees algebra (`docs/d5-plan.md`, step 3)

* `span_s_dyn`: `Constructive.rees_s_dyn` on `ReesAlg Φ` and `(s) = (reesS)`: `pq ∈ (s)` gives
  `p ∈ (s)`, `q ∈ (s)`, or `Q`.
* `span_s_dyn_split`: with `Q = RadSplit P` supplied by `Constructive.gr_dyn` (torsion-freeness for
  non-zero-divisors mod `(P)` and the partition-of-unity valuation property): `(s)` is prime in the
  Rees algebra, or `(P)` splits. Prime-free; the filtration only needs decidable membership.
* `rees_s_prime_of_dyn`: `rees_s_prime` recovered for the prime component (classical decisions,
  no split by `not_radSplit_of_isPrime`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open LaurentPolynomial Constructive

section Generic

variable {B : Type*} [CommRing B] [Algebra ℚ B] (Φ : WFil B) (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
include hneg

omit [Algebra ℚ B] in
/-- `(s) ≠ (1)` when `F_1 ≠ (1)`. -/
lemma span_s_ne_top (h1 : Φ.F 1 ≠ ⊤) : Ideal.span {reesS Φ hneg} ≠ ⊤ := by
  intro htop
  have h1mem : (1 : ReesAlg Φ) ∈ Ideal.span {reesS Φ hneg} := by rw [htop]; trivial
  have := (mem_span_s_iff Φ hneg 1).1 h1mem 0
  rw [show ((1 : ReesAlg Φ) : B[T;T⁻¹]) = 1 from rfl, coeff_one_laurent, ite_eq_left rfl] at this
  exact h1 ((Ideal.eq_top_iff_one _).2 (by simpa using this))

omit [Algebra ℚ B] in
/-- **`(s)` is prime, or `Q`.** -/
theorem span_s_dyn (hdec : ∀ (j : ℤ) (x : B), x ∈ Φ.F j ∨ x ∉ Φ.F j) {Q : Prop}
    (hgr : ∀ (a b : ℕ) (x y : B), x ∈ Φ.F a → x ∉ Φ.F (a + 1) → y ∈ Φ.F b → y ∉ Φ.F (b + 1) →
      x * y ∈ Φ.F ((a + b : ℕ) + 1) → Q)
    {p q : ReesAlg Φ} (hpq : p * q ∈ Ideal.span {reesS Φ hneg}) :
    p ∈ Ideal.span {reesS Φ hneg} ∨ q ∈ Ideal.span {reesS Φ hneg} ∨ Q := by
  rw [mem_span_s_iff] at hpq ⊢
  rw [mem_span_s_iff]
  exact rees_s_dyn Φ.F Φ.mul_le hneg hdec hgr p.2 q.2 hpq

omit [Algebra ℚ B] in
/-- **`(s)` is prime, or `(P)` splits.** -/
theorem span_s_dyn_split (hpres : HasPres B) {P : List B} (hP : IsRadL P)
    (hdec : ∀ (j : ℤ) (x : B), x ∈ Φ.F j ∨ x ∉ Φ.F j)
    (hT : ∀ (j : ℕ) (u x : B), NZDmod P u → u * x ∈ Φ.F ((j + 1 : ℕ) : ℤ) → x ∈ Φ.F (j : ℤ) →
      x ∈ Φ.F ((j + 1 : ℕ) : ℤ))
    (hpart : ∀ (a b : ℕ) (x y : B), x ∈ Φ.F a → y ∈ Φ.F b → x * y ∈ Φ.F ((a + b + 1 : ℕ) : ℤ) →
      ∃ g g' : B, g + g' = 1 ∧ g * x ∈ Φ.F ((a + 1 : ℕ) : ℤ) ∧ g' * y ∈ Φ.F ((b + 1 : ℕ) : ℤ))
    {p q : ReesAlg Φ} (hpq : p * q ∈ Ideal.span {reesS Φ hneg}) :
    p ∈ Ideal.span {reesS Φ hneg} ∨ q ∈ Ideal.span {reesS Φ hneg} ∨ RadSplit P := by
  refine span_s_dyn Φ hneg hdec (fun a b x y hx hx1 hy hy1 hxy => ?_) hpq
  have hxy' : x * y ∈ Φ.F ((a + b + 1 : ℕ) : ℤ) := by push_cast at hxy ⊢; exact hxy
  obtain ⟨g, g', hg, hgx, hgy⟩ := hpart a b x y hx hy hxy'
  exact gr_dyn hpres hP (fun j => Φ.F (j : ℤ)) hT hx (by push_cast; exact hx1) hy
    (by push_cast; exact hy1) hg hgx hgy

end Generic

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hI hmax h𝔭 hd hw in
/-- `rees_s_prime` recovered from `span_s_dyn_split`. -/
theorem rees_s_prime_of_dyn (hpres : HasPres A) (P : List A) (hP : lspan P = 𝔭) :
    (Ideal.span {reesS (compFil hI hmax h𝔭 d)
      (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj)}).IsPrime := by
  classical
  have hpr : (lspan P).IsPrime := hP ▸ h𝔭.1.1
  have hrad : IsRadL P := fun z n hz => hpr.mem_of_pow_mem n hz
  refine ⟨span_s_ne_top _ _ (F_one_ne_top hI hmax h𝔭 hd hw), fun {p q} hpq => ?_⟩
  rcases span_s_dyn_split (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj)
      hpres hrad (fun j x => em _) (compFil_torsionFree hI hmax h𝔭 hd hw P hP)
      (fun a b x y hx hy hxy => compFil_partition hI hmax h𝔭 hd hw hx hy hxy) hpq with
    h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (not_radSplit_of_isPrime hpr)

end BezoutCounterexample.Principalization
