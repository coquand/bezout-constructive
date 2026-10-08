import BezoutCounterexample.Principalization.Torsor
import BezoutCounterexample.Constructive.DynGr

/-!
# Classical bridge for the D5 graded-domain step (`docs/d5-plan.md`, step 3)

`Constructive.gr_dyn` replaces `compFil_mul_not_mem` by two prime-free hypotheses: torsion-freeness
for non-zero-divisors mod `(P)`, and the valuation property in partition-of-unity form. For the
prime component `𝔭` both follow from `compFil_mul_not_mem` (`compFil_torsionFree`,
`compFil_partition`), and `gr_dyn` gives `compFil_mul_not_mem` back (`compFil_mul_not_mem_of_dyn`;
`RadSplit` is empty for a prime, `not_radSplit_of_isPrime`).

This only checks that the D5 hypotheses are not stronger than the classical statement. For a
radical `(P)` whose components are not separated, the hypotheses must come from the local
structure at every point (step 4).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open Constructive

/-- A prime ideal is not the intersection of two strictly larger ideals. -/
lemma not_radSplit_of_isPrime {B : Type*} [CommRing B] {P : List B} (hP : (lspan P).IsPrime) :
    ¬ RadSplit P := by
  rintro ⟨L₁, L₂, -, -, -, -, ⟨y₁, m₁, n₁⟩, ⟨y₂, m₂, n₂⟩, hsp⟩
  have hm : y₁ * y₂ ∈ lspan P := (hsp _).2 ⟨Ideal.mul_mem_right _ _ m₁, Ideal.mul_mem_left _ _ m₂⟩
  rcases hP.mem_or_mem hm with h | h
  · exact n₁ h
  · exact n₂ h

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hI hmax h𝔭 hd hw in
/-- **Torsion-freeness** of the component filtration, for non-zero-divisors mod `𝔭`. -/
theorem compFil_torsionFree (P : List A) (hP : lspan P = 𝔭) (j : ℕ) (u x : A) (hu : NZDmod P u)
    (hux : u * x ∈ (compFil hI hmax h𝔭 d).F ((j + 1 : ℕ) : ℤ))
    (hx : x ∈ (compFil hI hmax h𝔭 d).F (j : ℤ)) :
    x ∈ (compFil hI hmax h𝔭 d).F ((j + 1 : ℕ) : ℤ) := by
  have h1 : (compFil hI hmax h𝔭 d).F 1 = 𝔭 := by
    rw [compFil_F, show ((1 : ℤ) : ℚ) / d = 1 / d by push_cast; ring,
      compF_one_div hI (IsMaxInvPt.toMax hmax) h𝔭 hd hw]
  have hu𝔭 : u ∉ 𝔭 := fun hu' => h𝔭.1.1.ne_top <| by
    rw [Ideal.eq_top_iff_one, ← hP]; exact hu 1 (by rw [one_mul, hP]; exact hu')
  have hu0 : u ∈ (compFil hI hmax h𝔭 d).F ((0 : ℕ) : ℤ) := by
    rw [Nat.cast_zero, (compFil hI hmax h𝔭 d).zero_eq]; trivial
  have hu1 : u ∉ (compFil hI hmax h𝔭 d).F ((0 + 1 : ℕ) : ℤ) := by
    rw [zero_add, Nat.cast_one, h1]; exact hu𝔭
  by_contra hx1
  exact compFil_mul_not_mem_pt hI hmax h𝔭 hd hw hu0 hu1 hx hx1 (by push_cast at hux ⊢; rwa [zero_add])

include hI hmax h𝔭 hd hw in
/-- **The valuation property in partition-of-unity form.** -/
theorem compFil_partition {a b : ℕ} {x y : A} (hx : x ∈ (compFil hI hmax h𝔭 d).F (a : ℤ))
    (hy : y ∈ (compFil hI hmax h𝔭 d).F (b : ℤ))
    (hxy : x * y ∈ (compFil hI hmax h𝔭 d).F ((a + b + 1 : ℕ) : ℤ)) :
    ∃ g g' : A, g + g' = 1 ∧ g * x ∈ (compFil hI hmax h𝔭 d).F ((a + 1 : ℕ) : ℤ) ∧
      g' * y ∈ (compFil hI hmax h𝔭 d).F ((b + 1 : ℕ) : ℤ) := by
  by_cases hx1 : x ∈ (compFil hI hmax h𝔭 d).F ((a + 1 : ℕ) : ℤ)
  · exact ⟨1, 0, add_zero 1, by rw [one_mul]; exact hx1, by rw [zero_mul]; exact zero_mem _⟩
  by_cases hy1 : y ∈ (compFil hI hmax h𝔭 d).F ((b + 1 : ℕ) : ℤ)
  · exact ⟨0, 1, zero_add 1, by rw [zero_mul]; exact zero_mem _, by rw [one_mul]; exact hy1⟩
  exact absurd hxy (compFil_mul_not_mem_pt hI hmax h𝔭 hd hw hx hx1 hy hy1)

include hI hmax h𝔭 hd hw in
/-- `compFil_mul_not_mem` recovered from `gr_dyn`. -/
theorem compFil_mul_not_mem_of_dyn (hpres : HasPres A) (P : List A) (hP : lspan P = 𝔭)
    {a b : ℕ} {x y : A} (hx : x ∈ (compFil hI hmax h𝔭 d).F (a : ℤ))
    (hx1 : x ∉ (compFil hI hmax h𝔭 d).F ((a + 1 : ℕ) : ℤ))
    (hy : y ∈ (compFil hI hmax h𝔭 d).F (b : ℤ))
    (hy1 : y ∉ (compFil hI hmax h𝔭 d).F ((b + 1 : ℕ) : ℤ)) :
    x * y ∉ (compFil hI hmax h𝔭 d).F ((a + b + 1 : ℕ) : ℤ) := by
  intro hxy
  have hpr : (lspan P).IsPrime := hP ▸ h𝔭.1.1
  have hrad : IsRadL P := fun z n hz => hpr.mem_of_pow_mem n hz
  obtain ⟨g, g', hg, hgx, hgy⟩ := compFil_partition hI hmax h𝔭 hd hw hx hy hxy
  exact not_radSplit_of_isPrime hpr <|
    gr_dyn hpres hrad (fun j => (compFil hI hmax h𝔭 d).F (j : ℤ))
      (compFil_torsionFree hI hmax h𝔭 hd hw P hP) hx hx1 hy hy1 hg hgx hgy

end BezoutCounterexample.Principalization
