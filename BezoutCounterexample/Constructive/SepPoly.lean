import BezoutCounterexample.Constructive.Kronecker
import BezoutCounterexample.Constructive.PresentedOps

/-!
# A separable annihilating polynomial at an explicit point (Task D, R6; roadmap §1.4)

`Chart.recFun` and `Chart.exists_centred` recentre by `minpoly ℚ (residue xᵢ)`, which needs the
residue field to be integral (Zariski, `residueField_isIntegral`) and `minpoly` (a `choose`).
Recentring only needs a `P ∈ ℚ[X]` with `P(a) = 0` and `P'(a) ≠ 0`, and `P = X` when `a = 0`.

* `exists_sep_poly`: for `a` in a finite extension `L/ℚ` with a zero test, such a `P`: an
  annihilating polynomial from finite dimensionality, its Kronecker factorisation
  (`exists_factorisation`), the factor vanishing at `a` found by the zero test in `L`; an
  irreducible polynomial over `ℚ` is separable (characteristic `0`).
* Choice over `Fin n` is `fin_choice` (PresentedOps).
-/

namespace BezoutCounterexample.Constructive

open Polynomial

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- In a field with a zero test, a vanishing product has a vanishing factor. -/
lemma exists_aeval_eq_zero_of_prod (hz : ∀ x : L, x = 0 ∨ x ≠ 0) (a : L) :
    ∀ l : List ℚ[X], aeval a l.prod = 0 → ∃ p ∈ l, aeval a p = 0
  | [], h => by
    letI : Nontrivial L := DivisionRing.toNontrivial
    rw [List.prod_nil, map_one] at h; exact absurd h one_ne_zero
  | p :: l, h => by
    rw [List.prod_cons, map_mul] at h
    rcases hz (aeval a p) with hp | hp
    · exact ⟨p, List.mem_cons_self .., hp⟩
    · obtain ⟨q, hq, hq0⟩ :=
        exists_aeval_eq_zero_of_prod hz a l ((mul_eq_zero.1 h).resolve_left hp)
      exact ⟨q, List.mem_cons_of_mem _ hq, hq0⟩

/-- **A separable annihilating polynomial**, `X` at `0`. -/
theorem exists_sep_poly (hz : ∀ x : L, x = 0 ∨ x ≠ 0) [FiniteDimensional ℚ L] (a : L) :
    ∃ P : ℚ[X], aeval a P = 0 ∧ aeval a (derivative P) ≠ 0 ∧ (a = 0 → P = X) := by
  letI : Nontrivial L := DivisionRing.toNontrivial
  rcases hz a with h0 | h0
  · refine ⟨X, by rw [aeval_X, h0], by rw [derivative_X, map_one]; exact one_ne_zero,
      fun _ => rfl⟩
  · obtain ⟨Q, hQm, hQ⟩ := (Algebra.IsIntegral.of_finite ℚ L).isIntegral a
    obtain ⟨u, l, hu, hirr, hQl⟩ := exists_factorisation hQm.ne_zero
    have hQa : aeval a Q = 0 := by rw [aeval_def]; exact hQ
    have hl : aeval a l.prod = 0 := by
      rw [hQl, map_mul] at hQa
      exact (mul_eq_zero.1 hQa).resolve_left (hu.map (aeval a)).ne_zero
    obtain ⟨p, hp, hpa⟩ := exists_aeval_eq_zero_of_prod hz a l hl
    exact ⟨p, hpa, (hirr p hp).separable.aeval_derivative_ne_zero hpa, fun h => absurd h h0⟩

end BezoutCounterexample.Constructive
