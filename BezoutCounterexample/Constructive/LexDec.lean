import Mathlib

/-!
# Totality of the lexicographic order for bounded supports

`exists_maxInv_C` (`Cover.lean`) takes the minimum of finitely many invariants under `¬¬`, only
because totality of the lexicographic order on `ℕ → ℚ` is not available constructively for
arbitrary sequences (`nn_le_total`). Invariants have bounded support (`ΓN`), and for sequences
vanishing beyond `N` the comparison is a finite search for the first difference, with decidable
comparisons of rationals (`lex_total_bounded`). No `lt_trichotomy`, no `le_total`.
-/

namespace BezoutCounterexample.Constructive

/-- **Lexicographic comparison of boundedly supported rational sequences.** -/
theorem lex_total_bounded {N : ℕ} {v w : ℕ → ℚ} (hv : ∀ i, N ≤ i → v i = 0)
    (hw : ∀ i, N ≤ i → w i = 0) : toLex v ≤ toLex w ∨ toLex w ≤ toLex v := by
  have key : ∀ k n, n + k = N → (∀ j < n, v j = w j) → toLex v ≤ toLex w ∨ toLex w ≤ toLex v := by
    intro k
    induction k with
    | zero =>
      intro n hn h
      have : v = w := funext fun i => by
        rcases Nat.lt_or_ge i n with hi | hi
        · exact h i hi
        · rw [hv i (by omega), hw i (by omega)]
      exact Or.inl (le_of_eq (congrArg toLex this))
    | succ k ih =>
      intro n hn h
      by_cases hlt : v n < w n
      · exact Or.inl (le_of_lt (show toLex v < toLex w from ⟨n, fun j hj => h j hj, hlt⟩))
      by_cases hgt : w n < v n
      · exact Or.inr (le_of_lt (show toLex w < toLex v from
          ⟨n, fun j hj => (h j hj).symm, hgt⟩))
      have heq : v n = w n := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      refine ih (n + 1) (by omega) fun j hj => ?_
      rcases Nat.lt_or_ge j n with hj' | hj'
      · exact h j hj'
      · rw [show j = n by omega]; exact heq
  exact key N 0 (by omega) fun j hj => absurd hj (Nat.not_lt_zero j)

end BezoutCounterexample.Constructive
