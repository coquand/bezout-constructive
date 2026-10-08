import BezoutCounterexample.Principalization.Centre
import BezoutCounterexample.Constructive.XiMin

/-!
# Method 1's minimiser on `Fin n →₀ ℕ`, by a bounded search (Task D, R6)

`exists_min_Xi_pos` is `Centre.exists_min_Xi` for a **decided** candidate set with a first
candidate (from (F2⁺)) and positive head weights. It goes through `Constructive.exists_min_Xi_dec`
(an explicit finite box, decided comparisons of rationals), without `classical` or `Nat.find`.
`lam`, `tailSum`, `Xi` agree with `lamF`, `tailF`, `XiF` on the underlying functions (`rfl`).
-/

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

variable {n : ℕ}

lemma Xi_eq_XiF (e : Fin n → ℚ) (j : ℕ) (β : Fin n →₀ ℕ) : Xi e j β = XiF e j β := rfl

lemma lam_eq_lamF (e : Fin n → ℚ) (β : Fin n →₀ ℕ) : lam e β = lamF e β := rfl

/-- **Method 1's minimiser, positively** (replaces `exists_min_Xi`). -/
theorem exists_min_Xi_pos {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) {j : ℕ}
    (hpos : ∀ i : Fin n, (i : ℕ) < j → 0 < e i) (S : Set (Fin n →₀ ℕ))
    (hS : ∀ β, β ∈ S ∨ β ∉ S) {β₀ : Fin n →₀ ℕ} (h₀ : β₀ ∈ S)
    (hlt : ∀ β ∈ S, lam e β < 1) :
    ∃ β ∈ S, ∀ β' ∈ S, Xi e j β ≤ Xi e j β' := by
  let φ : (Fin n → ℕ) → (Fin n →₀ ℕ) := Finsupp.equivFunOnFinite.symm
  have hφ : ∀ f, ⇑(φ f) = f := fun f => Finsupp.coe_equivFunOnFinite_symm f
  have hφ' : ∀ β : Fin n →₀ ℕ, φ ⇑β = β := fun β => Finsupp.equivFunOnFinite_symm_coe β
  obtain ⟨f, hf, hmin⟩ := exists_min_Xi_dec (S := fun f => φ f ∈ S) he hpos
    (fun f => hS (φ f)) (by rw [hφ']; exact h₀)
    (fun f hf => by have := hlt _ hf; rwa [lam_eq_lamF, hφ] at this)
  refine ⟨φ f, hf, fun β' hβ' => ?_⟩
  rw [Xi_eq_XiF, Xi_eq_XiF, hφ]
  exact hmin β' (by rw [hφ']; exact hβ')

end BezoutCounterexample.Principalization
