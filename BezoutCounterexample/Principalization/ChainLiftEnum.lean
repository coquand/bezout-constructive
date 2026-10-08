import Mathlib
import BezoutCounterexample.Constructive.NoethBar

/-!
# An explicit enumeration of presented rings (Task A, C1)

`enumPoly N : ℕ → ℚ[Y₀ … Y_{N-1}]` decodes `k` as a list of (exponent list, coefficient) pairs
(`Encodable` on `List (List ℕ × ℚ)`) and sums the corresponding terms; `enumQuo L` enumerates pairs
of elements of `ℚ[Y]/(L)` through `Nat.unpair`. Both are surjective. This replaces
`Construction.chooseSurj` (`Classical.choose` of `exists_surjective_nat`) for presented stages.
-/

namespace BezoutCounterexample

open MvPolynomial Constructive

/-- The term `q · ∏ᵢ Yᵢ^{e i}` of an (exponent list, coefficient) pair. -/
noncomputable def termOf {N : ℕ} (t : List ℕ × ℚ) : MvPolynomial (Fin N) ℚ :=
  C t.2 * ∏ i : Fin N, X i ^ t.1.getD i 0

/-- The polynomial of a list of terms. -/
noncomputable def polyOf {N : ℕ} (l : List (List ℕ × ℚ)) : MvPolynomial (Fin N) ℚ :=
  (l.map termOf).sum

/-- **An explicit enumeration of `ℚ[Y₀ … Y_{N-1}]`.** -/
noncomputable def enumPoly (N : ℕ) (k : ℕ) : MvPolynomial (Fin N) ℚ :=
  match Encodable.decode (α := List (List ℕ × ℚ)) k with
  | some l => polyOf l
  | none => 0

lemma enumPoly_encode {N : ℕ} (l : List (List ℕ × ℚ)) :
    enumPoly N (Encodable.encode l) = polyOf l := by
  simp [enumPoly, Encodable.encodek]

lemma polyOf_append {N : ℕ} (l l' : List (List ℕ × ℚ)) :
    (polyOf (l ++ l') : MvPolynomial (Fin N) ℚ) = polyOf l + polyOf l' := by
  simp [polyOf]

lemma termOf_monomial {N : ℕ} (s : Fin N →₀ ℕ) (a : ℚ) :
    (termOf (List.ofFn (fun i => s i), a) : MvPolynomial (Fin N) ℚ) = monomial s a := by
  rw [termOf, monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

theorem enumPoly_surjective (N : ℕ) : Function.Surjective (enumPoly N) := by
  have key : ∀ p : MvPolynomial (Fin N) ℚ, ∃ l : List (List ℕ × ℚ), polyOf l = p := by
    intro p
    induction p using MvPolynomial.induction_on' with
    | monomial s a => exact ⟨[(List.ofFn (fun i => s i), a)], by simp [polyOf, termOf_monomial]⟩
    | add p q hp hq =>
      obtain ⟨l, rfl⟩ := hp
      obtain ⟨l', rfl⟩ := hq
      exact ⟨l ++ l', polyOf_append l l'⟩
  intro p
  obtain ⟨l, rfl⟩ := key p
  exact ⟨Encodable.encode l, enumPoly_encode l⟩

/-- **An explicit enumeration of pairs in `ℚ[Y]/(L)`.** -/
noncomputable def enumQuo {N : ℕ} (L : List (MvPolynomial (Fin N) ℚ)) (k : ℕ) :
    (MvPolynomial (Fin N) ℚ ⧸ lspan L) × (MvPolynomial (Fin N) ℚ ⧸ lspan L) :=
  (Ideal.Quotient.mk _ (enumPoly N k.unpair.1), Ideal.Quotient.mk _ (enumPoly N k.unpair.2))

theorem enumQuo_surjective {N : ℕ} (L : List (MvPolynomial (Fin N) ℚ)) :
    Function.Surjective (enumQuo L) := by
  rintro ⟨x, y⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨i, rfl⟩ := enumPoly_surjective N p
  obtain ⟨j, rfl⟩ := enumPoly_surjective N q
  exact ⟨Nat.pair i j, by simp [enumQuo, Nat.unpair_pair]⟩

end BezoutCounterexample
