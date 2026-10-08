import Mathlib
import BezoutCounterexample.Constructive.ChainLiftGlue

/-!
# Integer presentations (bridge (a) of the chain-lifting strand)

The certificates of `Constructive/ChainLift*` live over `ℤ`; HM's presentations are over `ℚ`.

* `exists_int_mul`: every rational polynomial has a positive integer multiple with integer
  coefficients.
* `intPres G₀`: the relations cleared of denominators; `map_intPres`: they generate the same
  ideal over `ℚ`.
* `exists_int_mem`: an integer polynomial in the rational ideal of a list of integer polynomials has
  a positive integer multiple in the integer ideal.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive

variable {σ : Type*}

/-- `ℤ[Y] → ℚ[Y]`. -/
abbrev toQ : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)

lemma toQ_injective : Function.Injective (toQ (σ := σ)) :=
  MvPolynomial.map_injective _ (RingHom.injective_int _)

/-- **Clearing denominators** of one rational polynomial. -/
theorem exists_int_mul (p : MvPolynomial σ ℚ) :
    ∃ (D : ℕ) (q : MvPolynomial σ ℤ), 0 < D ∧ toQ q = (D : MvPolynomial σ ℚ) * p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, C a.num, a.den_pos, ?_⟩
    rw [map_C, ← map_natCast C, ← C_mul]
    congr 1
    simp only [eq_intCast, Int.cast_natCast]
    rw [mul_comm, Rat.mul_den_eq_num]
  | add p q hp hq =>
    obtain ⟨D, a, hD, ha⟩ := hp
    obtain ⟨D', b, hD', hb⟩ := hq
    refine ⟨D * D', C (D' : ℤ) * a + C (D : ℤ) * b, Nat.mul_pos hD hD', ?_⟩
    rw [map_add, map_mul, map_mul, ha, hb, map_C, map_C]
    simp only [eq_intCast, Int.cast_natCast, ← map_natCast C]
    push_cast
    simp only [map_mul, map_natCast]
    ring
  | mul_X p i hp =>
    obtain ⟨D, a, hD, ha⟩ := hp
    exact ⟨D, a * X i, hD, by rw [map_mul, ha, map_X, mul_assoc]⟩

/-- A rational number times a multiple of its denominator is an integer: `D a = num (D a)`. -/
lemma num_natCast_mul_of_den_dvd {a : ℚ} {D : ℕ} (h : a.den ∣ D) :
    ((((D : ℚ) * a).num : ℤ) : ℚ) = (D : ℚ) * a := by
  obtain ⟨k, rfl⟩ := h
  have : ((a.den * k : ℕ) : ℚ) * a = ((k * a.num : ℤ) : ℚ) := by
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring
  rw [this, Rat.num_intCast]

/-- Clearing denominators of finitely many rational polynomials at once. The multiplier is the
product of all denominators of all coefficients, and the integer polynomials are explicit
(no choice, no decidable equality on `ι`). -/
theorem exists_int_mul_fin {ι : Type*} [Fintype ι] (p : ι → MvPolynomial σ ℚ) :
    ∃ (D : ℕ) (q : ι → MvPolynomial σ ℤ), 0 < D ∧ ∀ i, toQ (q i) = (D : MvPolynomial σ ℚ) * p i := by
  set D : ℕ := ∏ i, ∏ m ∈ (p i).support, ((p i).coeff m).den
  have hdvd : ∀ i, ∀ m ∈ (p i).support, ((p i).coeff m).den ∣ D := fun i m hm =>
    (Finset.dvd_prod_of_mem (fun m => ((p i).coeff m).den) hm).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ m ∈ (p i).support, ((p i).coeff m).den)
        (Finset.mem_univ i))
  refine ⟨D, fun i => ∑ m ∈ (p i).support, monomial m (((D : ℚ) * (p i).coeff m).num),
    Finset.prod_pos fun i _ => Finset.prod_pos fun m _ => Rat.den_pos _, fun i => ?_⟩
  conv_rhs => rw [(p i).as_sum, Finset.mul_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_monomial, ← map_natCast (C : ℚ →+* MvPolynomial σ ℚ), C_mul_monomial]
  congr 1
  exact num_natCast_mul_of_den_dvd (hdvd i m hm)

/-- **Integer multiples of members of an extended ideal.** -/
theorem exists_int_mem (L : List (MvPolynomial σ ℤ)) (Z : MvPolynomial σ ℤ)
    (h : toQ Z ∈ lspan (L.map toQ)) : ∃ D : ℕ, 0 < D ∧ (D : MvPolynomial σ ℤ) * Z ∈ lspan L := by
  classical
  have hspan : lspan (L.map toQ) = Ideal.span (Set.range fun j : Fin L.length => toQ (L.get j)) := by
    show Ideal.span _ = Ideal.span _
    congr 1
    ext x
    simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨j, rfl⟩ := List.get_of_mem ha
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, List.get_mem L j, rfl⟩
  rw [hspan, Ideal.mem_span_range_iff_exists_fun] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨D, b, hD, hb⟩ := exists_int_mul_fin a
  refine ⟨D, hD, ?_⟩
  have : (D : MvPolynomial σ ℤ) * Z = ∑ j, b j * L.get j := by
    apply toQ_injective
    rw [map_mul, map_natCast, ← ha, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hb j, mul_assoc]
  rw [this]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (get_mem_lspan L j)

/-- Uniform integer multiples for finitely many members (induction on the multiset `univ`, no
choice, no decidable equality on `ι`). -/
theorem exists_int_mem_fin (L : List (MvPolynomial σ ℤ)) {ι : Type*} [Fintype ι]
    (Z : ι → MvPolynomial σ ℤ) (h : ∀ i, toQ (Z i) ∈ lspan (L.map toQ)) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, (D : MvPolynomial σ ℤ) * Z i ∈ lspan L := by
  have key : ∀ s : Multiset ι, ∃ D : ℕ, 0 < D ∧ ∀ i ∈ s, (D : MvPolynomial σ ℤ) * Z i ∈ lspan L := by
    intro s
    induction s using Multiset.induction_on with
    | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Multiset.notMem_zero i)⟩
    | cons a s ih =>
      obtain ⟨D, hD, hDs⟩ := ih
      obtain ⟨Da, hDa, hDaZ⟩ := exists_int_mem L (Z a) (h a)
      refine ⟨Da * D, Nat.mul_pos hDa hD, fun i hi => ?_⟩
      rcases Multiset.mem_cons.1 hi with rfl | hi
      · rw [mul_comm Da, Nat.cast_mul, mul_assoc]
        exact Ideal.mul_mem_left _ _ hDaZ
      · rw [Nat.cast_mul, mul_assoc]
        exact Ideal.mul_mem_left _ _ (hDs i hi)
  obtain ⟨D, hD, hDZ⟩ := key Finset.univ.val
  exact ⟨D, hD, fun i => hDZ i (Finset.mem_univ i)⟩

end BezoutCounterexample.Principalization
