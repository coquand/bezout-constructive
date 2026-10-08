import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Ideal.Operations

/-!
# The exceptional divisor of the Rees algebra, prime-or-split (D5; `docs/d5-plan.md`, step 3)

Constructive form of `Principalization.span_s_isPrime`, stated on Laurent polynomials so that it
does not depend on `ReesAlg`. `F : ℤ → Ideal B` is multiplicative with `F j = ⊤` for `j ≤ 0`; `p` is
in the Rees algebra if `p_j ∈ F_j` for all `j`, and in `(s)` (`s = T⁻¹`) if `p_j ∈ F_{j+1}` for all
`j` (`Principalization.mem_span_s_iff`).

The graded-domain property is an abstract conclusion `Q` (in the D5 use: a split of `(P)`, from
`gr_dyn`): `hgr` says that two homogeneous elements of exact degrees `a`, `b` with product in
`F_{a+b+1}` give `Q`. Membership in the `F_j` is assumed decidable (`hdec`).

`rees_s_dyn`: if `pq ∈ (s)` then `p ∈ (s)`, or `q ∈ (s)`, or `Q`. The minimal bad indices of the
classical proof are found by a finite search below a bound on the support (`first_bad`), using
`hdec`, so the proof is constructive.
-/

namespace BezoutCounterexample.Constructive

open LaurentPolynomial

/-- **First bad index** below `N`, by finite search. -/
lemma first_bad (good : ℕ → Prop) (hdec : ∀ k, good k ∨ ¬ good k) :
    ∀ N : ℕ, (∀ k < N, good k) ∨ ∃ k < N, ¬ good k ∧ ∀ i < k, good i
  | 0 => Or.inl fun k hk => absurd hk (Nat.not_lt_zero k)
  | N + 1 => by
    rcases first_bad good hdec N with hall | ⟨k, hk, hbad, hbelow⟩
    · rcases hdec N with hN | hN
      · exact Or.inl fun k hk => (Nat.lt_succ_iff_lt_or_eq.1 hk).elim (hall k) (· ▸ hN)
      · exact Or.inr ⟨N, Nat.lt_succ_self N, hN, hall⟩
    · exact Or.inr ⟨k, Nat.lt_succ_of_lt hk, hbad, hbelow⟩

variable {B : Type*} [CommRing B] (F : ℤ → Ideal B)

/-- A Laurent polynomial is in `(s)`, or has a first index `j₀ ≥ 0` with `p_{j₀} ∉ F_{j₀+1}`. -/
lemma good_or_first_bad (hneg : ∀ j : ℤ, j ≤ 0 → F j = ⊤)
    (hdec : ∀ (j : ℤ) (x : B), x ∈ F j ∨ x ∉ F j) (p : B[T;T⁻¹]) :
    (∀ j, p.coeff j ∈ F (j + 1)) ∨
      ∃ a : ℕ, p.coeff a ∉ F (a + 1) ∧ ∀ j : ℤ, j < a → p.coeff j ∈ F (j + 1) := by
  -- a bound on the support
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j : ℤ, (N : ℤ) ≤ j → p.coeff j = 0 := by
    refine ⟨p.coeff.support.sup Int.toNat + 1, fun j hj => ?_⟩
    rcases Finset.decidableMem j p.coeff.support with h | h
    · exact Finsupp.notMem_support_iff.1 h
    · have hle : j.toNat ≤ p.coeff.support.sup Int.toNat := Finset.le_sup (f := Int.toNat) h
      have h2 : (((p.coeff.support.sup Int.toNat + 1 : ℕ)) : ℤ) ≤ (j.toNat : ℤ) :=
        hj.trans (Int.self_le_toNat j)
      have h3 : p.coeff.support.sup Int.toNat + 1 ≤ j.toNat := by exact_mod_cast h2
      exact absurd (h3.trans hle) (Nat.not_succ_le_self _)
  have hlow : ∀ j : ℤ, j < 0 → p.coeff j ∈ F (j + 1) := fun j hj => by
    rw [hneg _ (Int.add_one_le_of_lt hj)]; trivial
  rcases first_bad (fun k : ℕ => p.coeff k ∈ F (k + 1)) (fun k => hdec _ _) N with
    hall | ⟨a, -, hbad, hbelow⟩
  · refine Or.inl fun j => ?_
    rcases lt_or_ge j 0 with h | h
    · exact hlow j h
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rcases lt_or_ge k N with hk | hk
    · exact hall k hk
    · rw [hN _ (by exact_mod_cast hk)]; exact zero_mem _
  · refine Or.inr ⟨a, hbad, fun j hj => ?_⟩
    rcases lt_or_ge j 0 with h | h
    · exact hlow j h
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    exact hbelow k (by exact_mod_cast hj)

/-- **The exceptional divisor is prime, or `Q`.** -/
theorem rees_s_dyn (hmul : ∀ a b, F a * F b ≤ F (a + b)) (hneg : ∀ j : ℤ, j ≤ 0 → F j = ⊤)
    (hdec : ∀ (j : ℤ) (x : B), x ∈ F j ∨ x ∉ F j) {Q : Prop}
    (hgr : ∀ (a b : ℕ) (x y : B), x ∈ F a → x ∉ F (a + 1) → y ∈ F b → y ∉ F (b + 1) →
      x * y ∈ F ((a + b : ℕ) + 1) → Q)
    {p q : B[T;T⁻¹]} (hp : ∀ j, p.coeff j ∈ F j) (hq : ∀ j, q.coeff j ∈ F j)
    (hpq : ∀ j, (p * q).coeff j ∈ F (j + 1)) :
    (∀ j, p.coeff j ∈ F (j + 1)) ∨ (∀ j, q.coeff j ∈ F (j + 1)) ∨ Q := by
  rcases good_or_first_bad F hneg hdec p with hp' | ⟨a, hpa, hbelow_p⟩
  · exact Or.inl hp'
  rcases good_or_first_bad F hneg hdec q with hq' | ⟨b, hqb, hbelow_q⟩
  · exact Or.inr (Or.inl hq')
  refine Or.inr (Or.inr (hgr a b _ _ (hp a) hpa (hq b) hqb ?_))
  -- the coefficient of `pq` in degree `a + b`
  set j₀ : ℤ := (a : ℤ) with hj₀
  set l₀ : ℤ := (b : ℤ) with hl₀
  have hcoeff := hpq (j₀ + l₀)
  have hexp : (p * q).coeff (j₀ + l₀) =
      ∑ i ∈ p.coeff.support, p.coeff i * q.coeff (-i + (j₀ + l₀)) := by
    rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
  have hrest : ∀ i, i ≠ j₀ → p.coeff i * q.coeff (-i + (j₀ + l₀)) ∈ F (j₀ + l₀ + 1) := by
    intro i hi
    rcases lt_or_gt_of_ne hi with h | h
    · have := hmul _ _ (Ideal.mul_mem_mul (hbelow_p i h) (hq (-i + (j₀ + l₀))))
      convert this using 2; ring
    · have := hmul _ _ (Ideal.mul_mem_mul (hp i) (hbelow_q (-i + (j₀ + l₀)) (by
        have := Int.add_lt_add_right (Int.neg_lt_neg h) (j₀ + l₀)
        rwa [show -j₀ + (j₀ + l₀) = l₀ by ring] at this)))
      convert this using 2; ring
  have hmain : p.coeff j₀ * q.coeff l₀ ∈ F (j₀ + l₀ + 1) := by
    rcases (Finset.decidableMem j₀ p.coeff.support) with hj | hj
    · -- `p_{j₀} = 0`
      rw [Finsupp.notMem_support_iff.1 hj, zero_mul]; exact zero_mem _
    · rw [hexp, ← Finset.add_sum_erase _ _ hj] at hcoeff
      have hs := Submodule.sum_mem (F (j₀ + l₀ + 1)) (t := p.coeff.support.erase j₀) fun i hi =>
        hrest i (Finset.ne_of_mem_erase hi)
      have := Ideal.sub_mem _ hcoeff hs
      rwa [add_sub_cancel_right, show -j₀ + (j₀ + l₀) = l₀ by ring] at this
  push_cast; exact hmain

end BezoutCounterexample.Constructive
