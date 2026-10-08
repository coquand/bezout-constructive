import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesRowsCongr

/-!
# Zero tests at a point of `A` (Task B, Rees layer S6, §13 step 3)

The point argument chooses an open by zero tests at a point `q` of `A` (`Pt.dec`). Each step is one
identity `N·x ≡ Σ uₛ hₛ` (or a partition of `1`, of `gᴹ`) evaluated at `q`: a nonzero left side
gives a nonzero `hₛ(q)`.

* `exists_ne_of_sum_ne`: a nonzero finite sum has a nonzero term (decided);
* `exists_ne_of_cover`: `N·x − Σ uₛ hₛ ∈ (G)`, `N > 0`, `x(q) ≠ 0` ⇒ some `hₛ(q) ≠ 0`;
* `SmoothCert.exists_piece_ne`: some piece of `A`'s certificate is nonzero at `q`;
* `exists_ne_of_one`, `exists_ne_of_part`: the chart cover `i + Σ f g = 1` and the partition
  `gᴹ = Σ β c + Σ ω a`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive

set_option linter.unusedSectionVars false

/-- **A nonzero finite sum has a nonzero term**, decided in the field. -/
lemma exists_ne_of_sum_ne {K : Type*} [Field K] (dec : ∀ x : K, x = 0 ∨ x ≠ 0) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → K) (h : ∑ i ∈ s, f i ≠ 0) : ∃ i ∈ s, f i ≠ 0 := by
  rcases finset_exists_or_forall (P := fun i => f i ≠ 0)
      (fun i => (dec (f i)).elim (fun h0 => Or.inr fun h' => h' h0) Or.inl) s with h' | hall
  · exact h'
  · exact absurd (Finset.sum_eq_zero fun i hi => (dec (f i)).resolve_right (hall i hi)) h

variable {A : Type} [CommRing A] [Algebra ℚ A] {m kc l : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)

/-- **A cover identity at a point.** -/
lemma exists_ne_of_cover (q : Pt A) {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} (hN : 0 < N)
    (x : MvPolynomial (Fin (m + (kc + l))) ℤ) (u h : ι → MvPolynomial (Fin (m + (kc + l))) ℤ)
    (hid : (N : MvPolynomial (Fin (m + (kc + l))) ℤ) * x - ∑ s, u s * h s ∈ lspan G)
    (hx : qHom G e q x ≠ 0) : ∃ s, qHom G e q (h s) ≠ 0 := by
  have := algebraRat.charZero q.L
  have h0 : qHom G e q ((N : MvPolynomial (Fin (m + (kc + l))) ℤ) * x - ∑ s, u s * h s) = 0 := by
    rw [qHom_apply, toAZ_eq_zero_of_mem G e hid, map_zero]
  rw [map_sub, map_sum, sub_eq_zero] at h0
  have hne : ∑ s, qHom G e q (u s * h s) ≠ 0 := by
    rw [← h0, map_mul, map_natCast]
    exact mul_ne_zero (Nat.cast_ne_zero.2 hN.ne') hx
  obtain ⟨s, -, hs⟩ := exists_ne_of_sum_ne q.dec Finset.univ _ hne
  exact ⟨s, fun h' => hs (by rw [map_mul, h', mul_zero])⟩

/-- **Some piece of `A`'s certificate is nonzero at a point.** -/
lemma SmoothCert.exists_piece_ne (hG : SmoothCert m (kc + l) G) (q : Pt A) :
    ∃ j, qHom G e q (hG.P j).h ≠ 0 := by
  have := algebraRat.charZero q.L
  refine exists_ne_of_cover G e q hG.hC 1 hG.u (fun j => (hG.P j).h) (by rw [mul_one]; exact hG.cover) ?_
  rw [map_one]; exact one_ne_zero

/-- **The chart cover at a point**: if `i(q) = 0`, some `gₖ(q) ≠ 0`. -/
lemma exists_ne_of_one (q : Pt A) {K : ℕ} (i : A) (f g : Fin K → A) (one : i + ∑ k, f k * g k = 1)
    (hi : q.z i = 0) : ∃ k, q.z (g k) ≠ 0 := by
  have h1 : ∑ k, q.z (f k * g k) ≠ 0 := by
    have h2 := congrArg q.z one
    rw [map_add, hi, zero_add, map_sum, map_one] at h2
    rw [h2]; exact one_ne_zero
  obtain ⟨k, -, hk⟩ := exists_ne_of_sum_ne q.dec Finset.univ _ h1
  exact ⟨k, fun h' => hk (by rw [map_mul, h', mul_zero])⟩

/-- **The partition at a point**: if `g(q) ≠ 0` and all `a_q(q) = 0`, some `c_τ(q) ≠ 0`. -/
lemma exists_ne_of_part (q : Pt A) {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ} (g : A) (M : ℕ)
    (β c : ι → A) (ω a : Fin K → A) (hpart : g ^ M = ∑ τ, β τ * c τ + ∑ q, ω q * a q)
    (hg : q.z g ≠ 0) (ha : ∀ i, q.z (a i) = 0) : ∃ τ, q.z (c τ) ≠ 0 := by
  have h1 : ∑ τ, q.z (β τ * c τ) ≠ 0 := by
    have h2 := congrArg q.z hpart
    rw [map_pow, map_add, map_sum, map_sum] at h2
    simp only [map_mul, ha, mul_zero, Finset.sum_const_zero, add_zero] at h2
    simp only [map_mul]
    rw [← h2]
    exact pow_ne_zero _ hg
  obtain ⟨τ, -, hτ⟩ := exists_ne_of_sum_ne q.dec Finset.univ _ h1
  exact ⟨τ, fun h' => hτ (by rw [map_mul, h', mul_zero])⟩

/-- A positive integer times a nonzero value. -/
lemma natCast_mul_ne (q : Pt A) {c : ℕ} (hc : 0 < c) {x : A} (hx : q.z x ≠ 0) :
    q.z ((c : A) * x) ≠ 0 := by
  have := algebraRat.charZero q.L
  rw [map_mul, map_natCast]
  exact mul_ne_zero (Nat.cast_ne_zero.2 hc.ne') hx

end BezoutCounterexample.Principalization
