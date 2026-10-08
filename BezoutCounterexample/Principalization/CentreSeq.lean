import BezoutCounterexample.Principalization.QuotSeq
import BezoutCounterexample.Principalization.ReesVertex

/-!
# The remaining residue-form duality sites from one chain condition

`_Q` copies (hypothesis `QuotSeqCond`, see `QuotSeq.lean`) of the residue-form duality sites
`mem_RF_iff_weight`, `RF_mul_not_mem` (`ReesVertex`) and `gradedCI` (`ReesSmooth`). Kept in a leaf
file to avoid rebuilding the files downstream of `ReesSmooth`. (`mem_span_x_iff`, `span_x_isPrime`
in `Invariant` take `[Fact (QuotSeqCond R)]` directly.)
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing Constructive

section LocalGrQ

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {n : ℕ}
  (c : Chart S n) (hc : c.IsCentred) {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) {d : ℕ} (hd : 0 < d)
  {w : Fin n → ℕ} (hw : ∀ i, (w i : ℚ) = d * e i) (hQ : QuotSeqCond S)
include hc he hd hw hQ

lemma mem_RF_iff_weight_Q (a : ℕ) (z : S) :
    z ∈ c.RF e ((a : ℚ) / d) ↔ ∀ β, Finsupp.weight w β < a → coeff β (c.tau z) = 0 := by
  rw [hc.mem_RF_iff_Q hQ he]
  refine forall_congr' fun β => imp_congr_left ?_
  rw [lam_eq_weight hd hw, div_lt_div_iff_of_pos_right (by exact_mod_cast hd)]
  exact Nat.cast_lt

/-- **The associated graded ring of a weighted filtration is a domain** (initial forms). -/
theorem RF_mul_not_mem_Q [IsDomain (ResidueField S)] {a b : ℕ} {z z' : S}
    (hz : z ∈ c.RF e ((a : ℚ) / d)) (hz1 : z ∉ c.RF e (((a + 1 : ℕ) : ℚ) / d))
    (hz' : z' ∈ c.RF e ((b : ℚ) / d)) (hz'1 : z' ∉ c.RF e (((b + 1 : ℕ) : ℚ) / d)) :
    z * z' ∉ c.RF e (((a + b + 1 : ℕ) : ℚ) / d) := by
  rw [mem_RF_iff_weight_Q c hc he hd hw hQ] at hz hz' hz1 hz'1 ⊢
  push Not at hz1 hz'1 ⊢
  obtain ⟨β, hβ, hβne⟩ := hz1
  obtain ⟨β', hβ', hβ'ne⟩ := hz'1
  have hβa : Finsupp.weight w β = a := by
    by_contra h; exact hβne (hz β (by omega))
  have hβb : Finsupp.weight w β' = b := by
    by_contra h; exact hβ'ne (hz' β' (by omega))
  have hF : wcomp w a (c.tau z) ≠ 0 := fun h => hβne (by
    have := congrArg (coeff β) h
    rwa [coeff_wcomp, ite_eq_left hβa, map_zero] at this)
  have hG : wcomp w b (c.tau z') ≠ 0 := fun h => hβ'ne (by
    have := congrArg (coeff β') h
    rwa [coeff_wcomp, ite_eq_left hβb, map_zero] at this)
  have hmul := wcomp_mul w hz hz'
  rw [← map_mul] at hmul
  have hne : wcomp w (a + b) (c.tau (z * z')) ≠ 0 := by
    rw [hmul]; exact mul_ne_zero hF hG
  by_contra hall
  push Not at hall
  apply hne
  ext γ
  rw [coeff_wcomp, map_zero]
  split_ifs with hγ
  · exact hall γ (by omega)
  · rfl

end LocalGrQ


section GradedCIQ

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {n : ℕ}

/-- **Weighted `GradedCI`**: a weighted-homogeneous combination of monomials in the first `k`
coordinates of weight `j` lies in `𝓕_{(j+1)/d}` only if all its coefficients lie in
`(x₀, …, x_{k-1})`. -/
theorem gradedCI_Q {c : Chart S n} (hc : c.IsCentred) (hQ : QuotSeqCond S) {e : Fin n → ℚ}
    (he : ∀ i, 0 ≤ e i) {k : ℕ}
    (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) {d : ℕ} (hd : 0 < d) {w : Fin n → ℕ}
    (hw : ∀ i, (w i : ℚ) = d * e i) (j : ℕ) (s : Finset (Fin n →₀ ℕ))
    (hs : ∀ α ∈ s, (∀ i : Fin n, k ≤ (i : ℕ) → α i = 0) ∧ Finsupp.weight w α = j)
    (q : (Fin n →₀ ℕ) → S)
    (hmem : ∑ α ∈ s, q α * ∏ i, c.x i ^ α i ∈ c.RF e (((j + 1 : ℕ) : ℚ) / d)) :
    ∀ α ∈ s, q α ∈ Ideal.span (c.x '' {i | (i : ℕ) < k}) := by
  classical
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hlamw : ∀ α : Fin n →₀ ℕ, lam e α = (Finsupp.weight w α : ℚ) / d := by
    intro α
    rw [lam, Finsupp.weight_eq_sum, eq_div_iff hdq.ne']
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, Nat.cast_mul, hw i]; ring
  have hwpos : ∀ i : Fin n, (i : ℕ) < k → 0 < w i := by
    intro i hi
    have h1 := (hsupp i).2 hi
    have h2 := hw i
    have : (0 : ℚ) < w i := by rw [h2]; exact mul_pos hdq (lt_of_le_of_ne (he i) (Ne.symm h1))
    exact_mod_cast this
  intro α₀ hα₀
  rw [hc.mem_span_iff_Q_dec hQ]
  intro β hβ
  -- the coefficient at `α₀ + β` of the combination vanishes
  have hlam : lam e (α₀ + β) < (((j + 1 : ℕ) : ℚ) / d) := by
    rw [lam_add, hlamw α₀, (hs α₀ hα₀).2]
    have hβ0 : lam e β = 0 := by
      rw [lam]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : (i : ℕ) < k
      · rw [hβ i hi, Nat.cast_zero, zero_mul]
      · rw [show e i = 0 by by_contra h; exact hi ((hsupp i).1 h), mul_zero]
    rw [hβ0, add_zero, div_lt_div_iff_of_pos_right hdq]
    exact_mod_cast Nat.lt_succ_self j
  have h0 := hc.coeff_tau_eq_zero_of_mem_RF he hmem (α₀ + β) hlam
  rw [map_sum] at h0
  simp only [map_mul, hc.tau_monomial, map_sum] at h0
  rw [Finset.sum_eq_single α₀] at h0
  · rw [coeff_mul_monomial, ite_eq_left (le_add_right le_rfl), mul_one, add_tsub_cancel_left] at h0
    exact h0
  · intro α hα hne
    rw [coeff_mul_monomial]
    split_ifs with hle
    · exfalso
      apply hne
      -- `α ≤ α₀ + β` with equal weights forces `α = α₀`
      have hle' : α ≤ α₀ := by
        intro i
        by_cases hi : (i : ℕ) < k
        · have := hle i; simp only [Finsupp.add_apply, hβ i hi, add_zero] at this; exact this
        · rw [(hs α hα).1 i (by omega)]; exact Nat.zero_le _
      refine le_antisymm hle' ?_
      by_contra hlt
      have hlt' : α < α₀ := lt_of_le_of_ne hle' (fun h => hlt (h ▸ le_rfl))
      obtain ⟨i, hi⟩ : ∃ i, α i < α₀ i := by
        by_contra h; push Not at h; exact hlt (fun i => h i)
      have hik : (i : ℕ) < k := by
        by_contra h; push Not at h; rw [(hs α₀ hα₀).1 i h] at hi; omega
      have hwt : Finsupp.weight w α < Finsupp.weight w α₀ := by
        rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
        apply Finset.sum_lt_sum
        · intro l _; exact Nat.mul_le_mul_right _ (hle' l)
        · exact ⟨i, Finset.mem_univ _, Nat.mul_lt_mul_of_pos_right hi (hwpos i hik)⟩
      rw [(hs α hα).2, (hs α₀ hα₀).2] at hwt
      exact lt_irrefl _ hwt
    · rfl
  · intro h; exact absurd hα₀ h

end GradedCIQ

end BezoutCounterexample.Principalization
