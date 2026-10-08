import BezoutCounterexample.Principalization.CentreSeq

/-!
# Weighted ideals over a decided residue field: stability and the graded domain (leaf; (A) A2, A3)

`S` local, `QuotSeqCond S` passed explicitly, residue field decided (`hdec : x ∈ 𝔪 ∨ IsUnit x`; at an
explicit point: `Pt.dec_local`). By `mem_RF_iff_weight_Q`, `z ∈ RF (a/d)` says that the Taylor
coefficients of weight `< a` vanish, each a decided equation in the residue field. Hence:

* `mem_RF_stable`: membership is `¬¬`-stable (a `∀` of decided equations);
* `RF_mul_not_mem_dec`: `RF_mul_not_mem_Q` without `push Not`/`by_contra`: the goal is `False`, so the
  witnesses of non-membership are found under it by the decided coefficient tests.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing Constructive

section LocalGrDec

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {n : ℕ}
  (c : Chart S n) (hc : c.IsCentred) {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) {d : ℕ} (hd : 0 < d)
  {w : Fin n → ℕ} (hw : ∀ i, (w i : ℚ) = d * e i) (hQ : QuotSeqCond S)
  (hdec : ∀ x : S, x ∈ maximalIdeal S ∨ IsUnit x)

include hdec in
/-- A Taylor coefficient is decided. -/
lemma coeff_tau_dec (z : S) (β : Fin n →₀ ℕ) : coeff β (c.tau z) = 0 ∨ coeff β (c.tau z) ≠ 0 := by
  rw [Chart.coeff_tau]
  rcases hdec (c.Dv β z) with h | h
  · exact Or.inl ((residue_eq_zero_iff _).2 h)
  · exact Or.inr fun h' => ((residue_eq_zero_iff _).1 h') |> (notMem_maximalIdeal.2 h)

include hc he hd hw hQ hdec

/-- **Membership in a weighted ideal is `¬¬`-stable** over a decided residue field. -/
lemma mem_RF_stable (a : ℕ) (z : S) (h : ¬¬ z ∈ c.RF e ((a : ℚ) / d)) : z ∈ c.RF e ((a : ℚ) / d) := by
  rw [mem_RF_iff_weight_Q c hc he hd hw hQ] at h ⊢
  intro β hβ
  rcases coeff_tau_dec c hdec z β with h0 | h0
  · exact h0
  · exact absurd (fun hall => h0 (hall β hβ)) h

/-- **The associated graded ring is a domain**, choice-free over a decided residue field. -/
theorem RF_mul_not_mem_dec {a b : ℕ} {z z' : S}
    (hz : z ∈ c.RF e ((a : ℚ) / d)) (hz1 : z ∉ c.RF e (((a + 1 : ℕ) : ℚ) / d))
    (hz' : z' ∈ c.RF e ((b : ℚ) / d)) (hz'1 : z' ∉ c.RF e (((b + 1 : ℕ) : ℚ) / d)) :
    z * z' ∉ c.RF e (((a + b + 1 : ℕ) : ℚ) / d) := by
  intro hzz
  rw [mem_RF_iff_weight_Q c hc he hd hw hQ] at hz hz' hz1 hz'1 hzz
  -- the witness `β` of `z ∉ RF((a+1)/d)`, under the goal `False`
  refine hz1 fun β hβ => (coeff_tau_dec c hdec z β).elim id fun hβne => ?_
  exfalso
  refine hz'1 fun β' hβ' => (coeff_tau_dec c hdec z' β').elim id fun hβ'ne => ?_
  exfalso
  have hβa : Finsupp.weight w β = a := by
    have : ¬ Finsupp.weight w β < a := fun h => hβne (hz β h)
    omega
  have hβb : Finsupp.weight w β' = b := by
    have : ¬ Finsupp.weight w β' < b := fun h => hβ'ne (hz' β' h)
    omega
  have hF : wcomp w a (c.tau z) ≠ 0 := fun h => hβne (by
    have := congrArg (coeff β) h
    rwa [coeff_wcomp, ite_eq_left hβa, map_zero] at this)
  have hG : wcomp w b (c.tau z') ≠ 0 := fun h => hβ'ne (by
    have := congrArg (coeff β') h
    rwa [coeff_wcomp, ite_eq_left hβb, map_zero] at this)
  have hmul := wcomp_mul w hz hz'
  rw [← map_mul] at hmul
  apply mul_ne_zero hF hG
  rw [← hmul]
  ext γ
  rw [coeff_wcomp, map_zero]
  split_ifs with hγ
  · exact hzz γ (by omega)
  · rfl

end LocalGrDec

end BezoutCounterexample.Principalization
