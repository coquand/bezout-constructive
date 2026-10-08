import BezoutCounterexample.Principalization.CentreK

/-!
# Relative order duality with a decidable coordinate set, below `QuotSeq` (R6, leaf)

`Chart.IsCentred.mem_sup_pow_succ` (Duality) case-splits on `∀ i ∈ S, α i = 0` for an arbitrary
`S : Set (Fin n)` (under `classical`) and picks exponents with `choose`; `IsCentred.pow_eq_span`
finds a nonzero exponent by `by_contra`. Twins with `[DecidablePred (· ∈ S)]` (coll-8a's
DualityDec, the part that needs nothing above `CentreK`, split off by coll-7c so that `QuotSeq`
can use it):

* `IsCentred.pow_eq_span_dec` (`Finsupp.ne_iff` instead of `by_contra`);
* `IsCentred.mem_sup_pow_succ_dec` (exponent-indexed linear combination, decided case split);
* `IsCentred.mem_span_iff_of_seqCond_dec` (also without the case split `J = ⊤`: `J ≤ 𝔪`).

`QuotSeq` restates `mem_span_iff_Q_dec` and proves `tau_injective_Q`, `mem_RF_iff_Q` (whose
statements have no coordinate set) through it, so their callers need no change.

Leaf module.
-/

namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing Constructive

section Dec

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] {n : ℕ}

namespace Chart

variable {c : Chart R n}

lemma IsCentred.pow_eq_span_dec (hc : c.IsCentred) (N : ℕ) :
    maximalIdeal R ^ N = Ideal.span (c.monos N) := by
  induction N with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, eq_comm, Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨0, by simp, by simp⟩
  | succ N ih =>
    rw [pow_succ, ih, hc, Ideal.span_mul_span]
    congr 1
    ext f
    simp only [Set.mem_mul, monos, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨a, ⟨α, hα, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
      exact ⟨α + Finsupp.single j 1, by simp [hα], (prod_pow_add_single _ _ _).symm⟩
    · rintro ⟨α, hα, rfl⟩
      obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 (show α ≠ 0 by rintro rfl; simp at hα)
      replace hj : α j ≠ 0 := hj
      set α' := α - Finsupp.single j 1 with hα'
      have hsum : α' + Finsupp.single j 1 = α := by
        ext l
        simp only [hα', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_apply]
        split_ifs with h
        · subst h; omega
        · omega
      refine ⟨_, ⟨α', ?_, rfl⟩, _, ⟨j, rfl⟩, ?_⟩
      · have := congrArg Finsupp.degree hsum
        rw [map_add, hα, Finsupp.degree_single] at this
        omega
      · rw [← prod_pow_add_single, hsum]

/-- **Key step of the duality, with a decidable `S`** (twin of `mem_sup_pow_succ`): the finite
representation is indexed by exponents (`Finsupp.mem_span_image_iff_linearCombination`, no
`choose`), and the case split on `∀ i ∈ S, α i = 0` is a decision. -/
lemma IsCentred.mem_sup_pow_succ_dec (hc : c.IsCentred) (S : Set (Fin n)) [DecidablePred (· ∈ S)]
    {g : R} (N : ℕ) (hg : g ∈ Ideal.span (c.x '' S) ⊔ maximalIdeal R ^ N)
    (h0 : ∀ δ : Fin n →₀ ℕ, (∀ i ∈ S, δ i = 0) → coeff δ (c.tau g) = 0) :
    g ∈ Ideal.span (c.x '' S) ⊔ maximalIdeal R ^ (N + 1) := by
  set J := Ideal.span (c.x '' S)
  set mo : (Fin n →₀ ℕ) → R := fun α => ∏ i, c.x i ^ α i with hmo
  obtain ⟨j, hj, h, hh, rfl⟩ := Submodule.mem_sup.1 hg
  have hmon : c.monos N = mo '' {α | α.degree = N} := by
    ext f
    constructor
    · rintro ⟨α, h1, h2⟩; exact ⟨α, h1, h2.symm⟩
    · rintro ⟨α, h1, h2⟩; exact ⟨α, h1, h2.symm⟩
  rw [hc.pow_eq_span_dec, hmon] at hh
  obtain ⟨l, hl, hlh⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 hh
  rw [Finsupp.mem_supported] at hl
  rw [Finsupp.linearCombination_apply] at hlh
  have hdeg : ∀ α ∈ l.support, α.degree = N := fun α hα => hl hα
  -- coefficient extraction
  have key : ∀ α ∈ l.support, (∀ i ∈ S, α i = 0) → l α ∈ maximalIdeal R := by
    intro α hα ht
    have h1 := h0 α ht
    rw [← hlh, map_add, map_add, hc.coeff_tau_eq_zero_of_mem hj _ ht, zero_add, Finsupp.sum,
      map_sum, map_sum] at h1
    rw [Finset.sum_eq_single α] at h1
    · rw [smul_eq_mul, map_mul, hmo, hc.tau_monomial, coeff_mul_monomial, ite_eq_left le_rfl,
        tsub_self, mul_one, coeff_zero_eq_constantCoeff_apply, constantCoeff_tau] at h1
      exact (residue_eq_zero_iff _).1 h1
    · intro β hβ hne
      rw [smul_eq_mul, map_mul, hmo, hc.tau_monomial, coeff_mul_monomial]
      split_ifs with hle
      · exact absurd (Finsupp.eq_of_le_of_degree_eq hle (by rw [hdeg β hβ, hdeg α hα])) hne
      · rfl
    · intro hn; exact absurd hα hn
  have hmem : ∀ α ∈ l.support, l α • mo α ∈ J ⊔ maximalIdeal R ^ (N + 1) := by
    intro α hα
    by_cases hS : ∃ i ∈ S, α i ≠ 0
    · obtain ⟨i, hiS, hi⟩ := hS
      refine Ideal.mem_sup_left (Ideal.mul_mem_left _ _ ?_)
      show ∏ i, c.x i ^ α i ∈ J
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _
        (Ideal.subset_span (Set.mem_image_of_mem c.x hiS)) _ (Nat.pos_of_ne_zero hi))
    · have hS' : ∀ i ∈ S, α i = 0 := fun i hi =>
        Decidable.byContradiction fun hne => hS ⟨i, hi, hne⟩
      refine Ideal.mem_sup_right ?_
      rw [smul_eq_mul, pow_succ']
      refine Ideal.mul_mem_mul (key α hα hS') ?_
      rw [hc.pow_eq_span_dec]
      exact Ideal.subset_span ⟨α, hdeg α hα, rfl⟩
  rw [← hlh, Finsupp.sum]
  exact add_mem (Ideal.mem_sup_left hj) (Ideal.sum_mem _ fun α hα => hmem α hα)

theorem IsCentred.mem_span_iff_of_seqCond_dec (hc : c.IsCentred) (S : Set (Fin n))
    [DecidablePred (· ∈ S)] (g : R)
    (hN : ∀ [IsLocalRing (R ⧸ Ideal.span (c.x '' S))],
      SeqCond (reesSubring (maximalIdeal (R ⧸ Ideal.span (c.x '' S))))) :
    g ∈ Ideal.span (c.x '' S) ↔
      ∀ δ : Fin n →₀ ℕ, (∀ i ∈ S, δ i = 0) → coeff δ (c.tau g) = 0 := by
  refine ⟨fun hg δ hδ => hc.coeff_tau_eq_zero_of_mem hg δ hδ, fun h0 => ?_⟩
  set J := Ideal.span (c.x '' S)
  have hN' : ∀ N, g ∈ J ⊔ maximalIdeal R ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => exact hc.mem_sup_pow_succ_dec S N ih h0
  -- `J ≤ 𝔪` (the chart is centred), so `J ≠ ⊤`: no case split
  have hJ : J ≠ ⊤ := fun htop => (maximalIdeal.isMaximal R).ne_top (eq_top_iff.2 (by
    rw [← htop, hc]
    exact Ideal.span_mono (Set.image_subset_range _ _)))
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine eq_zero_of_iInf _ hN (fun _ ha => isUnit_one_sub_of_mem_max ha) fun N => ?_
  have hle : Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R) ≤ maximalIdeal (R ⧸ J) :=
    Ideal.map_le_iff_le_comap.2 fun r hr => by
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : R ⧸ J)
      have h1 : Ideal.Quotient.mk J (r * s) = 1 := by rw [map_mul, hs, ← hu, Units.mul_inv]
      have h2 : r * s - 1 ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
      have h3 : r * s - 1 ∈ maximalIdeal R := le_maximalIdeal hJ h2
      have h4 : r * s ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hr
      exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2
        (by simpa using sub_mem h4 h3))
  have := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) (hN' N)
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow] at this
  exact Ideal.pow_right_mono hle N this

end Chart

end Dec

end BezoutCounterexample.Principalization
