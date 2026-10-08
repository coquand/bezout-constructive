import BezoutCounterexample.Principalization.DivisorialPt
import BezoutCounterexample.Principalization.LocDataPtMp

/-!
# Lemma 4.1 at points with `IsMaxInvPt` (leaf, for the top-chain switch)

The divisorial step of DivisorialPt with `hmaxPt : IsMaxInvPt I v₀` in place of the maximal-ideal
`hmax`. Argument order is kept; the only new inputs are those needed to produce invariants at
points (`l`, `hl`, `hchart`, as in `exists_invAt_semicont_ptL`):

* `div_not_mem_mp`, `div_Iloc_mp`, `div_invAt_iff_mp`, `div_inv_ge_mp`: `div_not_mem` …
  `div_inv_ge` (Divisorial) at an explicit point `q` (`q.ker` is maximal);
* `div_locusPt_le_mp`, `div_mem_locus_of_not_mem_mp`, `div_not_mem_comp_mp`,
  `div_locusPt_le_comp_mp`, `div_count_pt_mp`: as in DivisorialPt;
* `div_le_pt_mp`, `divisorial_decrease_pt_mp`: the attainment of `v₁` is at an explicit point
  (`hq₁`, from `IsMaxInv.attained_pt`) instead of `IsMaxInv (divI I π a) v₁`.

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

section DivMp

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [hpA : Fact (HasPres A)]

variable {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l)
  (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
  {v₀ : ℕ → ℚ} (hmaxPt : IsMaxInvPt I v₀)
  {π : A} {a : ℕ} (ha0 : 0 < a) (ha : v₀ 0 = 1 / a) (hle : I ≤ Ideal.span {π ^ a})

omit hpA in
include hI hl hchart hmaxPt ha0 ha hle in
/-- **The divisorial drop at a point**: `V(I : π^a)` misses `V(π)`. -/
theorem div_not_mem_mp (q : Pt A) (hq : divI I π a ≤ q.ker) : π ∉ q.ker := by
  intro hπq
  have hIq : I ≤ q.ker ^ (a + 1) := by
    rw [div_eq_mul hle, pow_succ]
    refine Ideal.mul_mono ?_ hq
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.pow_mem_pow hπq a
  have hIq' : I ≤ q.ker := hIq.trans (Ideal.pow_le_self (by omega))
  obtain ⟨v, hv, -⟩ := exists_invAt_semicont_ptL hI l hl hchart q hIq'
  have h1 := invAt_zero_le_of_le_pow hv (by omega) hIq
  have h2 := hmaxPt q hIq' v hv
  have hlt : v 0 < v₀ 0 := by
    rw [ha]
    refine lt_of_le_of_lt h1 ?_
    have : (0 : ℚ) < a := by exact_mod_cast ha0
    push_cast
    exact one_div_lt_one_div_of_lt this (by linarith)
  exact absurd h2 (not_le.2 ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _), hlt⟩)

omit hpA in
include hI hl hchart hmaxPt ha0 ha hle in
lemma div_Iloc_mp (q : Pt A) (hq : divI I π a ≤ q.ker) :
    Iloc I q.ker = Iloc (divI I π a) q.ker := by
  have := Iloc_span_unit_mul (J := divI I π a) (𝔪 := q.ker)
    (div_not_mem_mp hI l hl hchart hmaxPt ha0 ha hle q hq) a
  rwa [← div_eq_mul hle] at this

omit hpA in
include hI hl hchart hmaxPt ha0 ha hle in
lemma div_invAt_iff_mp (q : Pt A) (hq : divI I π a ≤ q.ker) {v : ℕ → ℚ} :
    InvAt (divI I π a) q.ker v ↔ InvAt I q.ker v :=
  ⟨InvAt.of_Iloc_eq (div_Iloc_mp hI l hl hchart hmaxPt ha0 ha hle q hq).symm,
    InvAt.of_Iloc_eq (div_Iloc_mp hI l hl hchart hmaxPt ha0 ha hle q hq)⟩

omit hpA in
include hI hl hchart hmaxPt ha0 ha hle in
lemma div_inv_ge_mp (q : Pt A) (hq : divI I π a ≤ q.ker) {v : ℕ → ℚ}
    (hv : InvAt (divI I π a) q.ker v) : toLex v₀ ≤ toLex v :=
  hmaxPt q ((le_divI I π a).trans hq) v ((div_invAt_iff_mp hI l hl hchart hmaxPt ha0 ha hle q hq).1 hv)

omit hpA in
include hI hl hchart hmaxPt ha0 ha hle in
/-- The points of the locus of `I₁` are points of the locus of `I`. -/
theorem div_locusPt_le_mp : locusPt I v₀ ≤ locusPt (divI I π a) v₀ := by
  intro f hf p hp hv
  exact hf p ((le_divI I π a).trans hp)
    ((div_invAt_iff_mp hI l hl hchart hmaxPt ha0 ha hle p hp).1 hv)

omit hpA in
include hI hl hchart hmaxPt ha0 ha hle in
/-- At a point of the locus of `I` off `V(π)`, `I₁` vanishes and has the same invariant. -/
theorem div_mem_locus_of_not_mem_mp (p : Pt A) (hIp : I ≤ p.ker) (hv : InvAt I p.ker v₀)
    (hπ : π ∉ p.ker) : divI I π a ≤ p.ker ∧ InvAt (divI I π a) p.ker v₀ := by
  have hle₁ : divI I π a ≤ p.ker := by
    intro f hf
    rcases p.ker_isMaximal.isPrime.mem_or_mem (hIp (mem_divI.1 hf)) with h | h
    · exact absurd (p.ker_isMaximal.isPrime.mem_of_pow_mem a h) hπ
    · exact h
  exact ⟨hle₁, (div_invAt_iff_mp hI l hl hchart hmaxPt ha0 ha hle p hle₁).2 hv⟩

include hI hl hchart hmaxPt ha0 ha hle in
/-- **`π` lies in no prime with generators above `locusPt I₁ v₀`**. -/
theorem div_not_mem_comp_mp {D : List A} (hDp : (lspan D).IsPrime)
    (hD : locusPt (divI I π a) v₀ ≤ lspan D) : π ∉ lspan D := by
  intro hπ
  obtain ⟨p, hp⟩ := (HasPres.exists_pt hpA.out) D ((Ideal.ne_top_iff_one _).1 hDp.ne_top)
  have h₁ : divI I π a ≤ p.ker := ((le_locusPt _ v₀).trans hD).trans hp
  exact div_not_mem_mp hI l hl hchart hmaxPt ha0 ha hle p h₁ (hp hπ)

include hI hl hchart hmaxPt ha0 ha hle in
/-- **A prime above the locus of `I` off `π` contains the locus of `I₁`**. -/
theorem div_locusPt_le_comp_mp {N : ℕ}
    (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (hb₀ : ∀ i, N ≤ i → v₀ i = 0) {C : List A} (hCp : (lspan C).IsPrime)
    (hC : locusPt I v₀ ≤ lspan C) (hπ : π ∉ lspan C) :
    locusPt (divI I π a) v₀ ≤ lspan C := by
  intro y hy
  rcases (HasPres.mem_dec hpA.out) C y with h | h
  · exact h
  · exfalso
    have hπy : ∀ k : ℕ, (π * y) ^ k ∉ lspan C := fun k hk =>
      (hCp.mem_or_mem (hCp.mem_of_pow_mem k hk)).elim hπ h
    obtain ⟨p, hCp', hp⟩ := (HasPres.exists_pt_away hpA.out) C (π * y) hπy
    obtain ⟨hIp, hv⟩ := mem_locusPt_of_le_ptL_mp hI l hl hchart hmaxPt hbd hb₀ p (hC.trans hCp')
    have hπp : π ∉ p.ker := fun h' => hp (Ideal.mul_mem_right _ _ h')
    obtain ⟨h₁, hv₁⟩ := div_mem_locus_of_not_mem_mp hI l hl hchart hmaxPt ha0 ha hle p hIp hv hπp
    exact hp (Ideal.mul_mem_left _ _ (hy p h₁ hv₁))

include hI hl hchart hmaxPt ha0 ha hle in
/-- **The number of components drops** (the `NumComp` form of `div_count`). -/
theorem div_count_pt_mp {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (h𝔭π : 𝔭 = Ideal.span {π})
    {Pg Pg₁ : List A} (hPg : locusPt I v₀ = lspan Pg)
    (hPg₁ : locusPt (divI I π a) v₀ = lspan Pg₁) {k k₁ : ℕ} (hk : NumComp Pg k)
    (hk₁ : NumComp Pg₁ k₁) : k₁ < k := by
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  obtain ⟨Cs, hC, rfl⟩ := hk
  obtain ⟨Ds, hD, rfl⟩ := hk₁
  have hπ𝔭 : π ∈ 𝔭 := h𝔭π ▸ Ideal.mem_span_singleton_self π
  -- each component of `I₁` is a component of `I` not containing `π`
  have hmap : ∀ D ∈ Ds, π ∉ lspan D ∧ ∃ C ∈ Cs, lspan C = lspan D := by
    intro D hDm
    have hDle : locusPt (divI I π a) v₀ ≤ lspan D := hPg₁ ▸ hD.le D hDm
    have hπD := div_not_mem_comp_mp hI l hl hchart hmaxPt ha0 ha hle (hD.isPrime hDm) hDle
    refine ⟨hπD, ?_⟩
    obtain ⟨C, hCm, hCD⟩ := hC.exists_le (hD.isPrime hDm)
      ((hPg ▸ div_locusPt_le_mp hI l hl hchart hmaxPt ha0 ha hle).trans hDle)
    have hπC : π ∉ lspan C := fun h' => hπD (hCD h')
    have hC₁ : lspan Pg₁ ≤ lspan C :=
      hPg₁ ▸ div_locusPt_le_comp_mp hI l hl hchart hmaxPt ha0 ha hle hbd hb₀ (hC.isPrime hCm)
        (hPg ▸ hC.le C hCm) hπC
    exact ⟨C, hCm, hD.minimal D hDm _ (hC.isPrime hCm) hC₁ hCD⟩
  -- `𝔭` is a component of `I`
  obtain ⟨C₀, hC₀m, hC₀⟩ := hC.exists_eq_of_mem_minimalPrimes (hPg ▸ h𝔭.min)
  have hsub : 𝔭 :: Ds.map lspan ⊆ Cs.map lspan := by
    intro P hP
    rcases List.mem_cons.1 hP with rfl | hP
    · exact List.mem_map.2 ⟨C₀, hC₀m, hC₀⟩
    · obtain ⟨D, hDm, rfl⟩ := List.mem_map.1 hP
      obtain ⟨C, hCm, hCD⟩ := (hmap D hDm).2
      exact List.mem_map.2 ⟨C, hCm, hCD⟩
  have hnd : (𝔭 :: Ds.map lspan).Nodup := by
    refine List.nodup_cons.2 ⟨fun h' => ?_, hD.nodup_map⟩
    obtain ⟨D, hDm, hD𝔭⟩ := List.mem_map.1 h'
    exact (hmap D hDm).1 (hD𝔭 ▸ hπ𝔭)
  have := hnd.length_le_of_subset hsub
  rw [List.length_cons, List.length_map, List.length_map] at this
  omega

omit hpA in
include hI hl hchart hmaxPt ha0 ha hle in
/-- **`maxinv(I₁) ⪯ maxinv(I)`**, as relations. -/
theorem div_le_pt_mp {v₁ : ℕ → ℚ}
    (hq₁ : ∃ q : Pt A, divI I π a ≤ q.ker ∧ InvAt (divI I π a) q.ker v₁) : v₁ ⪯ v₀ := by
  obtain ⟨q₁, hI₁, hv₁⟩ := hq₁
  exact div_inv_ge_mp hI l hl hchart hmaxPt ha0 ha hle q₁ hI₁ hv₁

include hI hl hchart hmaxPt ha0 ha hle in
/-- **Lemma 4.1 at points**: `v₁ ≺ v₀`, or `v₁ = v₀` and the number of components drops. -/
theorem divisorial_decrease_pt_mp {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭)
    (h𝔭π : 𝔭 = Ideal.span {π}) {v₁ : ℕ → ℚ}
    (hq₁ : ∃ q : Pt A, divI I π a ≤ q.ker ∧ InvAt (divI I π a) q.ker v₁)
    {Pg Pg₁ : List A} (hPg : locusPt I v₀ = lspan Pg)
    (hPg₁ : locusPt (divI I π a) v₁ = lspan Pg₁) {k k₁ : ℕ} (hk : NumComp Pg k)
    (hk₁ : NumComp Pg₁ k₁) : v₁ ≺ v₀ ∨ (v₁ = v₀ ∧ k₁ < k) := by
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  have hb₁ : ∀ i, N ≤ i → v₁ i = 0 := by
    obtain ⟨q₁, hI₁, hv₁⟩ := hq₁
    exact hbd q₁.ker v₁ ((div_invAt_iff_mp hI l hl hchart hmaxPt ha0 ha hle q₁ hI₁).1 hv₁)
  rcases weight_le_dec hb₁ hb₀ (div_le_pt_mp hI l hl hchart hmaxPt ha0 ha hle hq₁) with h | rfl
  · exact Or.inl h
  · exact Or.inr ⟨rfl, div_count_pt_mp hI l hl hchart hmaxPt ha0 ha hle h𝔭 h𝔭π hPg hPg₁ hk hk₁⟩

end DivMp

end BezoutCounterexample.Principalization
