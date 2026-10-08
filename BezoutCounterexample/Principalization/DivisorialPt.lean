import BezoutCounterexample.Principalization.Divisorial
import BezoutCounterexample.Principalization.InvariantPt
import BezoutCounterexample.Principalization.LocDataPtProd

/-!
# Lemma 4.1 (the divisorial decrease) at points (D3.5, leaf)

`PrincipalizationData.divisorial_decrease` (top level, `Divisorial.lean`) compares `maxinv(I₁)`
with `maxinv(I)` by `by_cases`, identifies the components of `I₁` with `components I \ {𝔭}`
through `components_eq_of`/`eq_of_forall_isMaximal` (Jacobson, finite sets of ideals), and counts
them with `Set.ncard`. Here, with `I₁ = (I : π^a)` (`divI`), `𝔭 = (π)` and the maximal invariant as
a relation (`docs/d3-design.md` §5, D3.5; rewrite-tasks C8):

* `div_locusPt_le`: `locusPt I v₀ ≤ locusPt I₁ v₀` (the points of the locus of `I₁` are points of
  the locus of `I`);
* `div_not_mem_comp`: `π` lies in no prime above `locusPt I₁ v₀` with generators (decided by (G);
  otherwise an explicit point above it contradicts `div_not_mem`);
* `div_locusPt_le_comp`: every prime `lspan C ⊇ locusPt I v₀` with `π ∉ lspan C` contains
  `locusPt I₁ v₀` (`exists_pt_away` at `π · y`; `mem_locusPt_of_le_ptL`, D3.6);
* `div_count_pt`: with `NumComp`, `k₁ < k`. The components of `I₁` inject into those of `I`
  other than `𝔭` (list form: `𝔭 :: Ds ⊆ Cs`, no duplicates);
* `div_le_pt`, `divisorial_decrease_pt`: `v₁ ≺ v₀ ∨ (v₁ = v₀ ∧ k₁ < k)` for
  `IsMaxInv I v₀`, `IsMaxInv I₁ v₁`, `NumComp Pg k`, `NumComp Pg₁ k₁` (`lspan Pg`, `lspan Pg₁` the
  locus ideals at points). `I₁ = ⊤` is decided by the caller (`HasPres.mem_dec _ 1`).

These replace `eq_of_forall_isMaximal`, `components_eq_of` and `div_count` on the path. Leaf
module; no `classical`, no `by_contra`, no `Set.ncard`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

section DivPt

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [hpA : Fact (HasPres A)]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {π : A} {a : ℕ} (ha0 : 0 < a) (ha : v₀ 0 = 1 / a) (hle : I ≤ Ideal.span {π ^ a})

omit hpA in
include hI hmax ha0 ha hle in
/-- The points of the locus of `I₁` are points of the locus of `I`. -/
theorem div_locusPt_le : locusPt I v₀ ≤ locusPt (divI I π a) v₀ := by
  intro f hf p hp hv
  exact hf p ((le_divI I π a).trans hp)
    ((div_invAt_iff hI hmax ha0 ha hle p.ker hp).1 hv)

omit hpA in
include hI hmax ha0 ha hle in
/-- At a point of the locus of `I` off `V(π)`, `I₁` vanishes and has the same invariant. -/
theorem div_mem_locus_of_not_mem (p : Pt A) (hIp : I ≤ p.ker) (hv : InvAt I p.ker v₀)
    (hπ : π ∉ p.ker) : divI I π a ≤ p.ker ∧ InvAt (divI I π a) p.ker v₀ := by
  have hle₁ : divI I π a ≤ p.ker := by
    intro f hf
    rcases p.ker_isMaximal.isPrime.mem_or_mem (hIp (mem_divI.1 hf)) with h | h
    · exact absurd (p.ker_isMaximal.isPrime.mem_of_pow_mem a h) hπ
    · exact h
  exact ⟨hle₁, (div_invAt_iff hI hmax ha0 ha hle p.ker hle₁).2 hv⟩

include hI hmax ha0 ha hle in
/-- **`π` lies in no prime with generators above `locusPt I₁ v₀`**. -/
theorem div_not_mem_comp {D : List A} (hDp : (lspan D).IsPrime)
    (hD : locusPt (divI I π a) v₀ ≤ lspan D) : π ∉ lspan D := by
  intro hπ
  obtain ⟨p, hp⟩ := (HasPres.exists_pt hpA.out) D ((Ideal.ne_top_iff_one _).1 hDp.ne_top)
  have h₁ : divI I π a ≤ p.ker := ((le_locusPt _ v₀).trans hD).trans hp
  exact div_not_mem hI hmax ha0 ha hle p.ker h₁ (hp hπ)

include hI hmax ha0 ha hle in
/-- **A prime above the locus of `I` off `π` contains the locus of `I₁`**. -/
theorem div_locusPt_le_comp (l : List A) (hl : I = lspan l)
    (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
    {N : ℕ}
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
    obtain ⟨hIp, hv⟩ := mem_locusPt_of_le_ptL hI l hl hchart hmax hbd hb₀ p (hC.trans hCp')
    have hπp : π ∉ p.ker := fun h' => hp (Ideal.mul_mem_right _ _ h')
    obtain ⟨h₁, hv₁⟩ := div_mem_locus_of_not_mem hI hmax ha0 ha hle p hIp hv hπp
    exact hp (Ideal.mul_mem_left _ _ (hy p h₁ hv₁))

include hI hmax ha0 ha hle in
/-- **The number of components drops** (the `NumComp` form of `div_count`). -/
theorem div_count_pt (l : List A) (hl : I = lspan l)
    (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
    {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (h𝔭π : 𝔭 = Ideal.span {π})
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
    have hπD := div_not_mem_comp hI hmax ha0 ha hle (hD.isPrime hDm) hDle
    refine ⟨hπD, ?_⟩
    obtain ⟨C, hCm, hCD⟩ := hC.exists_le (hD.isPrime hDm)
      ((hPg ▸ div_locusPt_le hI hmax ha0 ha hle).trans hDle)
    have hπC : π ∉ lspan C := fun h' => hπD (hCD h')
    have hC₁ : lspan Pg₁ ≤ lspan C :=
      hPg₁ ▸ div_locusPt_le_comp hI hmax ha0 ha hle l hl hchart hbd hb₀ (hC.isPrime hCm)
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
include hI hmax ha0 ha hle in
/-- **`maxinv(I₁) ⪯ maxinv(I)`**, as relations. -/
theorem div_le_pt {v₁ : ℕ → ℚ} (he₁ : IsMaxInv (divI I π a) v₁) : v₁ ⪯ v₀ := by
  obtain ⟨⟨𝔪₁, _, hI₁, hv₁⟩, -⟩ := he₁
  exact div_inv_ge hI hmax ha0 ha hle 𝔪₁ hI₁ hv₁

include hI hmax ha0 ha hle in
/-- **Lemma 4.1 at points**: `v₁ ≺ v₀`, or `v₁ = v₀` and the number of components drops. -/
theorem divisorial_decrease_pt (l : List A) (hl : I = lspan l)
    (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
    {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭)
    (h𝔭π : 𝔭 = Ideal.span {π}) {v₁ : ℕ → ℚ} (he₁ : IsMaxInv (divI I π a) v₁)
    {Pg Pg₁ : List A} (hPg : locusPt I v₀ = lspan Pg)
    (hPg₁ : locusPt (divI I π a) v₁ = lspan Pg₁) {k k₁ : ℕ} (hk : NumComp Pg k)
    (hk₁ : NumComp Pg₁ k₁) : v₁ ≺ v₀ ∨ (v₁ = v₀ ∧ k₁ < k) := by
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  have hb₁ : ∀ i, N ≤ i → v₁ i = 0 := by
    obtain ⟨⟨𝔪₁, _, hI₁, hv₁⟩, -⟩ := he₁
    exact hbd 𝔪₁ v₁ ((div_invAt_iff hI hmax ha0 ha hle 𝔪₁ hI₁).1 hv₁)
  rcases weight_le_dec hb₁ hb₀ (div_le_pt hI hmax ha0 ha hle he₁) with h | rfl
  · exact Or.inl h
  · exact Or.inr ⟨rfl, div_count_pt hI hmax ha0 ha hle l hl hchart h𝔭 h𝔭π hPg hPg₁ hk hk₁⟩

end DivPt

end BezoutCounterexample.Principalization
