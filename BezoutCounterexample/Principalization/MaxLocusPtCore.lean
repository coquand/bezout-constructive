import BezoutCounterexample.Principalization.MaxLocus
import BezoutCounterexample.Principalization.Points
import BezoutCounterexample.Constructive.CompList
import BezoutCounterexample.Principalization.MaxInvPtDef

/-!
# The maximal locus at explicit points: the core (D3.3c, `docs/d3-design.md` §8.2–8.3)

Split from `MaxLocusPt.lean` so that the engine modules below `MarkedCenter` (`Principalization/
{Torsor, TorsorInv, TorsorDer, Divisorial}`, reached from `PosCover` through `MarkedCenter`) can take
`h𝔭 : LocusComp I v₀ 𝔭`. Imports only `MaxLocus`, `Points` and `CompList`.

* `locusPt I v₀`: the functions vanishing at every explicit point of the maximal locus;
  `locusIdeal_le_locusPt` (constructive), `locusPt_eq_locusIdeal` (classical comparison, off path).
* `LocData.g_mul_num_mem_pt`, `LocData.exists_heads`: the head numerators `a` of local data, with
  `g a ⊆ locusPt` and `V(a) ∩ D(g)` in the locus at points.
* `LocData.locusPt_le_p`: `locusPt ≤ D.p` by the Nullstellensatz on `V(a) ∩ D(g f)`
  (`HasPres.exists_pt_away`); no generators of `D.p` are needed.
* `mem_locusPt_of_le`, `mem_locusPt_of_le_max`: the maximal locus is closed above `locusPt`, at points
  and at maximal ideals (`eq_or_ne_bounded` decides `v = v₀`; membership is decided only at points).
* `LocusComp I v₀ 𝔭`: a component of the maximal locus with generators (`Prop` record);
  `LocusComp.eq_p`, `LocusComp.mem`, `LocusComp.mem_max`, `LocusComp.sup_eq_top`; producers
  `LocusComp.of_comp`, `IsCompList.locusComp`.
* Classical, off the path at the end of D3.3: `locusPt_eq_locusIdeal`, and the two TEMPORARY
  helpers of the top-down switch, `LocusComp.of_minimalPrimes` and `LocusComp.toMin`.

Only the `D.iff` field of `LocData` is used, and only at kernels of points.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing IsLocalization

section Aux

/-- Finite choice over `Fin n`. -/
lemma exists_fun_fin {α : Type*} : ∀ {n : ℕ} (P : Fin n → α → Prop), (∀ i, ∃ a, P i a) →
    ∃ f : Fin n → α, ∀ i, P i (f i)
  | 0, _, _ => ⟨Fin.elim0, fun i => i.elim0⟩
  | n + 1, P, h => by
    obtain ⟨a, ha⟩ := h 0
    obtain ⟨f, hf⟩ := exists_fun_fin (fun i => P i.succ) (fun i => h i.succ)
    exact ⟨Fin.cons a f, fun i => Fin.cases ha hf i⟩

/-- Equality of bounded invariants is decided. -/
lemma eq_or_ne_bounded {N : ℕ} {v w : ℕ → ℚ} (hv : ∀ i, N ≤ i → v i = 0)
    (hw : ∀ i, N ≤ i → w i = 0) : v = w ∨ v ≠ w := by
  rcases Decidable.em (∀ i, i < N → v i = w i) with h | h
  · left
    funext i
    rcases Nat.lt_or_ge i N with hi | hi
    · exact h i hi
    · rw [hv i hi, hw i hi]
  · exact Or.inr fun hvw => h fun i _ => hvw ▸ rfl

end Aux

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- **The ideal of the maximal locus, at explicit points.** -/
def locusPt (I : Ideal A) (v₀ : ℕ → ℚ) : Ideal A where
  carrier := {f | ∀ p : Pt A, I ≤ p.ker → InvAt I p.ker v₀ → f ∈ p.ker}
  add_mem' := fun ha hb p hI hv => add_mem (ha p hI hv) (hb p hI hv)
  zero_mem' := fun _ _ _ => zero_mem _
  smul_mem' := fun c _ hx p hI hv => Ideal.mul_mem_left _ c (hx p hI hv)

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma mem_locusPt {I : Ideal A} {v₀ : ℕ → ℚ} {f : A} :
    f ∈ locusPt I v₀ ↔ ∀ p : Pt A, I ≤ p.ker → InvAt I p.ker v₀ → f ∈ p.ker := Iff.rfl

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma le_locusPt (I : Ideal A) (v₀ : ℕ → ℚ) : I ≤ locusPt I v₀ :=
  fun _ ha _ hI _ => hI ha

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- The classical locus ideal lies in the one at points (elimination at `p.ker`). -/
lemma locusIdeal_le_locusPt [IsNoetherianRing A] (I : Ideal A) (v₀ : ℕ → ℚ) :
    locusIdeal I v₀ ≤ locusPt I v₀ :=
  fun _ hf p hI hv => mem_locusIdeal.1 hf p.ker ⟨inferInstance, hI, hv⟩

namespace LocData

variable [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal]
  (D : LocData I v₀ 𝔪)

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- `g aᵢ` lies in the locus ideal at points (decided at each point). -/
lemma g_mul_num_mem_pt (i : Fin D.n) (hi : (i : ℕ) < D.k) (a : A) (m : D.M)
    (hx : D.ck.x i = IsLocalization.mk' (Localization D.M) a m) :
    D.g * a ∈ locusPt I v₀ := by
  intro p hI hv
  rcases p.mem_ker_dec D.g with hg | hg
  · exact Ideal.mul_mem_right _ _ hg
  · refine Ideal.mul_mem_left _ _ ?_
    have := (D.iff p.ker hg).1 ⟨hI, hv⟩ i hi
    rw [D.transport_x_mk' _ i a m hx,
      IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime p.ker) p.ker] at this
    exact this

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- **The head numerators** of local data: in `D.p`, with `g a ⊆ locusPt`, and
`V(a) ∩ D(g)` in the maximal locus at points. -/
theorem exists_heads : ∃ a : List A, (∀ b ∈ a, b ∈ D.p) ∧ (∀ b ∈ a, D.g * b ∈ locusPt I v₀) ∧
    ∀ p : Pt A, D.g ∉ p.ker → (∀ b ∈ a, b ∈ p.ker) → I ≤ p.ker ∧ InvAt I p.ker v₀ := by
  obtain ⟨f, hf⟩ := exists_fun_fin
    (fun i (am : A × D.M) => D.ck.x i = IsLocalization.mk' (Localization D.M) am.1 am.2)
    (fun i => by obtain ⟨a, m, h⟩ := D.exists_num i; exact ⟨(a, m), h⟩)
  refine ⟨((List.finRange D.n).filter (fun i : Fin D.n => decide ((i : ℕ) < D.k))).map
    (fun i => (f i).1), ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact D.num_mem_p i (by simpa using (List.mem_filter.1 hi).2) _ _ (hf i)
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact D.g_mul_num_mem_pt i (by simpa using (List.mem_filter.1 hi).2) _ _ (hf i)
  · intro p hg hall
    rw [D.iff p.ker hg]
    intro i hi
    rw [D.transport_x_mk' _ i _ _ (hf i),
      IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime p.ker) p.ker]
    exact hall _ (List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_finRange i, decide_eq_true hi⟩,
      rfl⟩)

/-- **The locus ideal at points lies in `D.p`** (replaces `locusIdeal_le_p`, no Jacobson): decide
`(g f)ᵏ ∈ (a)` for the head numerators `a`; otherwise a point of `V(a) ∩ D(g f)` lies in the locus
and `f` does not vanish there. -/
theorem locusPt_le_p [hpA : Fact (HasPres A)] : locusPt I v₀ ≤ D.p := by
  intro f hf
  have hp : HasPres A := hpA.out
  obtain ⟨a, hap, -, hloc⟩ := D.exists_heads
  obtain ⟨R, hR⟩ := hp.exists_radical a
  rcases hp.mem_dec R (D.g * f) with h | h
  · rw [hR] at h
    obtain ⟨k, hk⟩ := h
    have hle : lspan a ≤ D.p := by
      rw [lspan, Ideal.span_le]; exact fun b hb => hap b hb
    rcases (inferInstance : D.p.IsPrime).mem_or_mem
      ((inferInstance : D.p.IsPrime).mem_of_pow_mem k (hle hk)) with h | h
    · exact absurd (D.p_le h) D.hg
    · exact h
  · exfalso
    have hk : ∀ k : ℕ, (D.g * f) ^ k ∉ lspan a := fun k hk => h (hR ▸ ⟨k, hk⟩)
    obtain ⟨p, hap', hgf⟩ := HasPres.exists_pt_away hp a (D.g * f) hk
    have hg : D.g ∉ p.ker := fun h => hgf (Ideal.mul_mem_right _ _ h)
    obtain ⟨hI, hv⟩ := hloc p hg fun b hb => hap' (Ideal.subset_span hb)
    exact hgf (Ideal.mul_mem_left _ _ (hf p hI hv))

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- The chart functions lie in the extension of any ideal containing `locusPt`. -/
lemma P_le_map_pt {𝔮 : Ideal A} (h𝔮 : locusPt I v₀ ≤ 𝔮) :
    D.P ≤ 𝔮.map (algebraMap A (Localization.AtPrime 𝔪)) := by
  rw [P, Ideal.span_le]
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨a, m, hx⟩ := D.exists_num i
  rw [SetLike.mem_coe, D.transport_x_mk' _ i a m hx,
    IsLocalization.mk'_mem_map_algebraMap_iff 𝔪.primeCompl]
  exact ⟨D.g, D.hg, h𝔮 (D.g_mul_num_mem_pt i hi a m hx)⟩

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- `D.p` lies below every prime between `locusPt` and `𝔪`. -/
lemma p_le_of_le_pt {𝔮 : Ideal A} [𝔮.IsPrime] (h1 : locusPt I v₀ ≤ 𝔮) (h2 : 𝔮 ≤ 𝔪) :
    D.p ≤ 𝔮 := by
  intro a ha
  have h := D.P_le_map_pt h1 ha
  rw [← under_map_atPrime h2]
  exact h

end LocData

/-- **The maximal locus is closed, at points**: an explicit point above `locusPt` lies in the
locus. `v = v₀` is decided by the support bound (`eq_or_ne_bounded`); otherwise the
semicontinuity neighbourhood `D(g)` misses the locus, so `g ∈ locusPt` (decided at each point). -/
theorem mem_locusPt_of_le {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
    (hmax : IsMaxInvPt I v₀)
    {N : ℕ} (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (hb₀ : ∀ i, N ≤ i → v₀ i = 0) (p : Pt A) (hle : locusPt I v₀ ≤ p.ker) :
    I ≤ p.ker ∧ InvAt I p.ker v₀ := by
  have hIp : I ≤ p.ker := (le_locusPt I v₀).trans hle
  refine ⟨hIp, ?_⟩
  obtain ⟨v, hv⟩ := exists_invAt hI p.ker hIp
  rcases eq_or_ne_bounded (hbd _ _ hv) hb₀ with heq | hne
  · exact heq ▸ hv
  · exfalso
    have hlt : toLex v₀ < toLex v := lt_of_le_of_ne (hmax _ hIp v hv)
      (fun h => hne (toLex.injective h).symm)
    obtain ⟨g, hg, hgv⟩ := invAt_semicont hI p.ker hIp hv
    refine hg (hle fun q _ hvq => ?_)
    rcases q.mem_ker_dec g with h | h
    · exact h
    · exact absurd (hgv q.ker h v₀ hvq) (not_le.2 hlt)

/-- **The maximal locus is closed, at maximal ideals above `locusPt`**: the conclusion is at an
arbitrary maximal ideal, but the proof decides membership only at explicit points (that the
semicontinuity element `g` lies in `locusPt`). -/
theorem mem_locusPt_of_le_max {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
    (hmax : IsMaxInvPt I v₀)
    {N : ℕ} (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (hb₀ : ∀ i, N ≤ i → v₀ i = 0) (𝔪 : Ideal A) [𝔪.IsMaximal] (hle : locusPt I v₀ ≤ 𝔪) :
    I ≤ 𝔪 ∧ InvAt I 𝔪 v₀ := by
  have hI𝔪 : I ≤ 𝔪 := (le_locusPt I v₀).trans hle
  refine ⟨hI𝔪, ?_⟩
  obtain ⟨v, hv⟩ := exists_invAt hI 𝔪 hI𝔪
  rcases eq_or_ne_bounded (hbd _ _ hv) hb₀ with heq | hne
  · exact heq ▸ hv
  · exfalso
    have hlt : toLex v₀ < toLex v := lt_of_le_of_ne ((IsMaxInvPt.toMax hmax) _ hI𝔪 v hv)
      (fun h => hne (toLex.injective h).symm)
    obtain ⟨g, hg, hgv⟩ := invAt_semicont hI 𝔪 hI𝔪 hv
    refine hg (hle fun q _ hvq => ?_)
    rcases q.mem_ker_dec g with h | h
    · exact h
    · exact absurd (hgv q.ker h v₀ hvq) (not_le.2 hlt)

/-- **A component of the maximal locus, with generators** (`docs/d3-design.md` §8.2; m7, I1):
`𝔭` is a minimal prime of the locus ideal at points, whose generators exist, together with the
support bound of the invariants. A `Prop`: the data stay inside existentials. -/
structure LocusComp (I : Ideal A) (v₀ : ℕ → ℚ) (𝔭 : Ideal A) : Prop where
  /-- the locus ideal at points is finitely generated -/
  Pg : ∃ Pg : List A, locusPt I v₀ = lspan Pg
  /-- the support bound of the invariants -/
  bd : ∃ N : ℕ, (∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0) ∧
    ∀ i, N ≤ i → v₀ i = 0
  /-- `𝔭` is a minimal prime of the locus ideal at points -/
  min : 𝔭 ∈ (locusPt I v₀).minimalPrimes
  /-- generators of `I` (inputs of the point forms of the engine lemmas) -/
  gensI : ∃ l : List A, I = lspan l
  /-- charts of one size around every explicit point (from the stage's certificate,
  `ChartDim.exists_chart_away`) -/
  chartn : ∃ dim : ℕ, ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) dim)

namespace LocusComp

variable {I : Ideal A} {v₀ : ℕ → ℚ} {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭)
include h𝔭

omit [IsDomain A] [Algebra.Smooth ℚ A] in
theorem isPrime : 𝔭.IsPrime := h𝔭.min.1.1

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- A chart around every explicit point (the `hchart` input of the point lemmas). -/
theorem hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ,
    Nonempty (Chart (Localization.Away f) n) := fun p => by
  obtain ⟨dim, h⟩ := h𝔭.chartn
  obtain ⟨f, hf, hc⟩ := h p
  exact ⟨f, hf, dim, hc⟩

omit [IsDomain A] [Algebra.Smooth ℚ A] in
theorem le : locusPt I v₀ ≤ 𝔭 := h𝔭.min.1.2

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- **Generators of a component**, from those of the locus ideal (`IsCompList`). -/
theorem gens [Fact (HasPres A)] : ∃ C : List A, 𝔭 = lspan C ∧ PrimeFF (lspan C) := by
  obtain ⟨Pg, hPg⟩ := h𝔭.Pg
  obtain ⟨Cs, hC⟩ := HasPres.exists_compList (Fact.out : HasPres A) Pg
  obtain ⟨C, hCm, hCe⟩ := hC.exists_eq_of_mem_minimalPrimes (hPg ▸ h𝔭.min)
  exact ⟨C, hCe.symm, hC.primeFF C hCm⟩

/-- **The points of a component lie in the maximal locus.** -/
theorem mem (hI : I ≠ ⊥)
    (hmax : IsMaxInvPt I v₀)
    (p : Pt A) (h : 𝔭 ≤ p.ker) : I ≤ p.ker ∧ InvAt I p.ker v₀ := by
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  exact mem_locusPt_of_le hI hmax hbd hb₀ p (h𝔭.le.trans h)

/-- **The maximal ideals above a component lie in the maximal locus** (replaces
`mem_maxLocus_of_minimal`; decided only at points, see `mem_locusPt_of_le_max`). -/
theorem mem_max (hI : I ≠ ⊥)
    (hmax : IsMaxInvPt I v₀)
    (𝔪 : Ideal A) [𝔪.IsMaximal] (h : 𝔭 ≤ 𝔪) : I ≤ 𝔪 ∧ InvAt I 𝔪 v₀ := by
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  exact mem_locusPt_of_le_max hI hmax hbd hb₀ 𝔪 (h𝔭.le.trans h)

/-- **The component is the prime of local data at any of its points** (replaces
`LocData.eq_p_of_minimal`). -/
theorem eq_p [IsNoetherianRing A] [Fact (HasPres A)] {𝔪 : Ideal A} [𝔪.IsMaximal]
    (D : LocData I v₀ 𝔪) (h : 𝔭 ≤ 𝔪) : 𝔭 = D.p := by
  have := h𝔭.isPrime
  have hp : D.p ≤ 𝔭 := D.p_le_of_le_pt h𝔭.le h
  exact le_antisymm (h𝔭.min.2 ⟨inferInstance, D.locusPt_le_p⟩ hp) hp

/-- **Distinct components are comaximal** (replaces `minimalPrimes_sup_eq_top`): `1 ∈ 𝔭 + 𝔭'` is
decided by (G); otherwise local data at an explicit point of `V(𝔭 + 𝔭')` give `𝔭 = D.p = 𝔭'`. -/
theorem sup_eq_top [IsNoetherianRing A] [hpA : Fact (HasPres A)] (hI : I ≠ ⊥)
    (hmax : IsMaxInvPt I v₀)
    {𝔭' : Ideal A} (h𝔭' : LocusComp I v₀ 𝔭') (hne : 𝔭 ≠ 𝔭') : 𝔭 ⊔ 𝔭' = ⊤ := by
  obtain ⟨C, hC, -⟩ := h𝔭.gens
  obtain ⟨C', hC', -⟩ := h𝔭'.gens
  have hsup : 𝔭 ⊔ 𝔭' = lspan (C ++ C') := by
    rw [hC, hC', lspan, lspan, lspan, ← Ideal.span_union]
    congr 1
    ext x
    simp [List.mem_append]
  rcases hpA.out.mem_dec (C ++ C') 1 with h1 | h1
  · rw [hsup]; exact (Ideal.eq_top_iff_one _).2 h1
  · obtain ⟨p, hp⟩ := HasPres.exists_pt hpA.out _ h1
    rw [← hsup] at hp
    obtain ⟨hIp, hv⟩ := h𝔭.mem hI hmax p (le_sup_left.trans hp)
    obtain ⟨D⟩ := LocData.nonempty hI p.ker hIp hv
    exact absurd ((h𝔭.eq_p D (le_sup_left.trans hp)).trans
      (h𝔭'.eq_p D (le_sup_right.trans hp)).symm) hne

end LocusComp

/-! ### Producers of `LocusComp` -/

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- A component from an explicit component record of the locus ideal (constructive producer). -/
theorem LocusComp.of_comp {I : Ideal A} {v₀ : ℕ → ℚ} {Pg : List A}
    (hPg : locusPt I v₀ = lspan Pg) {N : ℕ}
    (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (hb₀ : ∀ i, N ≤ i → v₀ i = 0) (hgI : ∃ l : List A, I = lspan l)
    (hch : ∃ dim : ℕ, ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) dim))
    (P : Comp Pg) : LocusComp I v₀ (lspan P.gens) :=
  ⟨⟨Pg, hPg⟩, ⟨N, hbd, hb₀⟩, hPg ▸ P.mem_minimalPrimes, hgI, hch⟩

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- A component from an entry of an explicit component list (constructive producer). -/
theorem _root_.BezoutCounterexample.Constructive.IsCompList.locusComp {I : Ideal A} {v₀ : ℕ → ℚ} {Pg : List A}
    (hPg : locusPt I v₀ = lspan Pg) {N : ℕ}
    (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (hb₀ : ∀ i, N ≤ i → v₀ i = 0) (hgI : ∃ l : List A, I = lspan l)
    (hch : ∃ dim : ℕ, ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) dim))
    {Cs : List (List A)} (hC : IsCompList Pg Cs) {C : List A}
    (hCm : C ∈ Cs) : LocusComp I v₀ (lspan C) :=
  ⟨⟨Pg, hPg⟩, ⟨N, hbd, hb₀⟩, hPg ▸ hC.mem_minimalPrimes hCm, hgI, hch⟩

/-! ### Classical comparison (off path) -/


omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- **The two locus ideals agree** (classical comparison; off the path). -/
theorem locusPt_eq_locusIdeal [Algebra.FiniteType ℚ A] [IsNoetherianRing A] (I : Ideal A)
    (v₀ : ℕ → ℚ) : locusPt I v₀ = locusIdeal I v₀ := by
  refine le_antisymm (fun f hf => mem_locusIdeal.2 fun 𝔪 ⟨h𝔪, hI, hv⟩ => ?_)
    (locusIdeal_le_locusPt I v₀)
  have hk := Pt.ker_ofIsMaximal 𝔪
  have h1 : I ≤ (Pt.ofIsMaximal 𝔪).ker := by rw [hk]; exact hI
  have h2 := hf (Pt.ofIsMaximal 𝔪) h1 (InvAt.of_eq hk.symm hv)
  rwa [hk] at h2

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- TEMPORARY: removed in D3.3e. The producer-side bridge from the classical hypothesis
`𝔭 ∈ (locusIdeal I v₀).minimalPrimes` (classical through `locusPt_eq_locusIdeal`); used only at the
single producer site `ReesData.h𝔭` until `ReesData.comp` (D3.3e, `docs/d3-design.md` §8.5). -/
theorem LocusComp.of_minimalPrimes [Algebra.FiniteType ℚ A] [IsNoetherianRing A] {I : Ideal A}
    {v₀ : ℕ → ℚ} (hPg : ∃ Pg : List A, locusPt I v₀ = lspan Pg) {N : ℕ}
    (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (hb₀ : ∀ i, N ≤ i → v₀ i = 0) (hgI : ∃ l : List A, I = lspan l)
    (hch : ∃ dim : ℕ, ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) dim))
    {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) :
    LocusComp I v₀ 𝔭 :=
  ⟨hPg, ⟨N, hbd, hb₀⟩, locusPt_eq_locusIdeal I v₀ ▸ h𝔭, hgI, hch⟩

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- TEMPORARY: removed in D3.3e. The frontier adapter of the top-down switch
(`docs/d3-design.md` §8.5): a switched module passes `h𝔭.toMin` to a not-yet-switched one
(classical through `locusPt_eq_locusIdeal`). -/
theorem LocusComp.toMin [Algebra.FiniteType ℚ A] [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ}
    {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes :=
  locusPt_eq_locusIdeal I v₀ ▸ h𝔭.min

end BezoutCounterexample.Principalization
