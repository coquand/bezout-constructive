import BezoutCounterexample.Principalization.LocalPt
import BezoutCounterexample.Principalization.LocDataPtLemmas

/-!
# Local data at an explicit point, produced (D3.4 (d), leaf)

`LocData.nonempty` (MaxLocus) goes through `local_inv`/`local_structure` (classical engine) and,
for the `⟸` direction of `iff`, recentres at every `𝔪' ∌ g` with `Chart.exists_centred`
(Noetherian, residue field integral by Zariski). At explicit points:

* `LocDataPt.nonempty`: from `local_structure_pt` at `q`, with the recentring at each explicit
  point `p ∌ g` by `Chart.exists_centred_pos` (the point `p.zAt` and its zero test). Inputs: the
  generators `I = (l)` and a chart `c₀` over `A_f` with `f ∉ q.ker` (Hilbert's basis theorem and
  `exists_chart_away` are not used).
* `exists_invAt_semicont_ptL`, `invAt_semicont_ptL`, `mem_locusPt_of_le_ptL`: the invariant exists and is
  upper semicontinuous at explicit points, and the explicit points above `locusPt` lie in the
  locus (`exists_invAt`, `invAt_semicont`, `mem_locusPt_of_le` through `local_structure_pt`);
* `LocusComp.mem_ptL`, `LocusComp.eq_p_ptL`, `LocusComp.sup_eq_top_ptL`: the component lemmas
  over these and `LocDataPt` (no `LocData.nonempty`).

`hchart` (a chart near every explicit point) is the form of `exists_chart_away` at `p.ker`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- **Local data of the maximal locus at an explicit point.** -/
theorem LocDataPt.exists_dim {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l)
    {v₀ : ℕ → ℚ} (q : Pt A) (hIq : I ≤ q.ker) (hq : InvAt I q.ker v₀) {f : A} (hf : f ∉ q.ker)
    {n : ℕ} (c₀ : Chart (Localization.Away f) n) :
    ∃ D : LocDataPt I v₀ q.ker, D.n = n ∧ D.k ≤ n := by
  obtain ⟨M', g, hg, hctrl, k, ck, ek, hkn, hsupp, hnn, hanti, hadm, hM', hcent, hbound⟩ :=
    local_structure_pt I hI l hl q hIq hf c₀
  have hinv : IsInv (Iloc I q.ker) n ek := by
    refine ⟨⟨⟨_, ek, hcent, hnn, hanti⟩, ?_, rfl⟩, fun J' hJ' => (hbound q hg J' hJ').1⟩
    have h1 := Ideal.map_mono (f := Loc.map hM') hadm
    rw [Loc.map_map_algebraMap, Loc.map_RF] at h1
    exact h1
  have hv₀ : ext0 ek = v₀ := InvAt.unique ⟨n, ek, hinv, rfl⟩ hq
  refine ⟨⟨n, M', g, hg, hctrl, k, ck, ek, hsupp, hv₀, hadm, hinv, hcent,
    fun p hg' => ⟨?_, ?_⟩, fun p hg' J' hJ' he => (hbound p hg' J' hJ').2 he⟩, rfl, hkn⟩
  · rintro ⟨-, n', e', he', hev⟩
    obtain rfl := he'.card_eq (Loc.transport (hctrl p.ker hg') ck)
    have hee : e' = ek := ext0_injective (hev.trans hv₀.symm)
    subst e'
    obtain ⟨⟨J', hJ', hJ'e⟩, -⟩ := he'
    have hRF := (hbound p hg' J' hJ').2 hJ'e
    intro i hi
    have hpos : 0 < J'.e i := by
      rw [hJ'e]; exact lt_of_le_of_ne (hinv.nonneg i) (Ne.symm ((hsupp i).2 hi))
    have hmem := (Loc.transport (hctrl p.ker hg') ck).x_mem_RF ek i ((hsupp i).2 hi)
    rw [← hRF, ← hJ'e] at hmem
    exact J'.centred.RF_le_maximalIdeal hpos hmem
  · intro hx
    set c₁ := Loc.transport (hctrl p.ker hg') ck
    obtain ⟨c'', hc'', hxx⟩ := Chart.exists_centred_pos p.dec p.zAt p.zAt_spec c₁
    have hRF : ∀ t, c''.RF ek t = c₁.RF ek t := fun t =>
      Chart.RF_congr (fun i hi => hxx i (hx i ((hsupp i).1 hi))) t
    have hadm' : Iloc I p.ker ≤ c''.RF ek 1 := by
      rw [hRF]
      have h1 := Ideal.map_mono (f := Loc.map (hctrl p.ker hg')) hadm
      rw [Loc.map_map_algebraMap, Loc.map_RF] at h1
      exact h1
    set J'' : MC (Localization.AtPrime p.ker) n := ⟨c'', ek, hc'', hinv.nonneg, hinv.anti⟩
    have hIS : IsInv (Iloc I p.ker) n ek :=
      ⟨⟨J'', hadm', rfl⟩, fun J' hJ' => (hbound p hg' J' hJ').1⟩
    exact ⟨le_of_Iloc_le (hadm'.trans (hc''.RF_le_maximalIdeal one_pos)), n, ek, hIS, hv₀⟩

/-- **Local data of the maximal locus at an explicit point.** -/
theorem LocDataPt.nonempty {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l)
    {v₀ : ℕ → ℚ} (q : Pt A) (hIq : I ≤ q.ker) (hq : InvAt I q.ker v₀) {f : A} (hf : f ∉ q.ker)
    {n : ℕ} (c₀ : Chart (Localization.Away f) n) : Nonempty (LocDataPt I v₀ q.ker) :=
  let ⟨D, _⟩ := LocDataPt.exists_dim hI l hl q hIq hq hf c₀; ⟨D⟩

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- The number of heads of local data of dimension `n` is read off `v₀`. -/
theorem LocDataPt.k_eq {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal]
    (D : LocDataPt I v₀ 𝔪) {n : ℕ} (hn : D.n = n) (hk : D.k ≤ n) :
    D.k = (Finset.univ.filter fun i : Fin n => v₀ i ≠ 0).card := by
  subst hn
  have : (Finset.univ.filter fun i : Fin D.n => v₀ i ≠ 0) =
      Finset.univ.filter fun i : Fin D.n => (i : ℕ) < D.k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← D.hv, ext0_apply, D.supp]
  rw [this, Fin.card_filter_val_lt, min_eq_right hk]

section Locus

variable {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l)
  (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
include hI hl hchart

/-- The invariant at an explicit point of `V(I)`, with the semicontinuity element. -/
theorem exists_invAt_semicont_ptL (p : Pt A) (hIp : I ≤ p.ker) :
    ∃ v, InvAt I p.ker v ∧ ∃ g : A, g ∉ p.ker ∧ ∀ q : Pt A, g ∉ q.ker → ∀ v', InvAt I q.ker v' →
      toLex v ≤ toLex v' := by
  obtain ⟨f, hf, n, ⟨c₀⟩⟩ := hchart p
  obtain ⟨M', g, hg, hctrl, k, ck, ek, hkn, hsupp, hnn, hanti, hadm, hM', hcent, hbound⟩ :=
    local_structure_pt I hI l hl p hIp hf c₀
  have hinv : IsInv (Iloc I p.ker) n ek := by
    refine ⟨⟨⟨_, ek, hcent, hnn, hanti⟩, ?_, rfl⟩, fun J' hJ' => (hbound p hg J' hJ').1⟩
    have h1 := Ideal.map_mono (f := Loc.map hM') hadm
    rw [Loc.map_map_algebraMap, Loc.map_RF] at h1
    exact h1
  refine ⟨_, ⟨n, ek, hinv, rfl⟩, g, hg, fun q hg' v' hv' => ?_⟩
  obtain ⟨n', e', he', rfl⟩ := hv'
  obtain rfl := he'.card_eq (Loc.transport (hctrl q.ker hg') ck)
  obtain ⟨⟨J', hJ', hJ'e⟩, -⟩ := he'
  have := (hbound q hg' J' hJ').1
  rw [hJ'e] at this
  exact ext0_le this

/-- **Upper semicontinuity of the invariant, at explicit points.** -/
theorem invAt_semicont_ptL (p : Pt A) (hIp : I ≤ p.ker) {v : ℕ → ℚ} (hv : InvAt I p.ker v) :
    ∃ g : A, g ∉ p.ker ∧ ∀ q : Pt A, g ∉ q.ker → ∀ v', InvAt I q.ker v' → toLex v ≤ toLex v' := by
  obtain ⟨w, hw, hg⟩ := exists_invAt_semicont_ptL hI l hl hchart p hIp
  obtain rfl := hv.unique hw
  exact hg

variable {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
include hmax

/-- **The maximal locus is closed, at points** (`mem_locusPt_of_le` through `local_structure_pt`). -/
theorem mem_locusPt_of_le_ptL {N : ℕ}
    (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (hb₀ : ∀ i, N ≤ i → v₀ i = 0) (p : Pt A) (hle : locusPt I v₀ ≤ p.ker) :
    I ≤ p.ker ∧ InvAt I p.ker v₀ := by
  have hIp : I ≤ p.ker := (le_locusPt I v₀).trans hle
  refine ⟨hIp, ?_⟩
  obtain ⟨v, hv, g, hg, hgv⟩ := exists_invAt_semicont_ptL hI l hl hchart p hIp
  rcases eq_or_ne_bounded (hbd _ _ hv) hb₀ with heq | hne
  · exact heq ▸ hv
  · exfalso
    have hlt : toLex v₀ < toLex v := lt_of_le_of_ne (hmax _ hIp v hv)
      (fun h => hne (toLex.injective h).symm)
    refine hg (hle fun q _ hvq => ?_)
    rcases q.mem_ker_dec g with h | h
    · exact h
    · exact absurd (hgv q h v₀ hvq) (not_le.2 hlt)

namespace LocusComp

variable {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭)
include h𝔭

/-- **The points of a component lie in the maximal locus.** -/
theorem mem_ptL (p : Pt A) (h : 𝔭 ≤ p.ker) : I ≤ p.ker ∧ InvAt I p.ker v₀ := by
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  exact mem_locusPt_of_le_ptL hI l hl hchart hmax hbd hb₀ p (h𝔭.le.trans h)

omit hI hl hchart hmax in
/-- **The component is the prime of local data at any of its points.** -/
theorem eq_p_ptL [Fact (HasPres A)] {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocDataPt I v₀ 𝔪)
    (h : 𝔭 ≤ 𝔪) : 𝔭 = D.p := by
  have := h𝔭.isPrime
  have hp : D.p ≤ 𝔭 := D.p_le_of_le_pt h𝔭.le h
  exact le_antisymm (h𝔭.min.2 ⟨inferInstance, D.locusPt_le_p⟩ hp) hp

/-- **Distinct components are comaximal** (`sup_eq_top` with `LocDataPt.nonempty`). -/
theorem sup_eq_top_ptL [hpA : Fact (HasPres A)] {𝔭' : Ideal A} (h𝔭' : LocusComp I v₀ 𝔭')
    (hne : 𝔭 ≠ 𝔭') : 𝔭 ⊔ 𝔭' = ⊤ := by
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
    obtain ⟨hIp, hv⟩ := h𝔭.mem_ptL hI l hl hchart hmax p (le_sup_left.trans hp)
    obtain ⟨f, hf, n, ⟨c₀⟩⟩ := hchart p
    obtain ⟨D⟩ := LocDataPt.nonempty hI l hl p hIp hv hf c₀
    exact absurd ((h𝔭.eq_p_ptL D (le_sup_left.trans hp)).trans
      (h𝔭'.eq_p_ptL D (le_sup_right.trans hp)).symm) hne

end LocusComp

end Locus

/-! ### The component lemmas at points, with the data of `LocusComp` (signatures of the
classical ones) -/

namespace LocusComp

/-- `LocusComp.mem` through `mem_ptL`, with the generators and charts carried by `h𝔭`. -/
theorem memP {I : Ideal A} {v₀ : ℕ → ℚ} {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (hI : I ≠ ⊥)
    (hmax : IsMaxInvPt I v₀)
    (p : Pt A) (h : 𝔭 ≤ p.ker) : I ≤ p.ker ∧ InvAt I p.ker v₀ := by
  obtain ⟨l, hl⟩ := h𝔭.gensI
  exact h𝔭.mem_ptL hI l hl h𝔭.hchart hmax p h

/-- `LocusComp.sup_eq_top` through `sup_eq_top_ptL`, with the data carried by `h𝔭`. -/
theorem sup_eq_topP [Fact (HasPres A)] {I : Ideal A} {v₀ : ℕ → ℚ} {𝔭 : Ideal A}
    (h𝔭 : LocusComp I v₀ 𝔭) (hI : I ≠ ⊥)
    (hmax : IsMaxInvPt I v₀)
    {𝔭' : Ideal A} (h𝔭' : LocusComp I v₀ 𝔭') (hne : 𝔭 ≠ 𝔭') : 𝔭 ⊔ 𝔭' = ⊤ := by
  obtain ⟨l, hl⟩ := h𝔭.gensI
  exact h𝔭.sup_eq_top_ptL hI l hl h𝔭.hchart hmax h𝔭' hne

end LocusComp

end BezoutCounterexample.Principalization
