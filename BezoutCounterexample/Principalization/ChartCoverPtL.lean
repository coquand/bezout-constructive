import BezoutCounterexample.Principalization.ComponentFilPt
import BezoutCounterexample.Principalization.LocDataPtProd

/-!
# Chart covers by local data at explicit points (D3.4 (e), leaf)

`ChartCoverPt` (ComponentFilPt) carries `LocData` (properties at all maximal ideals, classical
producer). `ChartCoverPtL` is the same cover with `LocDataPt` (properties at explicit points):

* `ChartCoverPtL`, `ChartCoverPtL.cover` (the shape of coll-8a's producers: a finite family
  `k ↦ D k` with `∀ p, 𝔭 ≤ p.ker → ∃ k, (D k).g ∉ p.ker`, decided by the points' zero test);
* `ChartCoverPt.toL`: the current instance (`LocData.toPt`);
* `LocDataPt.restrict`: shrinking `D(g)` to `D(g h)`;
* `LocusComp.exists_chartCoverPtL`: `exists_chartCoverPt` with `LocDataPt.exists_dim`,
  `LocusComp.mem_ptL` and `LocusComp.sup_eq_top_ptL` in place of `LocData.nonempty`; inputs:
  generators `I = (l₀)` and a chart of a fixed dimension `dim` near every explicit point
  (`hchartn`, from the smoothness certificate). Output shapes: `(C.D k).n = dim` and
  `(C.D k).k = #{i < dim | v₀ i ≠ 0}` for all `k`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- **A cover of `V(𝔭)` by local data at explicit points**, separated over points, with
`LocDataPt`. -/
structure ChartCoverPtL (I : Ideal A) (v₀ : ℕ → ℚ) (𝔭 : Ideal A) where
  n : ℕ
  pt : Fin n → Pt A
  le : ∀ k, 𝔭 ≤ (pt k).ker
  D : ∀ k, LocDataPt I v₀ (pt k).ker
  f : Fin n → A
  i : A
  hi : i ∈ 𝔭
  one : i + ∑ k, f k * (D k).g = 1
  sep : ∀ k (p : Pt A), (D k).g ∉ p.ker → I ≤ p.ker → InvAt I p.ker v₀ → 𝔭 ≤ p.ker

namespace ChartCoverPtL

variable {I : Ideal A} {v₀ : ℕ → ℚ} {𝔭 : Ideal A} (C : ChartCoverPtL I v₀ 𝔭)

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- **The cover property**: every explicit point of `V(𝔭)` lies in some `D(g_k)`. -/
theorem cover (p : Pt A) (h𝔭p : 𝔭 ≤ p.ker) : ∃ k, (C.D k).g ∉ p.ker := by
  rcases list_exists_or_forall (P := fun k => (C.D k).g ∉ p.ker)
      (fun k => (p.mem_ker_dec (C.D k).g).elim (fun h => Or.inr fun h' => h' h) Or.inl)
      (List.finRange C.n) with ⟨k, -, hk⟩ | hall
  · exact ⟨k, hk⟩
  · exfalso
    have hg : ∀ k, (C.D k).g ∈ p.ker := fun k =>
      (p.mem_ker_dec (C.D k).g).elim id fun h => absurd h (hall k (List.mem_finRange k))
    have h1 : (1 : A) ∈ p.ker := by
      rw [← C.one]
      exact Ideal.add_mem _ (h𝔭p C.hi)
        (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hg k))
    exact (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h1)

end ChartCoverPtL

variable [IsNoetherianRing A] in
/-- The current instance: a `ChartCoverPt` forgets to a `ChartCoverPtL`. -/
def ChartCoverPt.toL {I : Ideal A} {v₀ : ℕ → ℚ} {𝔭 : Ideal A} (C : ChartCoverPt I v₀ 𝔭) :
    ChartCoverPtL I v₀ 𝔭 :=
  ⟨C.n, C.pt, C.le, fun k => (C.D k).toPt, C.f, C.i, C.hi, C.one, C.sep⟩

/-- Restricting local data at points to `D(g h)`. -/
def LocDataPt.restrict {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal]
    (D : LocDataPt I v₀ 𝔪) (h : A) (hh : h ∉ 𝔪) : LocDataPt I v₀ 𝔪 where
  n := D.n
  M := D.M
  g := D.g * h
  hg := fun hm => (Ideal.IsPrime.mem_or_mem inferInstance hm).elim D.hg hh
  ctrl := ⟨fun P _ hP => D.ctrl P fun hg => hP (Ideal.mul_mem_right _ _ hg), fun m hm =>
    (D.ctrl.dvd m hm).imp fun b hb => hb.trans (pow_dvd_pow_of_dvd (dvd_mul_right _ _) b)⟩
  k := D.k
  ck := D.ck
  ek := D.ek
  supp := D.supp
  hv := D.hv
  adm := D.adm
  inv := D.inv
  cent := D.cent
  iff := fun p hg' => D.iff p fun h1 => hg' (Ideal.mul_mem_right _ _ h1)
  rf := fun p hg' => D.rf p fun h1 => hg' (Ideal.mul_mem_right _ _ h1)

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)

namespace LocusComp

variable {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭)
include hI hmax h𝔭

/-- **Separated chart covers by local data at explicit points** (`exists_chartCoverPt` with
`LocDataPt.nonempty`). -/
theorem exists_chartCoverPtL [hpA : Fact (HasPres A)] (l₀ : List A) (hl₀ : I = lspan l₀)
    (dim : ℕ) (hchartn : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) dim)) :
    ∃ C : ChartCoverPtL I v₀ 𝔭, (∀ k, (C.D k).n = dim) ∧
      ∀ k, (C.D k).k = (Finset.univ.filter fun i : Fin dim => v₀ i ≠ 0).card := by
  have hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ,
      Nonempty (Chart (Localization.Away f) n) := fun p => by
    obtain ⟨f, hf, hc⟩ := hchartn p
    exact ⟨f, hf, dim, hc⟩
  have hp : HasPres A := hpA.out
  obtain ⟨Pg, hPg⟩ := h𝔭.Pg
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  obtain ⟨Cs, hCs⟩ := hp.exists_compList Pg
  obtain ⟨C, hCm, hCe⟩ := hCs.exists_eq_of_mem_minimalPrimes (hPg ▸ h𝔭.min)
  -- the separating element
  obtain ⟨K, hK⟩ := HasPres.exists_colon hp Pg C
  have hcomax : ∀ D ∈ Cs, lspan D = lspan C ∨ (1 : A) ∈ lspan C ⊔ lspan D := fun D hDm => by
    rcases hp.eq_dec D C with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [(hCs.locusComp hPg hbd hb₀ ⟨l₀, hl₀⟩ ⟨dim, hchartn⟩ hCm).sup_eq_top_ptL hI l₀ hl₀ hchart
        hmax (hCs.locusComp hPg hbd hb₀ ⟨l₀, hl₀⟩ ⟨dim, hchartn⟩ hDm) (Ne.symm h)]
      trivial
  have hrad : ∀ (x : A) (k : ℕ), x ^ k ∈ lspan Pg → x ∈ lspan Pg := fun x k hk => by
    rw [← hPg] at hk ⊢
    exact fun p hI' hv' => (inferInstance : p.ker.IsPrime).mem_of_pow_mem k (hk p hI' hv')
  obtain ⟨c, hc, q, hq, hcq⟩ := Submodule.mem_sup.1
    (hCs.one_mem_sup_colon hcomax hrad K hK)
  rw [hCe] at hc
  have h1q : 1 - q ∈ 𝔭 := by rw [← hcq, add_sub_cancel_right]; exact hc
  have hqsep : ∀ p : Pt A, q ∉ p.ker → I ≤ p.ker → InvAt I p.ker v₀ → 𝔭 ≤ p.ker :=
    fun p hqp hI' hv' y hy => by
      have hqy : q * y ∈ locusPt I v₀ := by
        rw [hPg]; exact (hK q).1 hq y (hCe ▸ hy)
      exact ((inferInstance : p.ker.IsPrime).mem_or_mem (hqy p hI' hv')).resolve_left hqp
  -- the cover
  obtain ⟨Cg, hCg, -⟩ := h𝔭.gens
  have hsup : ∀ l : List A, 𝔭 ⊔ lspan l = lspan (Cg ++ l) := fun l => by
    rw [hCg, lspan_append_eq]
  let good : A → Prop := fun g => ∃ (p : Pt A) (D : LocDataPt I v₀ p.ker),
    D.n = dim ∧ D.k ≤ dim ∧ 𝔭 ≤ p.ker ∧ D.g = g ∧ ∀ p' : Pt A, D.g ∉ p'.ker → I ≤ p'.ker → InvAt I p'.ker v₀ →
      𝔭 ≤ p'.ker
  obtain ⟨l, hl, h1⟩ := exists_cover 𝔭 (indNoeth_quotient_of_hasPres hp 𝔭) good
    (fun l => by rw [hsup]; exact hp.mem_dec _ 1) fun l _ hl1 => by
    rw [hsup] at hl1
    obtain ⟨p, hle⟩ := HasPres.exists_pt hp _ hl1
    rw [← hsup] at hle
    have h𝔭p : 𝔭 ≤ p.ker := le_sup_left.trans hle
    obtain ⟨hIp, hv⟩ := h𝔭.mem_ptL hI l₀ hl₀ hchart hmax p h𝔭p
    obtain ⟨f₀, hf₀, ⟨c₀⟩⟩ := hchartn p
    obtain ⟨D, hDn, hDk⟩ := LocDataPt.exists_dim hI l₀ hl₀ p hIp hv hf₀ c₀
    have hqp : q ∉ p.ker := fun h => (Ideal.IsMaximal.ne_top inferInstance)
      ((Ideal.eq_top_iff_one _).2 (by
        have := Ideal.add_mem _ (h𝔭p h1q) h
        rwa [sub_add_cancel] at this))
    let D' := D.restrict q hqp
    exact ⟨D'.g, ⟨p, D', hDn, hDk, h𝔭p, rfl, fun p' hg' hI' hv' =>
      hqsep p' (fun h => hg' (Ideal.mul_mem_left _ _ h)) hI' hv'⟩, fun h => D'.hg (hle h)⟩
  have hcov : (1 : A) ∈ 𝔭 ⊔ Ideal.span {g | good g} := by
    refine (sup_le_sup_left ?_ 𝔭) h1
    rw [lspan, Ideal.span_le]
    intro g hg; exact Ideal.subset_span (hl g hg)
  obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 hcov
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hy
  obtain ⟨F⟩ := fin_nonempty_pi (X := fun k : Fin n =>
    Σ' (p : Pt A), {D : LocDataPt I v₀ p.ker //
      D.n = dim ∧ D.k ≤ dim ∧ 𝔭 ≤ p.ker ∧ D.g = (g k : A) ∧ ∀ p' : Pt A, D.g ∉ p'.ker → I ≤ p'.ker →
        InvAt I p'.ker v₀ → 𝔭 ≤ p'.ker}) fun k => by
    obtain ⟨p, D, hDn, hDk, hle, hDg, hsep⟩ := (g k).2
    exact ⟨⟨p, D, hDn, hDk, hle, hDg, hsep⟩⟩
  refine ⟨⟨n, fun k => (F k).1, fun k => (F k).2.2.2.2.1, fun k => (F k).2.1, f, i, hi, ?_,
    fun k => (F k).2.2.2.2.2.2⟩, fun k => (F k).2.2.1,
    fun k => (F k).2.1.k_eq (F k).2.2.1 (F k).2.2.2.1⟩
  rw [← hiy, ← hfg]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, (F k).2.2.2.2.2.1]

end LocusComp

end BezoutCounterexample.Principalization
