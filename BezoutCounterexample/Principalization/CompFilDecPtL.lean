import BezoutCounterexample.Principalization.ChartCoverPtLGlue
import BezoutCounterexample.Principalization.LocDataPtProd

/-!
# Deciding membership in the filtration at points (leaf; (A) step A1)

`hF_of_cover` (HFDec) decides `x ∈ F_t` from the generators of `LocusComp.exists_lspan_compFPt`,
whose cover comes from `exists_chartCoverPt` and `LocusComp.mem` (classical locus). Here the same
R2 argument runs over a `ChartCoverPtL` (local data at explicit points):

* `ChartCoverPtL.exists_lspan_compFPt`: each chart ideal `RFB_k t` is contracted to `A`
  (`HasPres.exists_contract`) and the contractions are intersected (`HasPres.exists_inter_fin`),
  by `ChartCoverPtL.mem_compFPt_iff`;
* `LocusComp.exists_lspan_compFPt_ptL`, `LocusComp.compFPt_dec_ptL`: with the cover of
  `exists_chartCoverPtL` and `mem_ptL`, then `HasPres.mem_dec`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} (l : List A) (hl : I = lspan l)
  (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))

namespace ChartCoverPtL

variable {𝔭 : Ideal A} (C : ChartCoverPtL I v₀ 𝔭)
  (hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀)
include hI l hl hchart hZ C

/-- **I2 over a `ChartCoverPtL`**: on each open of the cover, the filtration is the chart ideal. -/
theorem map_compFPt_L [Fact (HasPres A)] (t : ℚ) (k : Fin C.n) :
    (compFPt I 𝔭 t).map (algebraMap A (C.D k).B) = (C.D k).RFB t := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact (C.mem_compFPt_iff hI l hl hchart hZ t x).1 hx k
  intro y hy
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (C.D k).N y
  have ha : algebraMap A (C.D k).B a ∈ (C.D k).RFB t := by
    have := (C.D k).RFB t |>.mul_mem_right (algebraMap A _ (s : A)) hy
    rwa [IsLocalization.mk'_spec] at this
  obtain ⟨M, hM⟩ := exists_uniform_list
    (P := fun j m => algebraMap A (C.D j).B ((C.D k).g ^ m * a) ∈ (C.D j).RFB t)
    (fun j m n hmn hm => by
      rw [← Nat.sub_add_cancel hmn, pow_add, mul_assoc, map_mul]
      exact Ideal.mul_mem_left _ _ hm)
    (List.finRange C.n) fun j _ => (C.D k).exists_pow_mul_mem_pt hI (C.D j) a t ha
  have hmem : (C.D k).g ^ M * a ∈ compFPt I 𝔭 t :=
    (C.mem_compFPt_iff hI l hl hchart hZ t _).2 fun j => hM j (List.mem_finRange j)
  have h1 := Ideal.mem_map_of_mem (algebraMap A (C.D k).B) hmem
  have hgu : IsUnit (algebraMap A (C.D k).B ((C.D k).g ^ M)) :=
    IsLocalization.map_units _ (⟨(C.D k).g ^ M,
      (C.D k).N.pow_mem (le_sup_right (a := (C.D k).M) (Submonoid.mem_powers _)) M⟩ : (C.D k).N)
  rw [map_mul] at h1
  have h2 := (Ideal.unit_mul_mem_iff_mem _ hgu).1 h1
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact Ideal.mul_mem_right _ _ h2

/-- **R2 over a `ChartCoverPtL`**: the steps of the filtration are explicitly finitely generated. -/
theorem exists_lspan_compFPt [hpA : Fact (HasPres A)] (t : ℚ) :
    ∃ L : List A, compFPt I 𝔭 t = lspan L := by
  have hp : HasPres A := hpA.out
  have hN : ∀ k, ∃ N : List A, ∀ x : A,
      algebraMap A (C.D k).B x ∈ (C.D k).RFB t ↔ x ∈ lspan N := by
    intro k
    obtain ⟨l, hl⟩ := (C.D k).cB.RF_eq_lspan (C.D k).ek (C.D k).inv.nonneg t
    obtain ⟨N, hN⟩ := HasPres.exists_contract hp (C.D k).g (C.D k).B l
    exact ⟨N, fun y => by rw [LocDataPt.RFB, hl]; exact hN y⟩
  obtain ⟨N, hN⟩ := Constructive.finite_choice_dep hN
  obtain ⟨L, hL⟩ := hp.exists_inter_fin C.n N
  refine ⟨L, Ideal.ext fun x => ?_⟩
  rw [C.mem_compFPt_iff hI l hl hchart hZ t x, hL]
  exact forall_congr' fun k => hN k x

end ChartCoverPtL

namespace LocusComp

variable (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {dim : ℕ}
  (hchartn : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) dim))
include hI l hl hmax h𝔭 hchartn

omit [IsDomain A] in
lemma hchart_of_dim : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ,
    Nonempty (Chart (Localization.Away f) n) := fun p => by
  obtain ⟨f, hf, hc⟩ := hchartn p
  exact ⟨f, hf, dim, hc⟩

/-- **R2 for a component at points** (no `exists_chartCoverPt`, no `LocusComp.mem`). -/
theorem exists_lspan_compFPt_ptL [Fact (HasPres A)] (t : ℚ) :
    ∃ L : List A, compFPt I 𝔭 t = lspan L := by
  have hchart := hchart_of_dim hI l hl hmax h𝔭 hchartn
  obtain ⟨C, -, -⟩ := h𝔭.exists_chartCoverPtL hI hmax l hl dim hchartn
  exact C.exists_lspan_compFPt hI l hl hchart (fun p h => h𝔭.mem_ptL hI l hl hchart hmax p h) t

/-- **Membership in `F_t` is decided** (twin of `hF_of_cover`). -/
theorem compFPt_dec_ptL [hpA : Fact (HasPres A)] (t : ℚ) (x : A) :
    x ∈ compFPt I 𝔭 t ∨ x ∉ compFPt I 𝔭 t := by
  obtain ⟨L, hL⟩ := h𝔭.exists_lspan_compFPt_ptL hI l hl hmax hchartn t
  rw [hL]
  exact hpA.out.mem_dec L x

end LocusComp

/-- `LocusComp.exists_lspan_compFPt` (R2) through `exists_lspan_compFPt_ptL`, with the generators
and charts carried by `h𝔭` (signature of the classical one). -/
theorem LocusComp.exists_lspan_compFPtP [Fact (HasPres A)] {I : Ideal A} {v₀ : ℕ → ℚ}
    {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (hI : I ≠ ⊥)
    (hmax : IsMaxInvPt I v₀)
    (t : ℚ) : ∃ L : List A, compFPt I 𝔭 t = lspan L := by
  obtain ⟨l, hl⟩ := h𝔭.gensI
  obtain ⟨dim, hchartn⟩ := h𝔭.chartn
  exact h𝔭.exists_lspan_compFPt_ptL hI l hl hmax hchartn t

end BezoutCounterexample.Principalization
