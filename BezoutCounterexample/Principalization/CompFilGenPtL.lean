import BezoutCounterexample.Principalization.SpanSPtL

/-!
# I2, R3 and generation in bounded degrees over a `ChartCoverPtL` (leaf)

The R3 lemma `compFil_loc_F_pt` and the generation lemma `compFil_le_iSup` (ReesGlobal) take their
chart cover from `LocusComp.exists_chartCoverPt` (`LocData.nonempty`, the classical local structure)
and use `LocusComp.mem`/`exists_pow_mem_compFPt`. Twins over `exists_chartCoverPtL`:

* `ChartCoverPtL.map_compFPt_pt_L` (R3), `compFil_loc_F_ptL` (I2, `map_compFPt_L`, is in CompFilDecPtL);
* `compFil_le_iSup_ptL`, `C_mul_T_mem_adjoin_set_ptL`, `C_mul_T_mem_adjoin_of_ptL`.

The proofs are those of ComponentFilPt / ReesGlobal with the cover, `mem_ptL` and
`exists_pow_mem_compFPt_ptL`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

namespace ChartCoverPtL

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} (lI : List A) (hlI : I = lspan lI)
  (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
  {𝔭 : Ideal A} (C : ChartCoverPtL I v₀ 𝔭)
  (hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀)
include hI lI hlI hchart hZ C

/-- **R3 over a `ChartCoverPtL`**: the filtration at one point is the centre's weighted ideal. -/
theorem map_compFPt_pt_L [Fact (HasPres A)] (t : ℚ) (p : Pt A) (h𝔭p : 𝔭 ≤ p.ker) :
    (compFPt I 𝔭 t).map (algebraMap A (Localization.AtPrime p.ker)) = cRF I p.ker t := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_compFPt.1 hx p h𝔭p
  obtain ⟨k, hk⟩ := C.cover p h𝔭p
  obtain ⟨hI', hv'⟩ := hZ p h𝔭p
  have hcomp : (Loc.map ((C.D k).ctrlN p.ker hk)).comp (algebraMap A (C.D k).B) =
      algebraMap A (Localization.AtPrime p.ker) :=
    RingHom.ext ((C.D k).map_algebraMap_B p hk)
  rw [← (C.D k).RFB_map_of_mem_L p hk hv', ← C.map_compFPt_L hI lI hlI hchart hZ t k, Ideal.map_map,
    hcomp]

end ChartCoverPtL

variable [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) (lI : List A) (hlI : I = lspan lI) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {dim : ℕ}
  (hchartn : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) dim))

include hI lI hlI hmax h𝔭 hchartn in
/-- **R3 for a component at points** (twin of `compFil_loc_F_pt`). -/
lemma compFil_loc_F_ptL [Fact (Constructive.HasPres A)] (d : ℕ) (p : Pt A) (h𝔭p : 𝔭 ≤ p.ker)
    (j : ℤ) :
    ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime p.ker)).F j = cRF I p.ker ((j : ℚ) / d) := by
  have hchart := LocusComp.hchart_of_dim hI lI hlI hmax h𝔭 hchartn
  obtain ⟨C, -, -⟩ := h𝔭.exists_chartCoverPtL hI hmax lI hlI dim hchartn
  exact C.map_compFPt_pt_L hI lI hlI hchart (fun q h => h𝔭.mem_ptL hI lI hlI hchart hmax q h) _ p h𝔭p

variable {d : ℕ} (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI lI hlI hmax h𝔭 hchartn hd hw

/-- **Generation in bounded degrees**: `F_j = ∑_{1 ≤ l ≤ d} F_l F_{j-l}` for `j > d`.
Constructive (D3.3d): comaximal local–global over a chart cover at points (`ChartCoverPt`,
`Ideal.mem_of_cover`). On `D(i)`, `i ∈ 𝔭`, a power of `i` lies in `F_1 F_{j-1}` (I3); on the chart
`D(gₖ)`, `F_t` is the chart ideal (I2) and a monomial of weight `≥ j/d` splits off one coordinate
`x_i` of weight `wᵢ/d`, `1 ≤ wᵢ ≤ d`. -/
theorem compFil_le_iSup_ptL [Fact (Constructive.HasPres A)] {j : ℤ} (hj : (d : ℤ) < j) :
    (compFil hI hmax h𝔭 d).F j ≤
      ⨆ l ∈ Finset.Icc (1 : ℤ) d, (compFil hI hmax h𝔭 d).F l * (compFil hI hmax h𝔭 d).F (j - l) := by
  set Φ := compFil hI hmax h𝔭 d
  set Rj := ⨆ l ∈ Finset.Icc (1 : ℤ) d, Φ.F l * Φ.F (j - l)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hR : ∀ l : ℤ, 1 ≤ l → l ≤ d → Φ.F l * Φ.F (j - l) ≤ Rj := fun l h1 h2 =>
    le_iSup₂_of_le (f := fun l (_ : l ∈ Finset.Icc (1 : ℤ) d) => Φ.F l * Φ.F (j - l)) l
      (Finset.mem_Icc.2 ⟨h1, h2⟩) le_rfl
  have hchart := LocusComp.hchart_of_dim hI lI hlI hmax h𝔭 hchartn
  obtain ⟨C, -, -⟩ := h𝔭.exists_chartCoverPtL hI hmax lI hlI dim hchartn
  have hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀ :=
    fun p h => h𝔭.mem_ptL hI lI hlI hchart hmax p h
  intro x hx
  have h1 : (1 : A) ∈ Constructive.lspan (C.i :: List.ofFn fun k => (C.D k).g) := by
    rw [← C.one]
    refine Ideal.add_mem _ (Ideal.subset_span List.mem_cons_self)
      (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
    exact List.mem_cons_of_mem _ (List.mem_ofFn.2 ⟨k, rfl⟩)
  refine Ideal.mem_of_cover _ h1 fun g hg => ?_
  rcases List.mem_cons.1 hg with rfl | hg
  · -- `D(i)`: `i^(b + b') ∈ F_1 F_{j-1}`
    obtain ⟨b, hb⟩ := h𝔭.exists_pow_mem_compFPt_ptL hI lI hlI hchart hmax hd hw C.hi (((1 : ℤ) : ℚ) / d)
    obtain ⟨b', hb'⟩ := h𝔭.exists_pow_mem_compFPt_ptL hI lI hlI hchart hmax hd hw C.hi (((j - 1 : ℤ) : ℚ) / d)
    have hb1 : C.i ^ b ∈ Φ.F 1 := hb
    have hb2 : C.i ^ b' ∈ Φ.F (j - 1) := hb'
    refine ⟨b + b', ?_⟩
    rw [pow_add]
    exact Ideal.mul_mem_right _ _ (hR 1 le_rfl (by exact_mod_cast hd) (Ideal.mul_mem_mul hb1 hb2))
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hg
  set D := C.D k
  have hmap : ∀ l : ℤ, (Φ.F l).map (algebraMap A D.B) = D.RFB ((l : ℚ) / d) := fun l =>
    C.map_compFPt_L hI lI hlI hchart hZ _ k
  refine exists_pow_mul_mem_of_away D.g D.B ?_
  have hxB : algebraMap A D.B x ∈ D.RFB ((j : ℚ) / d) := by
    rw [← hmap]; exact Ideal.mem_map_of_mem _ hx
  have hI' : I ≤ (C.pt k).ker := (hZ _ (C.le k)).1
  revert hxB
  generalize algebraMap A D.B x = y
  intro hy
  refine (show D.RFB ((j : ℚ) / d) ≤ Rj.map (algebraMap A D.B) from ?_) hy
  rw [LocDataPt.RFB, Chart.RF, Ideal.span_le]
  rintro _ ⟨α, h0, hα, rfl⟩
  -- pick a coordinate occurring in `α` (decided coordinatewise)
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    rcases Constructive.fin_forall_or_exists (A := fun i => α i = 0) (B := fun i => α i ≠ 0)
      (fun i => (Nat.decEq (α i) 0).em) with h | h
    · exfalso
      rw [show α = 0 from Finsupp.ext h, lam_zero] at hα
      have : (0 : ℚ) < (j : ℚ) / d := div_pos (by exact_mod_cast (by omega : (0 : ℤ) < j)) hdq
      linarith
    · exact h
  have hei : D.ek i ≠ 0 := fun h => hi (h0 i h)
  have hv : D.ek i = v₀ i := by
    have := congrFun D.hv i
    rwa [ext0_apply] at this
  obtain ⟨w, hw'⟩ := hw i
  rw [← hv] at hw'
  have hle1 : D.ek i ≤ 1 := D.inv.le_one (Iloc_le hI') i
  have hpos : 0 < D.ek i := lt_of_le_of_ne (D.inv.nonneg i) (Ne.symm hei)
  have hw1 : 1 ≤ w := by
    have : (0 : ℚ) < w := by rw [hw']; positivity
    exact_mod_cast this
  have hwd : w ≤ d := by
    have : (w : ℚ) ≤ d := by rw [hw']; nlinarith
    exact_mod_cast this
  have hei' : D.ek i = (w : ℚ) / d := by rw [hw']; field_simp
  -- split off `x_i`
  set β := α - Finsupp.single i 1
  have hαβ : α = β + Finsupp.single i 1 := by
    rw [tsub_add_cancel_of_le]
    exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
  have hprod : ∏ l, D.cB.x l ^ α l = D.cB.x i * ∏ l, D.cB.x l ^ β l := by
    rw [hαβ]
    simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [mul_comm, Finset.prod_eq_single i]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · simp
  have hlamβ : lam D.ek β = lam D.ek α - D.ek i := by
    rw [hαβ, lam_add, lam_single]; ring
  have h1 : D.cB.x i ∈ D.RFB (((w : ℤ) : ℚ) / d) := by
    have := D.cB.x_mem_RF D.ek i hei
    rw [hei'] at this; push_cast; exact this
  have h2 : ∏ l, D.cB.x l ^ β l ∈ D.RFB (((j - w : ℤ) : ℚ) / d) := by
    apply Ideal.subset_span
    refine ⟨β, fun l hl => ?_, ?_, rfl⟩
    · have := h0 l hl
      rw [hαβ, Finsupp.add_apply] at this
      omega
    · rw [hlamβ, hei']
      push_cast
      rw [sub_div]
      linarith
  rw [SetLike.mem_coe, hprod]
  refine Ideal.map_mono (hR w (by exact_mod_cast hw1) (by exact_mod_cast hwd)) ?_
  rw [Ideal.map_mul, hmap, hmap]
  exact Ideal.mul_mem_mul h1 h2


/-- **R2, generic in the generators**: every homogeneous element lies in the algebra generated by
`T⁻¹` and `g T^j` for `g` in a generating set of `F_j`, `1 ≤ j ≤ d`. -/
theorem C_mul_T_mem_adjoin_set_ptL [Fact (Constructive.HasPres A)] (gens : ℤ → Set A)
    (hgens : ∀ j : ℤ, 1 ≤ j → j ≤ d → Ideal.span (gens j) = (compFil hI hmax h𝔭 d).F j)
    (j : ℤ) (f : A) (hf : f ∈ (compFil hI hmax h𝔭 d).F j) :
    LaurentPolynomial.C f * T j ∈ Algebra.adjoin A ({T (-1)} ∪ ⋃ j ∈ Finset.Icc (1 : ℤ) d,
      (fun g => LaurentPolynomial.C g * T j) '' gens j) := by
  set R' := Algebra.adjoin A ({T (-1)} ∪ ⋃ j ∈ Finset.Icc (1 : ℤ) d,
      (fun g => LaurentPolynomial.C g * T j) '' gens j)
  set Φ := compFil hI hmax h𝔭 d
  -- the ideal of coefficients in degree `j`
  let Mj : ℤ → Ideal A := fun j =>
    (Subalgebra.toSubmodule R').comap ((LinearMap.lsmul A A[T;T⁻¹]).flip (T j))
  have hMj : ∀ j f, f ∈ Mj j ↔ LaurentPolynomial.C f * T j ∈ R' := fun j f => by
    show f • (T j : A[T;T⁻¹]) ∈ R' ↔ _
    rw [Algebra.smul_def, ← LaurentPolynomial.C_eq_algebraMap]
  have base : ∀ j : ℤ, j ≤ d → ∀ f ∈ Φ.F j, LaurentPolynomial.C f * T j ∈ R' := by
    intro j hjd f hf
    by_cases hj0 : j ≤ 0
    · have h1 : (LaurentPolynomial.C f * T j : A[T;T⁻¹]) =
          algebraMap A A[T;T⁻¹] f * (T (-1)) ^ (-j).toNat := by
        rw [← LaurentPolynomial.C_eq_algebraMap, T_pow]
        congr 2
        omega
      rw [h1]
      exact R'.mul_mem (R'.algebraMap_mem f)
        (R'.pow_mem (Algebra.subset_adjoin (Or.inl rfl)) _)
    · have hj1 : 1 ≤ j := by omega
      rw [← hMj]
      have hle : Φ.F j ≤ Mj j := by
        rw [← hgens j hj1 hjd, Ideal.span_le]
        intro g hg
        rw [SetLike.mem_coe, hMj]
        apply Algebra.subset_adjoin
        right
        simp only [Set.mem_iUnion, Set.mem_image]
        exact ⟨j, Finset.mem_Icc.2 ⟨hj1, hjd⟩, g, hg, rfl⟩
      exact hle hf
  have main : ∀ N : ℕ, ∀ j : ℤ, j ≤ N → ∀ f ∈ Φ.F j, LaurentPolynomial.C f * T j ∈ R' := by
    intro N
    induction N with
    | zero => intro j hj f hf; exact base j (by omega) f hf
    | succ N ih =>
      intro j hj f hf
      by_cases hjd : j ≤ d
      · exact base j hjd f hf
      · push Not at hjd
        rw [← hMj]
        have hsup := compFil_le_iSup_ptL hI lI hlI hmax h𝔭 hchartn hd hw hjd hf
        refine (iSup₂_le fun l hl => ?_ : _ ≤ Mj j) hsup
        rw [Ideal.mul_le]
        intro a ha b hb
        rw [hMj]
        have hl' := Finset.mem_Icc.1 hl
        have h1 := base l (by omega) a ha
        have h2 := ih (j - l) (by push_cast at hj ⊢; omega) b hb
        have : (LaurentPolynomial.C (a * b) * T j : A[T;T⁻¹]) =
            (LaurentPolynomial.C a * T l) * (LaurentPolynomial.C b * T (j - l)) := by
          rw [map_mul, show j = l + (j - l) by ring, T_add]
          ring_nf
        rw [this]; exact R'.mul_mem h1 h2
  exact main j.toNat j (Int.self_le_toNat j) f hf


/-- `C_mul_T_mem_adjoin_of` through `C_mul_T_mem_adjoin_set_ptL`. -/
theorem C_mul_T_mem_adjoin_of_ptL [Fact (Constructive.HasPres A)] (gens : ℤ → List A)
    (hgens : ∀ j : ℤ, 1 ≤ j → j ≤ d → Constructive.lspan (gens j) = (compFil hI hmax h𝔭 d).F j)
    (j : ℤ) (f : A) (hf : f ∈ (compFil hI hmax h𝔭 d).F j) :
    LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (reesGenSetOf d gens) :=
  C_mul_T_mem_adjoin_set_ptL hI lI hlI hmax h𝔭 hchartn hd hw (fun j => {g | g ∈ gens j}) hgens j f hf

end BezoutCounterexample.Principalization
