import BezoutCounterexample.Principalization.VertexBasePos
import BezoutCounterexample.Principalization.StepRunOfPos

/-!
# The invariant at the vertex at a decided point (leaf; (B) step B5)

Twins of `DE_stepAp`, `DE_stepAp'`, `DE_stepRp`, `vertex_invariant` (Vertex) with the residue field of
`B` decided (`hdecB`; at an explicit point: `Pt.dec_local`) and `I = (lI)`:

* `MC.SA.step_data_Q` ↦ `MC.adm_or_witness` (the admissible branch contradicts `hna`) and
  `SA.step_data_pos`;
* `MC.SA.step_run_of` ↦ `SA.step_run_of_pos` (StepRunOfPos), at the vertex with `VLoc_dec` and the
  generators `weakGens` of the weak transform (`weakV_eq_lspan`);
* `MC.sa_zero_Q` ↦ `MC.sa_zero_pos`; `VLoc_polyIndNoeth` ↦ `VLoc_polyIndNoeth_dec`.

The proofs are otherwise those of Vertex.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open LaurentPolynomial Polynomial IsLocalRing MvPowerSeries Constructive

section DEAp
variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B]
  [Fact (Constructive.PolyIndNoeth B)] {n : ℕ}
  {e : Fin n → ℚ} {d : ℕ} {Φ : WFil B}

/-- The A-side of a vertex step: Method 1 in a compatible chart has next weight `e_j`, and the
next coordinate can be chosen within the block of weight `e_j`. -/
theorem DE_stepAp (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) {k : ℕ}
    (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) (I : Ideal B)
    (hdecB : ∀ x : B, x ∈ maximalIdeal B ∨ IsUnit x) (lI : List B) (hlI : I = lspan lI) (hId : I ≤ Φ.F d)
    (hmax : ∀ J' : MC B n, J'.Adm I → toLex e ≤ toLex J'.e) {j : ℕ} (hjk : j < k) (hkn : k ≤ n)
    (c' : Chart B n) (hc' : c'.IsCentred) (hF' : ∀ m, Φ.F m = chartFil c' e d m)
    (hA : MC.SA I j ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩) :
    ∃ (β₀ : Fin n →₀ ℕ) (f₀ : B) (_hf₀ : f₀ ∈ I) (l : Fin n),
      coeff β₀ (c'.tau f₀) ≠ 0 ∧ lam (truncW e j) β₀ < 1 ∧ 0 < tailSum j β₀ ∧
      (∀ β : Fin n →₀ ℕ, (∃ g ∈ I, coeff β (c'.tau g) ≠ 0) → lam (truncW e j) β < 1 →
        Xi (truncW e j) j β₀ ≤ Xi (truncW e j) j β) ∧
      j ≤ (l : ℕ) ∧ β₀ l ≠ 0 ∧ e l = e ⟨j, by omega⟩ ∧ lam e β₀ = 1 ∧
      nextW (truncW e j) j β₀ = e ⟨j, by omega⟩ := by
  classical
  have hjn : j < n := by omega
  set jj : Fin n := ⟨j, hjn⟩ with hjjdef
  have hej : 0 < e jj := lt_of_le_of_ne (he _) (Ne.symm ((hsupp jj).2 hjk))
  have hadm' : I ≤ c'.RF e 1 := by rw [← chartFil_d c' hd, ← hF']; exact hId
  set Jc : MC B n := ⟨c', e, hc', he, hanti⟩
  have hJc : Jc.Adm I := hadm'
  have hna : ¬ MC.Adm I ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩ := by
    intro hadm
    have h1 := hmax _ hadm
    have h2 := lex_le_at h1 hjn (fun i hi => by simp [truncW, hi])
    simp only [truncW, lt_irrefl, ite_false] at h2
    exact absurd h2 (not_le.2 hej)
  obtain ⟨f₁, hf₁, β₁, hβ₁, hlt₁⟩ := (MC.adm_or_witness hdecB lI hlI
    ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩).resolve_left hna
  obtain ⟨hj, β₀, f₀, hf₀, hf₀ne, hlt₀, hN₀, hmin₀, hnext₀, hbJ₀⟩ :=
    hA.step_data_pos hdecB lI hlI hf₁ hβ₁ hlt₁
  set b := (1 - lam (truncW e j) β₀) / tailSum j β₀ with hbdef
  have hNq : (0 : ℚ) < tailSum j β₀ := by exact_mod_cast hN₀
  have hkey : lam (truncW e j) β₀ + b * tailSum j β₀ = 1 := by rw [hbdef]; field_simp; ring
  have hb_le : b ≤ e jj := (hnext₀ Jc hJc (fun i hi => by simp [Jc, truncW, hi])).2
  -- `b ≥ e_j` from maximality of `e`
  obtain ⟨l₀, hl₀, hβl₀⟩ := MC.tailSum_pos_exists hN₀
  have hb_ge : e jj ≤ b := by
    obtain ⟨hj2, hun2, hb2, u, hu, hc2, hnn2, ha2, hSA2⟩ :=
      hA.step_run_of_pos hdecB lI hlI β₀ f₀ hf₀ hf₀ne hlt₀ hN₀ hmin₀ l₀ hl₀ hβl₀
    obtain ⟨J'', hJ'', hag''⟩ := hSA2.dom0
    have h1 := hmax J'' hJ''
    have h2 := lex_le_at h1 hjn (fun i hi => by
      rw [hag'' i (by omega)]
      simp [nextE, truncW, hi])
    rw [hag'' jj (by simp [hjjdef])] at h2
    simpa [nextE, nextW, hjjdef] using h2
  have hbeq : b = e jj := le_antisymm hb_le hb_ge
  -- `λ_e(β₀) ≥ 1` by duality
  have hlam1 : 1 ≤ lam e β₀ := by
    by_contra h; push Not at h
    exact hf₀ne (hc'.coeff_tau_eq_zero_of_mem_RF he (hadm' hf₀) β₀ h)
  -- splitting `λ_e(β₀)` at `j`
  have hsum : lam e β₀ = lam (truncW e j) β₀ +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), (β₀ i : ℚ) * e i := by
    simp only [lam, truncW]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < j)]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < j)]
    have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < j),
        (β₀ i : ℚ) * (if (i : ℕ) < j then e i else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [Finset.mem_filter] at hi; rw [ite_eq_right hi.2, mul_zero]
    have h2 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j),
        (β₀ i : ℚ) * (if (i : ℕ) < j then e i else 0) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), (β₀ i : ℚ) * e i :=
      Finset.sum_congr rfl fun i hi => by rw [Finset.mem_filter] at hi; rw [ite_eq_left hi.2]
    rw [h1, h2, add_zero]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i; simp
  have htail : (tailSum j β₀ : ℚ) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), (β₀ i : ℚ) := by
    simp [tailSum]
  have hle : ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), (β₀ i : ℚ) * e i ≤
      e jj * tailSum j β₀ := by
    rw [htail, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hanti (show jj ≤ i from Fin.le_def.2 (by
      simp only [hjjdef]; exact hi.2))) (Nat.cast_nonneg _)
  have hsplit : ∀ l : Fin n, j ≤ (l : ℕ) → β₀ l ≠ 0 → e l = e jj := by
    intro l hl hβl
    by_contra hne
    have hlt : e l < e jj := lt_of_le_of_ne (hanti (Fin.le_def.2 (by simp [hjjdef]; omega))) hne
    have hless : ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), (β₀ i : ℚ) * e i <
        e jj * tailSum j β₀ := by
      rw [htail, Finset.mul_sum]
      apply Finset.sum_lt_sum
      · intro i hi
        rw [Finset.mem_filter] at hi
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hanti (show jj ≤ i from Fin.le_def.2 (by
          simp only [hjjdef]; exact hi.2))) (Nat.cast_nonneg _)
      · refine ⟨l, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩, ?_⟩
        rw [mul_comm]
        exact mul_lt_mul_of_pos_right hlt
          (show (0 : ℚ) < (β₀ l : ℚ) by exact_mod_cast Nat.pos_of_ne_zero hβl)
    have : lam e β₀ < 1 := by rw [hsum, ← hkey, hbeq]; linarith
    linarith
  obtain ⟨l, hl, hβl⟩ := MC.tailSum_pos_exists hN₀
  have hel := hsplit l hl hβl
  have hlam : lam e β₀ = 1 := by
    refine le_antisymm ?_ hlam1
    rw [hsum, ← hkey, hbeq]; linarith
  refine ⟨β₀, f₀, hf₀, l, hf₀ne, hlt₀, hN₀, hmin₀, hl, hβl, hel, hlam, ?_⟩
  rw [nextW]; exact hbeq

end DEAp

section DEStepp
variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B]
  [Fact (Constructive.PolyIndNoeth B)] {n : ℕ}
  {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} {Φ : WFil B}
  (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i)
  (hpos : ∀ j : ℤ, 0 < j → Φ.F j ≤ maximalIdeal B)

include hd in
/-- The A-side data of a vertex step, with the chart after the step. -/
theorem DE_stepAp' {k : ℕ} (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) (I : Ideal B)
    (hdecB : ∀ x : B, x ∈ maximalIdeal B ∨ IsUnit x) (lI : List B) (hlI : I = lspan lI)
    (hId : I ≤ Φ.F d) (hmax : ∀ J' : MC B n, J'.Adm I → toLex e ≤ toLex J'.e) {j : ℕ}
    (hjk : j < k) (hkn : k ≤ n)
    (c' : Chart B n) (hc' : c'.IsCentred) (hF' : ∀ m, Φ.F m = chartFil c' e d m)
    (hA : MC.SA I j ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩) :
    ∃ (β₀ : Fin n →₀ ℕ) (f₀ : B) (hf₀ : f₀ ∈ I) (l : Fin n) (hl : j ≤ (l : ℕ)) (hβl : β₀ l ≠ 0)
      (u : Bˣ) (hu : c'.d l (c'.Dv (β₀ - Finsupp.single l 1) f₀) = u)
      (hc'' : (nextChart c' ⟨j, by omega⟩ l (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu).IsCentred),
      IsUnit (c'.D β₀ f₀) ∧ coeff β₀ (c'.tau f₀) ≠ 0 ∧ lam (truncW e j) β₀ < 1 ∧
      0 < tailSum j β₀ ∧ e l = e ⟨j, by omega⟩ ∧ lam e β₀ = 1 ∧
      nextW (truncW e j) j β₀ = e ⟨j, by omega⟩ ∧
      (∀ m, Φ.F m = chartFil (nextChart c' ⟨j, by omega⟩ l
        (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu) e d m) ∧
      MC.SA I (j + 1) ⟨nextChart c' ⟨j, by omega⟩ l (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu,
        truncW e (j + 1), hc'', truncW_nonneg he _, truncW_antitone he hanti _⟩ := by
  have hjn : j < n := by omega
  obtain ⟨β₀, f₀, hf₀, l, hf₀ne, hlt₀, hN₀, hmin₀, hl, hβl, hel, hlam, hW⟩ :=
    DE_stepAp he hanti hd hsupp I hdecB lI hlI hId hmax hjk hkn c' hc' hF' hA
  have hej : 0 < e ⟨j, hjn⟩ := lt_of_le_of_ne (he _) (Ne.symm ((hsupp _).2 hjk))
  have hna : ¬ MC.Adm I ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩ := by
    intro hadm
    have h1 := hmax _ hadm
    have h2 := lex_le_at h1 hjn (fun i hi => by simp [truncW, hi])
    simp only [truncW, lt_irrefl, ite_false] at h2
    exact absurd h2 (not_le.2 hej)
  obtain ⟨hj', hunit, hbJ, u, hu, hc'', hnn'', ha'', hSA''⟩ :=
    hA.step_run_of_pos hdecB lI hlI β₀ f₀ hf₀ hf₀ne hlt₀ hN₀ hmin₀ l hl hβl
  have hwts : nextE (truncW e j) j (nextW (truncW e j) j β₀) = truncW e (j + 1) := by
    rw [hW]; exact nextE_truncW e hjn
  have hf1 : f₀ ∈ c'.RF e 1 := by rw [← chartFil_d c' hd, ← hF']; exact hId hf₀
  have hyRF : c'.Dv (β₀ - Finsupp.single l 1) f₀ ∈ c'.RF e (e l) := by
    have hlow := Chart.Dv_mem_RF_of_lowersBy c' c' e e (fun i => c'.lowersBy_self he i)
      (β₀ - Finsupp.single l 1) hf1
    have hlamsub : lam e (β₀ - Finsupp.single l 1) = lam e β₀ - e l := by
      have h := congrArg (lam e) (MC.add_single_sub hβl)
      rw [lam_add, lam_single] at h
      push_cast at h; linarith
    rw [hlamsub, hlam] at hlow
    simpa using hlow
  have hel' : 0 < e l := by rw [hel]; exact hej
  have hy := hc'.RF_le_maximalIdeal hel' hyRF
  refine ⟨β₀, f₀, hf₀, l, hl, hβl, u, hu, hc'', hunit, hf₀ne, hlt₀, hN₀, hel, hlam, hW,
    fcompat_nextChart he hc' hF' hel _ u hu hy hyRF, ?_⟩
  have hMC : (⟨nextChart c' ⟨j, hj'⟩ l (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu,
      nextE (truncW e j) j (nextW (truncW e j) j β₀), hc'', hnn'', ha''⟩ : MC B n) =
      ⟨nextChart c' ⟨j, hj'⟩ l (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu,
        truncW e (j + 1), hc'', truncW_nonneg he _, truncW_antitone he hanti _⟩ :=
    MC.ext' rfl hwts
  rw [hMC] at hSA''
  exact hSA''

end DEStepp

section DEStepRp
variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B]
  [Fact (Constructive.PolyIndNoeth B)] {n : ℕ}
  {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} {Φ : WFil B}
  (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i)
  (hpos : ∀ j : ℤ, 0 < j → Φ.F j ≤ maximalIdeal B)

set_option maxHeartbeats 1000000 in
theorem DE_stepRp (c₀ : Chart B n) (hF₀ : ∀ m, Φ.F m = chartFil c₀ e d m) {k : ℕ}
    (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k) (hkn : k ≤ n) (I : Ideal B)
    (hdecB : ∀ x : B, x ∈ maximalIdeal B ∨ IsUnit x) (lI : List B) (hlI : I = lspan lI) (hId : I ≤ Φ.F d)
    (hmax : ∀ J' : MC B n, J'.Adm I → toLex e ≤ toLex J'.e) {j : ℕ} (hjk : j < k)
    (c' : Chart B n) (hc' : c'.IsCentred) (hF' : ∀ m, Φ.F m = chartFil c' e d m)
    (hA : MC.SA I j ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩)
    (hR : MC.SA (weakV hpos I hId) j ⟨vChart he hd hw hpos c' hF', pad (n + 1) (truncW e j),
        vChart_isCentred he hd hw hpos c' hF' hc', pad_nonneg' _ (truncW_nonneg he j),
        pad_antitone' (truncW_nonneg he j) (truncW_antitone he hanti j)⟩) :
    ∃ (c'' : Chart B n) (hc'' : c''.IsCentred) (hF'' : ∀ m, Φ.F m = chartFil c'' e d m),
      MC.SA I (j + 1) ⟨c'', truncW e (j + 1), hc'', truncW_nonneg he _,
        truncW_antitone he hanti _⟩ ∧
      MC.SA (weakV hpos I hId) (j + 1) ⟨vChart he hd hw hpos c'' hF'',
          pad (n + 1) (truncW e (j + 1)), vChart_isCentred he hd hw hpos c'' hF'' hc'',
          pad_nonneg' _ (truncW_nonneg he _),
          pad_antitone' (truncW_nonneg he _) (truncW_antitone he hanti _)⟩ := by
  classical
  have := VLoc_polyIndNoeth_dec hpos c₀ hF₀ he hd hw
  have hjn : j < n := by omega
  obtain ⟨β₀, f₀, hf₀, l, hl, hβl, u, hu, hc'', hunit, hf₀ne, hlt₀, hN₀, hel, hlam, hW, hF'',
    hSA''⟩ := DE_stepAp' he hanti hd hsupp I hdecB lI hlI hId hmax hjk hkn c' hc' hF' hA
  refine ⟨_, hc'', hF'', hSA'', ?_⟩
  set Rc := vChart he hd hw hpos c' hF' with hRcdef
  have hRc : Rc.IsCentred := vChart_isCentred he hd hw hpos c' hF' hc'
  have hf₀d : LaurentPolynomial.C f₀ * T d ∈ ReesAlg Φ := C_mul_T_mem_ReesAlg (hId hf₀)
  set F₀ : VLoc hpos := algebraMap (ReesAlg Φ) (VLoc hpos) ⟨_, hf₀d⟩ with hF₀def
  have hF₀mem : F₀ ∈ weakV hpos I hId :=
    Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨⟨f₀, hf₀⟩, rfl⟩)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hlamw : lam e β₀ = (Finsupp.weight w β₀ : ℚ) / d := by
    rw [lam, Finsupp.weight_eq_sum, eq_div_iff hdq.ne']
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, Nat.cast_mul, hw i]; ring
  have hweight : (Finsupp.weight w β₀ : ℤ) = d := by
    rw [hlam, eq_comm, div_eq_one_iff_eq hdq.ne'] at hlamw
    exact_mod_cast hlamw
  have hDF : Rc.D (pushIdx (Nat.le_succ n) β₀) F₀ =
      algebraMap (ReesAlg Φ) (VLoc hpos) (algebraMap B (ReesAlg Φ) (c'.D β₀ f₀)) := by
    rw [hRcdef, vChart, hF₀def, Chart.localization_D]
    congr 1
    apply Subtype.ext
    rw [reesChart_D_hom, hweight, sub_self, T_zero, mul_one, Subalgebra.coe_algebraMap,
      ← LaurentPolynomial.C_eq_algebraMap]
  have hunitR : IsUnit (Rc.D (pushIdx (Nat.le_succ n) β₀) F₀) := by
    rw [hDF]; exact (hunit.map _).map _
  have hfneR : coeff (pushIdx (Nat.le_succ n) β₀) (Rc.tau F₀) ≠ 0 := by
    rw [Ne, Chart.coeff_tau_eq_zero_iff, Chart.Dv, Algebra.smul_def]
    intro hmem
    have hq : IsUnit (algebraMap ℚ (VLoc hpos)
        ((∏ i, ((pushIdx (Nat.le_succ n) β₀) i).factorial : ℕ) : ℚ)⁻¹) :=
      (isUnit_iff_ne_zero.2 (by positivity)).map _
    exact (IsLocalRing.notMem_maximalIdeal.2 hunitR) ((Ideal.unit_mul_mem_iff_mem _ hq).1 hmem)
  have hltR : lam (pad (n + 1) (truncW e j)) (pushIdx (Nat.le_succ n) β₀) < 1 := by
    rw [lam_pad]; exact hlt₀
  have hNR : 0 < tailSum j (pushIdx (Nat.le_succ n) β₀) := by rw [tailSum_push]; exact hN₀
  have hnaR : ¬ MC.Adm (weakV hpos I hId) ⟨Rc, pad (n + 1) (truncW e j), hRc,
      pad_nonneg' _ (truncW_nonneg he j),
      pad_antitone' (truncW_nonneg he j) (truncW_antitone he hanti j)⟩ := by
    intro hadm
    exact hfneR (hRc.coeff_tau_eq_zero_of_mem_RF (pad_nonneg' _ (truncW_nonneg he j))
      (hadm hF₀mem) _ hltR)
  have hJV : weakV hpos I hId ≤ Rc.RF (pad (n + 1) e) 1 := by
    rw [hRcdef, vChart, Chart.localization_RF]
    exact Ideal.map_mono (weak_le_reesRF he hd hw c' hF' I hId)
  have hjR : j < n + 1 := by omega
  have hej : 0 < e ⟨j, hjn⟩ := lt_of_le_of_ne (he _) (Ne.symm ((hsupp _).2 hjk))
  have hejR : pad (n + 1) e ⟨j, hjR⟩ = e ⟨j, hjn⟩ := by simp [pad, hjn]
  have hcompl := hR.compl_adm ⟨Rc, pad (n + 1) e, hRc, pad_nonneg' e he, pad_antitone' he hanti⟩
    hJV (fun i hi => by
      show pad (n + 1) e i = pad (n + 1) (truncW e j) i
      simp only [pad, truncW]
      split_ifs <;> rfl) hjR (by
      show 0 < pad (n + 1) e ⟨j, hjR⟩
      rw [hejR]; exact hej)
  have hW' : 1 - lam (truncW e j) β₀ = e ⟨j, hjn⟩ * tailSum j β₀ := by
    have hNq : (0 : ℚ) < tailSum j β₀ := by exact_mod_cast hN₀
    rw [nextW] at hW
    rw [← hW]; field_simp
  have hminR : ∀ β' : Fin (n + 1) →₀ ℕ, (∃ g ∈ weakV hpos I hId, coeff β' (Rc.tau g) ≠ 0) →
      lam (pad (n + 1) (truncW e j)) β' < 1 →
      Xi (pad (n + 1) (truncW e j)) j (pushIdx (Nat.le_succ n) β₀) ≤
        Xi (pad (n + 1) (truncW e j)) j β' := by
    rintro β' ⟨g, hg, hgne⟩ hβ'
    have h1 := hcompl hg
    have hcnn : ∀ i, 0 ≤ compl (pad (n + 1) (truncW e j)) j (pad (n + 1) e ⟨j, hjR⟩) i := by
      intro i; simp only [compl]; split_ifs
      · exact pad_nonneg' _ (truncW_nonneg he j) i
      · rw [hejR]; exact hej.le
    have h2 : 1 ≤ lam (compl (pad (n + 1) (truncW e j)) j (pad (n + 1) e ⟨j, hjR⟩)) β' := by
      by_contra h; push Not at h
      exact hgne (hRc.coeff_tau_eq_zero_of_mem_RF hcnn h1 β' h)
    rw [lam_compl (pad_zero_ge_truncW e), hejR] at h2
    simp only [Xi]
    rw [tailSum_push, lam_pad]
    have hNq : (0 : ℚ) < tailSum j β₀ := by exact_mod_cast hN₀
    have hp1 : 0 < 1 - lam (truncW e j) β₀ := by linarith
    have hp2 : 0 < 1 - lam (pad (n + 1) (truncW e j)) β' := by linarith
    rw [div_le_div_iff₀ hp1 hp2, hW']
    have : (1 - lam (pad (n + 1) (truncW e j)) β') ≤ e ⟨j, hjn⟩ * tailSum j β' := by linarith
    nlinarith
  obtain ⟨hjR', hunitR', hbJR, uR, huR, hcR, hnnR, haR, hSAR⟩ :=
    hR.step_run_of_pos (VLoc_dec hpos hdecB)
      (weakGens hpos lI fun f hf => hId (hlI ▸ Ideal.subset_span hf)) (weakV_eq_lspan hpos I hId lI hlI) (pushIdx (Nat.le_succ n) β₀) F₀ hF₀mem hfneR hltR hNR hminR
      (Fin.castSucc l) (by simpa using hl) (by rw [← castLE_succ_eq, pushIdx_apply]; exact hβl)
  have hwl : w l = w ⟨j, hjn⟩ := by
    have h1 := hw l; have h2 := hw ⟨j, hjn⟩; rw [hel] at h1; exact_mod_cast h1.trans h2.symm
  have hwswap : ∀ a, w (Equiv.swap ⟨j, hjn⟩ l a) = w a := by
    intro a
    rcases eq_or_ne a ⟨j, hjn⟩ with h | h
    · rw [h, Equiv.swap_apply_left, hwl]
    · rcases eq_or_ne a l with h' | h'
      · rw [h', Equiv.swap_apply_right, hwl]
      · rw [Equiv.swap_apply_of_ne_of_ne h h']
  have hgR : Rc.Dv (pushIdx (Nat.le_succ n) β₀ - Finsupp.single (Fin.castSucc l) 1) F₀ =
      algebraMap (ReesAlg Φ) (VLoc hpos) ((reesChart c' hF' he hd hw).Dv
        (pushIdx (Nat.le_succ n) (β₀ - Finsupp.single l 1)) ⟨_, hf₀d⟩) := by
    rw [← castLE_succ_eq, ← pushIdx_sub_single, hRcdef, vChart, hF₀def, Chart.localization_Dv]
  have hsplitw : Finsupp.weight w β₀ = Finsupp.weight w (β₀ - Finsupp.single l 1) + w l := by
    conv_lhs => rw [← MC.add_single_sub hβl]
    rw [map_add, Finsupp.weight_single, smul_eq_mul, one_mul]
  have hgcoe : (((reesChart c' hF' he hd hw).Dv (pushIdx (Nat.le_succ n) (β₀ - Finsupp.single l 1))
      ⟨_, hf₀d⟩ : ReesAlg Φ) : B[T;T⁻¹]) =
      LaurentPolynomial.C (c'.Dv (β₀ - Finsupp.single l 1) f₀) * T (w l) := by
    rw [reesChart_Dv_hom]
    congr 2
    have := hweight
    rw [hsplitw] at this
    push_cast at this
    omega
  have hjj : (⟨j, hjR'⟩ : Fin (n + 1)) = Fin.castSucc ⟨j, hjn⟩ := rfl
  set gR := Rc.Dv (pushIdx (Nat.le_succ n) β₀ - Finsupp.single (Fin.castSucc l) 1) F₀
    with hgRdef
  set c'' := nextChart c' ⟨j, hjn⟩ l (c'.Dv (β₀ - Finsupp.single l 1) f₀) u hu with hc''def
  have hc''x : ∀ a, c''.x a = if Equiv.swap ⟨j, hjn⟩ l a = l then
      c'.Dv (β₀ - Finsupp.single l 1) f₀ else c'.x (Equiv.swap ⟨j, hjn⟩ l a) :=
    fun a => nextChart_x_apply c' _ _ _ _ _ a
  have hgR' : gR = algebraMap (ReesAlg Φ) (VLoc hpos) (reesX c'' hF'' he hd hw
      (Fin.castSucc ⟨j, hjn⟩)) := by
    rw [hgR]
    congr 1
    apply Subtype.ext
    rw [hgcoe, reesX_castSucc, hc''x, ite_eq_left (Equiv.swap_apply_left _ _), hwl]
  have heqchart : nextChart Rc ⟨j, hjR'⟩ (Fin.castSucc l) gR uR huR =
      vChart he hd hw hpos c'' hF'' := by
    apply Chart.eq_of_x
    funext i
    rw [nextChart_x_apply, hjj]
    cases i using Fin.lastCases with
    | last =>
      rw [swap_castSucc_last, ite_eq_right (Fin.castSucc_lt_last l).ne']
      show algebraMap (ReesAlg Φ) (VLoc hpos) (reesX c' hF' he hd hw (Fin.last n)) =
        algebraMap (ReesAlg Φ) (VLoc hpos) (reesX c'' hF'' he hd hw (Fin.last n))
      congr 1
      apply Subtype.ext
      rw [reesX_last, reesX_last]
    | cast a =>
      rw [swap_castSucc_eq]
      by_cases hb : Equiv.swap ⟨j, hjn⟩ l a = l
      · rw [ite_eq_left (congrArg Fin.castSucc hb), hgR']
        have ha : a = ⟨j, hjn⟩ := by
          have := congrArg (Equiv.swap ⟨j, hjn⟩ l) hb
          rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
        subst ha
        rfl
      · rw [ite_eq_right (fun h => hb (Fin.castSucc_injective _ h))]
        show algebraMap (ReesAlg Φ) (VLoc hpos) (reesX c' hF' he hd hw _) =
          algebraMap (ReesAlg Φ) (VLoc hpos) (reesX c'' hF'' he hd hw (Fin.castSucc a))
        congr 1
        apply Subtype.ext
        rw [reesX_castSucc, reesX_castSucc, hc''x, ite_eq_right hb, hwswap]
  have hwtsR : nextE (pad (n + 1) (truncW e j)) j
      (nextW (pad (n + 1) (truncW e j)) j (pushIdx (Nat.le_succ n) β₀)) =
      pad (n + 1) (truncW e (j + 1)) := by
    have : nextW (pad (n + 1) (truncW e j)) j (pushIdx (Nat.le_succ n) β₀) =
        nextW (truncW e j) j β₀ := by simp only [nextW, lam_pad, tailSum_push]
    rw [this, hW, ← pad_nextE hjn, nextE_truncW e hjn]
  have hMC : (⟨_, _, hcR, hnnR, haR⟩ : MC (VLoc hpos) (n + 1)) =
      ⟨vChart he hd hw hpos _ hF'', pad (n + 1) (truncW e (j + 1)),
        vChart_isCentred he hd hw hpos _ hF'' hc'', pad_nonneg' _ (truncW_nonneg he _),
        pad_antitone' (truncW_nonneg he _) (truncW_antitone he hanti _)⟩ :=
    MC.ext' heqchart hwtsR
  rw [hMC] at hSAR
  exact hSAR

end DEStepRp

section DEMain2p
variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B]
  [Fact (Constructive.PolyIndNoeth B)] [IsDomain B]
  {n : ℕ} {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} {Φ : WFil B}
  (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i)
  (hpos : ∀ j : ℤ, 0 < j → Φ.F j ≤ maximalIdeal B)

/-- **The invariant at the vertex** (Brais, properties (D) and (E)): at the vertex point of the
weighted deformation, the weak transform has the same invariant as `I`, and its maximal centre is
the Rees centre of a compatible chart. -/
theorem vertex_invariant_pos (c₀ : Chart B n) (hc₀ : c₀.IsCentred)
    (hF₀ : ∀ m, Φ.F m = chartFil c₀ e d m) {k : ℕ} (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k)
    (hkn : k ≤ n) (I : Ideal B)
    (hdecB : ∀ x : B, x ∈ maximalIdeal B ∨ IsUnit x) (lI : List B) (hlI : I = lspan lI) (hI0 : I ≠ ⊥) (hId : I ≤ Φ.F d)
    (hmax : ∀ J' : MC B n, J'.Adm I → toLex e ≤ toLex J'.e) :
    ∃ (c' : Chart B n) (hc' : c'.IsCentred) (hF' : ∀ m, Φ.F m = chartFil c' e d m),
      MC.SA (weakV hpos I hId) k ⟨vChart he hd hw hpos c' hF', pad (n + 1) e,
        vChart_isCentred he hd hw hpos c' hF' hc', pad_nonneg' e he, pad_antitone' he hanti⟩ := by
  have := VLoc_polyIndNoeth_dec hpos c₀ hF₀ he hd hw
  have hIm : I ≤ maximalIdeal B := hId.trans (hpos d (by exact_mod_cast hd))
  have key : ∀ j, j ≤ k → ∃ (c' : Chart B n) (hc' : c'.IsCentred)
      (hF' : ∀ m, Φ.F m = chartFil c' e d m),
      MC.SA I j ⟨c', truncW e j, hc', truncW_nonneg he j, truncW_antitone he hanti j⟩ ∧
      MC.SA (weakV hpos I hId) j ⟨vChart he hd hw hpos c' hF', pad (n + 1) (truncW e j),
        vChart_isCentred he hd hw hpos c' hF' hc', pad_nonneg' _ (truncW_nonneg he j),
        pad_antitone' (truncW_nonneg he j) (truncW_antitone he hanti j)⟩ := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨c₀, hc₀, hF₀, ?_, ?_⟩
      · have h := MC.sa_zero_pos hdecB lI hlI hI0 hIm c₀ hc₀
        have hMC : (⟨c₀, 0, hc₀, fun _ => le_rfl, fun _ _ _ => le_rfl⟩ : MC B n) =
            ⟨c₀, truncW e 0, hc₀, truncW_nonneg he 0, truncW_antitone he hanti 0⟩ :=
          MC.ext' rfl (truncW_zero e).symm
        rwa [hMC] at h
      · have h := MC.sa_zero_pos (VLoc_dec hpos hdecB)
          (weakGens hpos lI fun f hf => hId (hlI ▸ Ideal.subset_span hf)) (weakV_eq_lspan hpos I hId lI hlI)
          (weakV_ne_bot hpos c₀ hF₀ he hw I hI0 hId)
          (weakV_le_max hpos I hId hd) (vChart he hd hw hpos c₀ hF₀)
          (vChart_isCentred he hd hw hpos c₀ hF₀ hc₀)
        have hMC : (⟨vChart he hd hw hpos c₀ hF₀, 0, vChart_isCentred he hd hw hpos c₀ hF₀ hc₀,
            fun _ => le_rfl, fun _ _ _ => le_rfl⟩ : MC (VLoc hpos) (n + 1)) =
            ⟨vChart he hd hw hpos c₀ hF₀, pad (n + 1) (truncW e 0),
              vChart_isCentred he hd hw hpos c₀ hF₀ hc₀, pad_nonneg' _ (truncW_nonneg he 0),
              pad_antitone' (truncW_nonneg he 0) (truncW_antitone he hanti 0)⟩ :=
          MC.ext' rfl (by
            show (0 : Fin (n + 1) → ℚ) = pad (n + 1) (truncW e 0)
            rw [truncW_zero, pad_zero'])
        rwa [hMC] at h
    | succ j ih =>
      intro hj
      obtain ⟨c', hc', hF', hA, hR⟩ := ih (by omega)
      exact DE_stepRp he hanti hd hw hpos c₀ hF₀ hsupp hkn I hdecB lI hlI hId hmax (by omega) c' hc' hF' hA hR
  obtain ⟨c', hc', hF', -, hR⟩ := key k le_rfl
  refine ⟨c', hc', hF', ?_⟩
  have hMC : (⟨vChart he hd hw hpos c' hF', pad (n + 1) (truncW e k),
      vChart_isCentred he hd hw hpos c' hF' hc', pad_nonneg' _ (truncW_nonneg he k),
      pad_antitone' (truncW_nonneg he k) (truncW_antitone he hanti k)⟩ : MC (VLoc hpos) (n + 1)) =
      ⟨vChart he hd hw hpos c' hF', pad (n + 1) e, vChart_isCentred he hd hw hpos c' hF' hc',
        pad_nonneg' e he, pad_antitone' he hanti⟩ :=
    MC.ext' rfl (by
      show pad (n + 1) (truncW e k) = pad (n + 1) e
      rw [truncW_of_supp hsupp])
  rwa [hMC] at hR

end DEMain2p

end BezoutCounterexample.Principalization
