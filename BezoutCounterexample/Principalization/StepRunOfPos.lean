import BezoutCounterexample.Principalization.Rees
import BezoutCounterexample.Principalization.StepRunPos

/-!
# `SA.step_run_of` at a decided residue field (leaf; (B) step B4)

`MC.SA.step_run_of` (Rees) is given a minimiser `βs` and calls `step_data_Q` (classical: `by_contra`,
`Nat.find`, (F2) through `QuotSeqCond`) only for a second minimiser with the bounds `hnext`, `hbJ`.
Here that minimiser comes from `SA.step_data_pos` (decided residue field, `I = (l₀)`), whose first
candidate is a generator `f' ∈ l₀` and `γ ≤ βs` with `coeff_γ(τ f') ≠ 0`
(`Chart.exists_gen_coeff_ne_zero`), `λ(γ) ≤ λ(βs) < 1`. No `¬ J.Adm I` is needed. The rest of the
proof is that of `step_run_of`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing Constructive

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] {n : ℕ}

namespace MC

variable {I : Ideal R} {j : ℕ} {J : MC R n}

theorem SA.step_run_of_pos (hdec : ∀ x : R, x ∈ maximalIdeal R ∨ IsUnit x) (l₀ : List R)
    (hl₀ : I = lspan l₀) (hSA : SA I j J) (βs : Fin n →₀ ℕ) (f : R) (hf : f ∈ I)
    (hfne : coeff βs (J.c.tau f) ≠ 0) (hlt : lam J.e βs < 1) (hN : 0 < tailSum j βs)
    (hmin : ∀ β : Fin n →₀ ℕ, (∃ g ∈ I, coeff β (J.c.tau g) ≠ 0) → lam J.e β < 1 →
      Xi J.e j βs ≤ Xi J.e j β) (l : Fin n) (hl : j ≤ (l : ℕ)) (hβl : βs l ≠ 0) :
    ∃ (hj : j < n) (_ : IsUnit (J.c.D βs f))
      (_ : ∀ i : Fin n, (i : ℕ) < j → nextW J.e j βs ≤ J.e i)
      (u : Rˣ) (hu : J.c.d l (J.c.Dv (βs - Finsupp.single l 1) f) = u)
      (hc : (nextChart J.c ⟨j, hj⟩ l (J.c.Dv (βs - Finsupp.single l 1) f) u hu).IsCentred)
      (hnn : ∀ i, 0 ≤ nextE J.e j (nextW J.e j βs) i)
      (ha : Antitone (nextE J.e j (nextW J.e j βs))),
      SA I (j + 1) ⟨nextChart J.c ⟨j, hj⟩ l (J.c.Dv (βs - Finsupp.single l 1) f) u hu,
        nextE J.e j (nextW J.e j βs), hc, hnn, ha⟩ := by
  have hγ := J.c.exists_gen_coeff_ne_zero hdec l₀ (hl₀ ▸ hf) βs hfne
  obtain ⟨f', hf', γ, hγβ, hγne⟩ := hγ
  have hltγ : lam J.e γ < 1 := lt_of_le_of_lt (lam_le_of_le J.nonneg hγβ) hlt
  obtain ⟨hj, β₀, f₀, hf₀, hf₀ne, hlt₀, hN₀, hmin₀, hnext₀, hbJ₀⟩ :=
    hSA.step_data_pos hdec l₀ hl₀ hf' hγne hltγ
  have hXi : Xi J.e j βs = Xi J.e j β₀ :=
    le_antisymm (hmin β₀ ⟨f₀, hf₀, hf₀ne⟩ hlt₀) (hmin₀ βs ⟨f, hf, hfne⟩ hlt)
  have hW : (1 - lam J.e βs) / tailSum j βs = (1 - lam J.e β₀) / tailSum j β₀ := by
    have h1 : (1 - lam J.e βs) / tailSum j βs = (Xi J.e j βs)⁻¹ := by rw [Xi, inv_div]
    have h2 : (1 - lam J.e β₀) / tailSum j β₀ = (Xi J.e j β₀)⁻¹ := by rw [Xi, inv_div]
    rw [h1, h2, hXi]
  have hnext : ∀ J' : MC R n, J'.Adm I → (∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i) →
      0 < J'.e ⟨j, hj⟩ ∧ (1 - lam J.e βs) / tailSum j βs ≤ J'.e ⟨j, hj⟩ := by
    intro J' hJ' hag; rw [hW]; exact hnext₀ J' hJ' hag
  have hbJ : ∀ i : Fin n, (i : ℕ) < j → (1 - lam J.e βs) / tailSum j βs ≤ J.e i := by
    intro i hi; rw [hW]; exact hbJ₀ i hi
  set jj : Fin n := ⟨j, hj⟩ with hjj
  set bp : ℚ := (1 - lam J.e βs) / tailSum j βs with hbpdef
  have hNq : (0 : ℚ) < tailSum j βs := by exact_mod_cast hN
  have hbp : 0 < bp := div_pos (by linarith) hNq
  have hzero : ∀ i : Fin n, j ≤ (i : ℕ) → J.e i = 0 := fun i hi => hSA.e_eq_zero hi
  have hkey : lam J.e βs + bp * tailSum j βs = 1 := by
    rw [hbpdef]; field_simp; ring
  have hS_bound : ∀ β : Fin n →₀ ℕ, (∃ g ∈ I, coeff β (J.c.tau g) ≠ 0) → lam J.e β < 1 →
      1 ≤ lam J.e β + bp * tailSum j β := by
    intro β hβ hβlt
    have hX := hmin β hβ hβlt
    simp only [Xi] at hX
    have h1 : 0 < 1 - lam J.e β := by linarith
    have h2 : 0 < 1 - lam J.e βs := by linarith
    rw [div_le_div_iff₀ h2 h1] at hX
    have : 1 - lam J.e β ≤ bp * tailSum j β := by
      rw [hbpdef, div_mul_eq_mul_div, le_div_iff₀ hNq]; linarith
    linarith
  -- the completion is an admissible marked centre
  have hc_nonneg : ∀ i, 0 ≤ compl J.e j bp i := fun i => by
    simp only [compl]; split_ifs
    · exact J.nonneg i
    · exact hbp.le
  have hc_ne : ∀ i, compl J.e j bp i ≠ 0 := fun i => by
    simp only [compl]; split_ifs with h
    · exact (hSA.e_pos h).ne'
    · exact hbp.ne'
  have hc_anti : Antitone (compl J.e j bp) := by
    intro i i' hii'
    simp only [compl]
    by_cases h1 : (i' : ℕ) < j
    · have h2 : (i : ℕ) < j := lt_of_le_of_lt (Fin.le_def.1 hii') h1
      rw [ite_eq_left h1, ite_eq_left h2]; exact J.anti hii'
    · rw [ite_eq_right h1]
      by_cases h2 : (i : ℕ) < j
      · rw [ite_eq_left h2]; exact hbJ i h2
      · rw [ite_eq_right h2]
  have hc_adm : I ≤ J.c.RF (compl J.e j bp) 1 := by
    intro g hg
    rw [J.centred.mem_RF_iff_of_ne hc_nonneg hc_ne]
    intro β hβ
    rcases J.c.coeff_tau_dec hdec β g with h0 | hne
    · exact h0
    exfalso
    rw [lam_compl hzero] at hβ
    rcases MC.lam_lt_dec J.e β with hβ1 | hβ1
    · have := hS_bound β ⟨g, hg, hne⟩ hβ1; linarith
    · have : 0 ≤ bp * tailSum j β := mul_nonneg hbp.le (Nat.cast_nonneg _)
      linarith
  -- the new parameter
  set γ := βs - Finsupp.single l 1 with hγdef
  have hγ : γ + Finsupp.single l 1 = βs := add_single_sub hβl
  have hlamγ : lam J.e γ = lam J.e βs := by
    rw [← hγ, lam_add, lam_single, hzero l hl, mul_zero, add_zero]
  have htailγ : tailSum j γ + 1 = tailSum j βs := tailSum_sub_single hl hβl
  set xb := J.c.Dv γ f with hxb
  have hdl : J.c.d l xb = ((γ l + 1 : ℕ) : ℚ) • J.c.Dv βs f := by rw [hxb, Chart.d_Dv, hγ]
  have hdl_nm : J.c.d l xb ∉ maximalIdeal R := by
    intro hmem
    rw [hdl, ← residue_eq_zero_iff, map_rat_smul] at hmem
    rw [← Chart.coeff_tau] at hmem
    exact hfne ((smul_eq_zero.1 hmem).resolve_left (by positivity))
  have hxb_mem : xb ∈ maximalIdeal R := by
    rw [hxb, ← residue_eq_zero_iff, ← Chart.coeff_tau]
    rcases J.c.coeff_tau_dec hdec γ f with h0 | hne
    · exact h0
    exfalso
    have hX := hmin γ ⟨f, hf, hne⟩ (by rw [hlamγ]; exact hlt)
    simp only [Xi, hlamγ] at hX
    have h2 : 0 < 1 - lam J.e βs := by linarith
    rw [div_le_div_iff_of_pos_right h2] at hX
    have : ((tailSum j γ : ℕ) : ℚ) + 1 = tailSum j βs := by exact_mod_cast htailγ
    linarith
  obtain ⟨u, hu⟩ := notMem_maximalIdeal.1 hdl_nm
  -- the new chart and weights
  set cp := (J.c.replace l xb u hu.symm).reindex (Equiv.swap jj l) with hcp
  have hcp_centred : cp.IsCentred := (J.centred.replace l xb u hu.symm hxb_mem).reindex _
  set ep : Fin n → ℚ := fun i => if (i : ℕ) < j then J.e i else if (i : ℕ) = j then bp else 0
    with hep
  have hep_nonneg : ∀ i, 0 ≤ ep i := fun i => by
    simp only [hep]; split_ifs
    · exact J.nonneg i
    · exact hbp.le
    · exact le_rfl
  have hep_anti : Antitone ep := by
    intro i i' hii'
    have hle := Fin.le_def.1 hii'
    simp only [hep]
    by_cases h1 : (i' : ℕ) < j
    · rw [ite_eq_left h1, ite_eq_left (lt_of_le_of_lt hle h1)]; exact J.anti hii'
    · rw [ite_eq_right h1]
      by_cases h2 : (i' : ℕ) = j
      · rw [ite_eq_left h2]
        by_cases h3 : (i : ℕ) < j
        · rw [ite_eq_left h3]; exact hbJ i h3
        · rw [ite_eq_right h3, ite_eq_left (by omega)]
      · rw [ite_eq_right h2]
        split_ifs
        · exact J.nonneg i
        · exact hbp.le
        · exact le_rfl
  have hcp_x_lt : ∀ i : Fin n, (i : ℕ) < j → cp.x i = J.c.x i := by
    intro i hi
    have h1 : i ≠ jj := fun h => by rw [h] at hi; simp [hjj] at hi
    have h2 : i ≠ l := fun h => by rw [h] at hi; omega
    rw [hcp, Chart.reindex_x, Equiv.swap_apply_of_ne_of_ne h1 h2, J.c.replace_x_ne _ _ _ _ h2]
  have hcp_x_j : cp.x jj = xb := by
    rw [hcp, Chart.reindex_x, Equiv.swap_apply_left, J.c.replace_x_self]
  have hunitD : IsUnit (J.c.D βs f) := by
    rw [← notMem_maximalIdeal]
    intro hmem
    apply hfne
    rw [Chart.coeff_tau, residue_eq_zero_iff, Chart.Dv, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hmem
  refine ⟨hj, hunitD, hbJ, u, hu.symm, hcp_centred, hep_nonneg,
    hep_anti, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- support
    intro i
    show ep i ≠ 0 ↔ (i : ℕ) < j + 1
    simp only [hep]
    by_cases h1 : (i : ℕ) < j
    · rw [ite_eq_left h1]; exact ⟨fun _ => by omega, fun _ => (hSA.supp i).2 h1⟩
    · rw [ite_eq_right h1]
      by_cases h2 : (i : ℕ) = j
      · rw [ite_eq_left h2]; exact ⟨fun _ => by omega, fun _ => hbp.ne'⟩
      · rw [ite_eq_right h2]; exact ⟨fun h => absurd rfl h, fun h => by omega⟩
  · -- domination by an admissible centre: the completion
    refine ⟨⟨J.c, compl J.e j bp, J.centred, hc_nonneg, hc_anti⟩, hc_adm, fun i hi => ?_⟩
    show compl J.e j bp i = ep i
    simp only [compl, hep]
    by_cases h1 : (i : ℕ) < j
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left (by omega)]
  · -- maximality
    intro J' hJ' i hi hbelow
    by_cases h1 : (i : ℕ) < j
    · have : ep i = J.e i := by simp only [hep, ite_eq_left h1]
      show ep i ≤ J'.e i
      rw [this]
      refine hSA.max J' hJ' i h1 fun i' hi' => ?_
      rw [hbelow i' hi']
      show ep i' = J.e i'
      simp only [hep, ite_eq_left (lt_trans (Fin.lt_def.1 hi') h1)]
    · have hij : (i : ℕ) = j := by omega
      have hieq : i = jj := Fin.ext hij
      subst hieq
      have hag : ∀ i' : Fin n, (i' : ℕ) < j → J'.e i' = J.e i' := fun i' hi' => by
        rw [hbelow i' (Fin.lt_def.2 hi')]
        show ep i' = J.e i'
        simp only [hep, ite_eq_left hi']
      have := (hnext J' hJ' hag).2
      show ep jj ≤ J'.e jj
      simp only [hep, ite_eq_right h1, ite_eq_left hij]
      exact this
  · -- domination
    intro J' hJ' hag
    have hag_j : ∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i := fun i hi => by
      rw [hag i (by omega)]; show ep i = J.e i; simp only [hep, ite_eq_left hi]
    have hJ'j : J'.e jj = bp := by
      rw [hag jj (by simp [hjj])]; show ep jj = bp; simp [hep, hjj]
    obtain ⟨c'', hc'', hRF, hx⟩ := hSA.dom J' hJ' hag_j
    have hf' : f ∈ c''.RF J'.e 1 := by rw [hRF]; exact hJ' hf
    -- lowering bounds for the derivations of `J.c` with respect to `(c'', J'.e)`
    have hlow : ∀ i, c''.LowersBy J'.e (J.c.d i) (compl J.e j bp i) := by
      intro i
      by_cases hi : (i : ℕ) < j
      · have := hc''.lowersBy_lt (c := J.c) J'.nonneg J'.anti (fun i' hi' => (hx i' hi').symm) i hi
        simp only [compl, ite_eq_left hi]
        rwa [hag_j i hi] at this
      · simp only [compl, ite_eq_right hi]
        refine hc''.lowersBy_ge (c := J.c) J'.nonneg (fun i' hi' => (hx i' hi').symm) i (by omega)
          fun m hm => ?_
        rw [← hJ'j]; exact J'.anti (Fin.le_def.2 (by simp only [hjj, Fin.val_mk]; omega))
    have hxb_RF : xb ∈ c''.RF J'.e bp := by
      have hm1 := Chart.Dv_mem_RF_of_lowersBy c'' J.c J'.e (compl J.e j bp) hlow γ hf'
      rw [lam_compl hzero, hlamγ] at hm1
      have htq : ((tailSum j γ : ℕ) : ℚ) + 1 = tailSum j βs := by exact_mod_cast htailγ
      have hm2 : 1 - (lam J.e βs + bp * (tailSum j γ : ℚ)) = bp := by
        have := hkey; rw [← htq] at this; linarith
      rw [hm2] at hm1
      exact hm1
    -- a coordinate of `c''` in which `xb` has a linear term
    obtain ⟨m, hm, hmnm⟩ : ∃ m : Fin n, j ≤ (m : ℕ) ∧ c''.d m xb ∉ maximalIdeal R := by
      have hPdec : ∀ m : Fin n, (j ≤ (m : ℕ) ∧ c''.d m xb ∉ maximalIdeal R) ∨
          ¬ (j ≤ (m : ℕ) ∧ c''.d m xb ∉ maximalIdeal R) := fun m => by
        rcases hdec (c''.d m xb) with h | h
        · exact Or.inr fun hP => hP.2 h
        · by_cases hm : j ≤ (m : ℕ)
          · exact Or.inl ⟨hm, fun h' => (mem_maximalIdeal _).1 h' h⟩
          · exact Or.inr fun hP => hm hP.1
      rcases list_exists_or_forall hPdec (List.finRange n) with ⟨m, -, hm⟩ | hall
      · exact ⟨m, hm⟩
      exfalso
      have hcon : ∀ m : Fin n, j ≤ (m : ℕ) → c''.d m xb ∈ maximalIdeal R := fun m hm =>
        (hdec (c''.d m xb)).elim id fun hu =>
          absurd ⟨hm, fun h => (mem_maximalIdeal _).1 h hu⟩ (hall m (List.mem_finRange m))
      apply hdl_nm
      rw [c''.eq_sum (J.c.d l), Derivation.sum_apply']
      refine Ideal.sum_mem _ fun m _ => ?_
      rw [Derivation.smul_apply, smul_eq_mul]
      by_cases hmj : (m : ℕ) < j
      · rw [hx m hmj, J.c.d_x, ite_eq_right (fun h => by rw [h] at hl; omega), zero_mul]
        exact zero_mem _
      · exact Ideal.mul_mem_left _ _ (hcon m (by omega))
    have hJ'm : J'.e m = bp := by
      refine le_antisymm ?_ ?_
      · rw [← hJ'j]; exact J'.anti (Fin.le_def.2 (by simp only [hjj, Fin.val_mk]; omega))
      · refine le_of_not_gt fun hlt' => ?_
        have := hc''.coeff_tau_eq_zero_of_mem_RF J'.nonneg hxb_RF (Finsupp.single m 1) (by
          rw [lam_single]; simpa using hlt')
        rw [Chart.coeff_tau_eq_zero_iff, Chart.Dv_single_one] at this
        exact hmnm this
    obtain ⟨u', hu'⟩ := notMem_maximalIdeal.1 hmnm
    refine ⟨(c''.replace m xb u' hu'.symm).reindex (Equiv.swap jj m),
      (hc''.replace m xb u' hu'.symm hxb_mem).reindex _, fun t => ?_, fun i hi => ?_⟩
    · rw [Chart.RF_reindex _ _ (fun i => by
          rcases eq_or_ne i jj with h | h
          · rw [h, Equiv.swap_apply_left, hJ'm, hJ'j]
          · rcases eq_or_ne i m with h' | h'
            · rw [h', Equiv.swap_apply_right, hJ'm, hJ'j]
            · rw [Equiv.swap_apply_of_ne_of_ne h h'])]
      rw [hc''.RF_replace J'.nonneg m xb u' hu'.symm hxb_mem (by rw [hJ'm]; exact hxb_RF), hRF]
    · show ((c''.replace m xb u' hu'.symm).reindex (Equiv.swap jj m)).x i = cp.x i
      by_cases hij : (i : ℕ) < j
      · have h1 : i ≠ jj := fun h => by rw [h] at hij; simp [hjj] at hij
        have h2 : i ≠ m := fun h => by rw [h] at hij; omega
        rw [Chart.reindex_x, Equiv.swap_apply_of_ne_of_ne h1 h2, c''.replace_x_ne _ _ _ _ h2,
          hx i hij, hcp_x_lt i hij]
      · have hieq : i = jj := Fin.ext (by simp [hjj]; omega)
        subst hieq
        rw [Chart.reindex_x, Equiv.swap_apply_left, c''.replace_x_self, hcp_x_j]



end MC

end BezoutCounterexample.Principalization
