import BezoutCounterexample.Principalization.Transfer
import BezoutCounterexample.Constructive.CompList

/-!
# The transfer theorem with a decided target (D3.4 (c), leaf)

`TI.step` (Transfer) finds a coordinate `m` of the target chart with `∂_m x̄ ∉ 𝔪'` by `by_contra`
(a search over `Fin n'`), and compares weights by `by_contra`. Here the target local ring `R'`
has a decided residue field (`hdec`; at a point `p`: `Pt.dec_local` on `A_{p.ker}`), so the
search is a decision; the comparisons use the order of `ℚ` and `ℕ`. Twins: `TI.step_pos`,
`IsRun.transfer_pos`, `IsRun.transfer_bound_pos` (same conclusions). In `local_structure` the
target is `A_{𝔪'}` for every `𝔪' ∌ g`; at explicit points `𝔪' = p.ker` this is all that
`LocDataPt` needs.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing Constructive

variable {S : Type*} [CommRing S] [Algebra ℚ S] {R' : Type*} [CommRing R'] [Algebra ℚ R']
  [IsLocalRing R'] {n n' : ℕ} {hnn : n ≤ n'}

/-- **Transfer step.** -/
theorem TI.step_pos (hdec : ∀ x : R', x ∈ maximalIdeal R' ∨ IsUnit x) {ψ : S →+* R'} {I : Ideal S} {j : ℕ} {c : Chart S n} {e : Fin n → ℚ}
    {c' : Chart R' n'} (hT : TI hnn ψ I j c e c') (hj : j < n)
    (hsupp : ∀ i : Fin n, j ≤ (i : ℕ) → e i = 0)
    (f : S) (hf : f ∈ I) (β : Fin n →₀ ℕ) (l : Fin n) (hl : j ≤ (l : ℕ)) (hβl : β l ≠ 0)
    (hlam : lam e β < 1) (hN : 0 < tailSum j β) (hunit : IsUnit (c.D β f))
    (u : Sˣ) (hu : c.d l (c.Dv (β - Finsupp.single l 1) f) = u) :
    TI hnn ψ I (j + 1) (nextChart c ⟨j, hj⟩ l (c.Dv (β - Finsupp.single l 1) f) u hu)
      (nextE e j (nextW e j β))
      (nextChart c' (Fin.castLE hnn ⟨j, hj⟩) (Fin.castLE hnn l)
        (ψ (c.Dv (β - Finsupp.single l 1) f)) (Units.map ψ.toMonoidHom u) (hT.compat.hu' hu)) := by
  set jj : Fin n := ⟨j, hj⟩ with hjj
  set jj' : Fin n' := Fin.castLE hnn jj with hjj'
  have hjj'v : (jj' : ℕ) = j := by simp [hjj', hjj]
  set b := nextW e j β with hbdef
  have hNq : (0 : ℚ) < tailSum j β := by exact_mod_cast hN
  have hbpos : 0 < b := div_pos (by linarith) hNq
  have hkey : lam e β + b * tailSum j β = 1 := by rw [hbdef, nextW]; field_simp; ring
  set γ := β - Finsupp.single l 1 with hγdef
  have hγ : γ + Finsupp.single l 1 = β := MC.add_single_sub hβl
  have hlamγ : lam e γ = lam e β := by
    rw [← hγ, lam_add, lam_single, hsupp l hl, mul_zero, add_zero]
  have htailγ : tailSum j γ + 1 = tailSum j β := MC.tailSum_sub_single hl hβl
  have hψf : ∀ J' : MC R' n', J'.Adm (I.map ψ) → ψ f ∈ J'.RF 1 :=
    fun J' hJ' => hJ' (Ideal.mem_map_of_mem ψ hf)
  refine ⟨hT.compat.nextChart jj l _ u hu, ?_, ?_⟩
  · -- maximality
    intro J' hJ' i hi hbelow
    by_cases h1 : (i : ℕ) < j
    · rw [pad_nextE_lt i h1]
      exact hT.max J' hJ' i h1 fun i' hi' => by
        rw [hbelow i' hi', pad_nextE_lt i' (lt_trans (Fin.lt_def.1 hi') h1)]
    · have hij : (i : ℕ) = j := by omega
      rw [pad_nextE_eq hj i hij]
      have hag : ∀ i' : Fin n', (i' : ℕ) < j → J'.e i' = pad n' e i' := fun i' hi' => by
        rw [hbelow i' (Fin.lt_def.2 (by omega)), pad_nextE_lt i' hi']
      obtain ⟨c'', hc'', hRF, hx⟩ := hT.dom J' hJ' hag
      refine le_of_not_gt fun hlt => ?_
      have hlow := lowers_compl (c' := c') hc'' hx hag (b := J'.e i) fun m hm =>
        J'.anti (Fin.le_def.2 (by omega))
      have hmem := Chart.D_mem_RF_of_lowersBy c'' c' J'.e _ hlow (pushIdx hnn β) 1 (ψ f)
        (by rw [hRF]; exact hψf J' hJ')
      rw [hT.compat.D, lam_compl_pad hsupp] at hmem
      have hpos : 0 < 1 - (lam e β + J'.e i * tailSum j β) := by
        have : J'.e i * tailSum j β < b * tailSum j β := mul_lt_mul_of_pos_right hlt hNq
        linarith
      have := hc''.RF_le_maximalIdeal hpos hmem
      exact (notMem_maximalIdeal.2 (hunit.map ψ)) this
  · -- domination
    intro J' hJ' hag
    have hag_j : ∀ i : Fin n', (i : ℕ) < j → J'.e i = pad n' e i := fun i hi => by
      rw [hag i (by omega), pad_nextE_lt i hi]
    have hJ'j : J'.e jj' = b := by rw [hag jj' (by omega), pad_nextE_eq hj jj' hjj'v]
    obtain ⟨c'', hc'', hRF, hx⟩ := hT.dom J' hJ' hag_j
    have hlow := lowers_compl (c' := c') hc'' hx hag_j (b := b) fun m hm => by
      rw [← hJ'j]; exact J'.anti (Fin.le_def.2 (by omega))
    set xb' := ψ (c.Dv γ f) with hxb'
    have hxb_RF : xb' ∈ c''.RF J'.e b := by
      have hm1 := Chart.Dv_mem_RF_of_lowersBy c'' c' J'.e _ hlow (pushIdx hnn γ)
        (by rw [hRF]; exact hψf J' hJ' : ψ f ∈ c''.RF J'.e 1)
      rw [hT.compat.Dv, lam_compl_pad hsupp, hlamγ] at hm1
      have htq : ((tailSum j γ : ℕ) : ℚ) + 1 = tailSum j β := by exact_mod_cast htailγ
      have hm2 : 1 - (lam e β + b * (tailSum j γ : ℚ)) = b := by
        have := hkey; rw [← htq] at this; linarith
      rw [hm2] at hm1
      exact hm1
    have hxb_mem : xb' ∈ maximalIdeal R' := hc''.RF_le_maximalIdeal hbpos hxb_RF
    have hdl : c'.d (Fin.castLE hnn l) xb' = ψ u := by rw [hxb', hT.compat.d, hu]
    have hdl_nm : c'.d (Fin.castLE hnn l) xb' ∉ maximalIdeal R' := by
      rw [hdl]; exact notMem_maximalIdeal.2 ((Units.isUnit u).map ψ)
    obtain ⟨m, hm, hmnm⟩ : ∃ m : Fin n', j ≤ (m : ℕ) ∧ c''.d m xb' ∉ maximalIdeal R' := by
      have hPdec : ∀ m : Fin n', (j ≤ (m : ℕ) ∧ c''.d m xb' ∉ maximalIdeal R') ∨
          ¬ (j ≤ (m : ℕ) ∧ c''.d m xb' ∉ maximalIdeal R') := fun m => by
        rcases hdec (c''.d m xb') with h | h
        · exact Or.inr fun hP => hP.2 h
        · by_cases hm : j ≤ (m : ℕ)
          · exact Or.inl ⟨hm, fun h' => (mem_maximalIdeal _).1 h' h⟩
          · exact Or.inr fun hP => hm hP.1
      rcases list_exists_or_forall hPdec (List.finRange n') with ⟨m, -, hm⟩ | hall
      · exact ⟨m, hm⟩
      exfalso
      have hcon : ∀ m : Fin n', j ≤ (m : ℕ) → c''.d m xb' ∈ maximalIdeal R' := fun m hm =>
        (hdec (c''.d m xb')).elim id fun hu =>
          absurd ⟨hm, fun h => (mem_maximalIdeal _).1 h hu⟩ (hall m (List.mem_finRange m))
      apply hdl_nm
      rw [c''.eq_sum (c'.d (Fin.castLE hnn l)), Derivation.sum_apply']
      refine Ideal.sum_mem _ fun m _ => ?_
      rw [Derivation.smul_apply, smul_eq_mul]
      by_cases hmj : (m : ℕ) < j
      · rw [hx m hmj, c'.d_x, ite_eq_right (fun h => by rw [← h] at hmj; simp at hmj; omega), zero_mul]
        exact zero_mem _
      · exact Ideal.mul_mem_left _ _ (hcon m (by omega))
    have hJ'm : J'.e m = b := by
      refine le_antisymm ?_ ?_
      · rw [← hJ'j]; exact J'.anti (Fin.le_def.2 (by omega))
      · refine le_of_not_gt fun hlt' => ?_
        have := hc''.coeff_tau_eq_zero_of_mem_RF J'.nonneg hxb_RF (Finsupp.single m 1) (by
          rw [lam_single]; simpa using hlt')
        rw [Chart.coeff_tau_eq_zero_iff, Chart.Dv_single_one] at this
        exact hmnm this
    obtain ⟨u', hu'⟩ := notMem_maximalIdeal.1 hmnm
    refine ⟨(c''.replace m xb' u' hu'.symm).reindex (Equiv.swap jj' m),
      (hc''.replace m xb' u' hu'.symm hxb_mem).reindex _, fun t => ?_, fun i hi => ?_⟩
    · rw [Chart.RF_reindex _ _ (fun i => by
          rcases eq_or_ne i jj' with h | h
          · rw [h, Equiv.swap_apply_left, hJ'm, hJ'j]
          · rcases eq_or_ne i m with h' | h'
            · rw [h', Equiv.swap_apply_right, hJ'm, hJ'j]
            · rw [Equiv.swap_apply_of_ne_of_ne h h'])]
      rw [hc''.RF_replace J'.nonneg m xb' u' hu'.symm hxb_mem (by rw [hJ'm]; exact hxb_RF), hRF]
    · show ((c''.replace m xb' u' hu'.symm).reindex (Equiv.swap jj' m)).x i =
        (nextChart c' jj' (Fin.castLE hnn l) xb' (Units.map ψ.toMonoidHom u) _).x i
      simp only [Principalization.nextChart, Chart.reindex_x]
      by_cases hij : (i : ℕ) < j
      · have h1 : i ≠ jj' := fun h => by rw [h] at hij; omega
        have h2 : i ≠ m := fun h => by rw [h] at hij; omega
        have h3 : i ≠ Fin.castLE hnn l := fun h => by rw [h] at hij; simp at hij; omega
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h3,
          c''.replace_x_ne _ _ _ _ h2, c'.replace_x_ne _ _ _ _ h3, hx i hij]
      · have hieq : i = jj' := Fin.ext (by omega)
        subst hieq
        rw [Equiv.swap_apply_left, Equiv.swap_apply_left, c''.replace_x_self, c'.replace_x_self]

/-- **Transfer theorem** (inductive form). -/
theorem IsRun.transfer_pos (hdec : ∀ x : R', x ∈ maximalIdeal R' ∨ IsUnit x) {ψ : S →+* R'} {I : Ideal S} {j : ℕ} {c : Chart S n} {e : Fin n → ℚ}
    {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ} (h : IsRun I j c e k ck ek)
    (hsupp : ∀ i : Fin n, j ≤ (i : ℕ) → e i = 0) :
    ∀ c' : Chart R' n', TI hnn ψ I j c e c' → ∃ ck' : Chart R' n', TI hnn ψ I k ck ek ck' := by
  induction h with
  | refl => exact fun c' hT => ⟨c', hT⟩
  | step hj f hf β l hl hβl hlam hN hunit hb u hu hnext ih =>
    intro c' hT
    exact ih (fun i hi => nextE_zero_ge _ i hi) _
      (hT.step_pos hdec hj hsupp f hf β l hl hβl hlam hN hunit u hu)

/-- **Transfer theorem.** A Method-1 run for `I` on `S`, transported along `ψ : S → R'` with a
compatible chart, bounds the admissible marked centres of `I R'` from below (lexicographically in
the weights, i.e. from above in the invariant), and identifies those with equal weights. -/
theorem IsRun.transfer_bound_pos (hdec : ∀ x : R', x ∈ maximalIdeal R' ∨ IsUnit x) {ψ : S →+* R'} {I : Ideal S} {c : Chart S n} {k : ℕ}
    {ck : Chart S n} {ek : Fin n → ℚ} (h : IsRun I 0 c 0 k ck ek) {c' : Chart R' n'}
    (hc : Compat hnn ψ c c') :
    ∃ ck' : Chart R' n', Compat hnn ψ ck ck' ∧ ∀ J' : MC R' n', J'.Adm (I.map ψ) →
      toLex (pad n' ek) ≤ toLex J'.e ∧
      (J'.e = pad n' ek → ∀ t, J'.RF t = ck'.RF (pad n' ek) t) := by
  obtain ⟨ck', hT⟩ := h.transfer_pos hdec (fun _ _ => rfl) c' (TI.zero hc)
  have hsk := h.supp (fun _ _ => rfl)
  refine ⟨ck', hT.compat, fun J' hJ' => ⟨?_, fun he t => ?_⟩⟩
  · rw [← not_lt]
    rintro ⟨i, hbelow, hlt⟩
    simp only [Pi.toLex_apply] at hbelow hlt
    rcases Nat.lt_or_ge (i : ℕ) k with hik | hik
    · exact absurd (hT.max J' hJ' i hik fun i' hi' => hbelow i' hi') (not_le.2 hlt)
    · rw [pad_zero_ge hsk i (by omega)] at hlt
      exact absurd (J'.nonneg i) (not_le.2 hlt)
  · obtain ⟨c'', -, hRF, hx⟩ := hT.dom J' hJ' (fun i _ => by rw [he])
    rw [← hRF, he]
    refine Chart.RF_congr (fun i hi => hx i ?_) t
    rcases Nat.lt_or_ge (i : ℕ) k with hik | hik
    · exact hik
    · exact absurd (pad_zero_ge hsk i hik) hi

end BezoutCounterexample.Principalization
