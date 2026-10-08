import BezoutCounterexample.Principalization.Stable
import BezoutCounterexample.Principalization.TransferPos

/-!
# Derivations and the canonical centre, with a decided residue field (leaf, part (a))

`deriv_mem_RF` (Stable) compares the flowed centre with the run in `S' = S[t]_{(𝔪,t)}` through the
classical `IsRun.transfer_bound` (`TI.step`, a `by_contra` search). When the residue field of `S` is
decided (`hdec`; at an explicit point `Pt.dec_local`), so is that of `S'` (`polyLoc_dec`: the class
of `p/s` is decided by the constant coefficient of `p`), and the transfer bound comes from
`IsRun.transfer_bound_pos`:

* `polyLoc_dec`: the decision on `PolyLoc S`;
* `deriv_mem_RF_pos`: twin of `deriv_mem_RF`;
* `length_le_of_derivations_pos`: twin of `length_le_of_derivations` (Lemma 3.7(2)).

Same statements plus `hdec`; no `classical`. Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing TrivSqZeroExt Polynomial Finset

section K

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {n : ℕ}

omit [Algebra ℚ S] in
/-- **The residue field of `S[t]_{(𝔪,t)}` is decided** when that of `S` is. -/
theorem polyLoc_dec (hdec : ∀ x : S, x ∈ maximalIdeal S ∨ IsUnit x) :
    ∀ x : PolyLoc S, x ∈ maximalIdeal (PolyLoc S) ∨ IsUnit x := by
  intro x
  obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective (polyMax S).primeCompl x
  rcases hdec (p.coeff 0) with h | h
  · left
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff (PolyLoc S) (polyMax S) p s).2
      ((mem_polyMax p).2 h)
  · right
    refine (IsLocalization.AtPrime.isUnit_mk'_iff (PolyLoc S) (polyMax S) p s).2 ?_
    intro hp
    exact (IsLocalRing.notMem_maximalIdeal.2 h) ((mem_polyMax p).1 hp)

theorem deriv_mem_RF_pos (hdec : ∀ x : S, x ∈ maximalIdeal S ∨ IsUnit x) {I : Ideal S}
    {c : Chart S n} {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ}
    (hrun : IsRun I 0 c 0 k ck ek) (hadm : I ≤ ck.RF ek 1) (hck : ck.IsCentred)
    (hnn : ∀ i, 0 ≤ ek i) (hanti : Antitone ek) (hsupp : ∀ i, ek i ≠ 0 ↔ (i : ℕ) < k)
    (δ : Derivation ℚ S S) (hδ : ∀ f ∈ I, δ f ∈ I) (i : Fin n) (hi : (i : ℕ) < k) :
    δ (ck.x i) ∈ ck.RF ek (ek i) := by
  obtain ⟨d, w, hd, hw⟩ := Chart.exists_scale hnn
  set N := d + 1 with hNdef
  have hN : 0 < N := by omega
  have hN2 : 2 ≤ N := by omega
  have hkn : k ≤ n := hrun.stage_le (Nat.zero_le _)
  have hk1 : k < n + 1 := by omega
  have hz : ∀ a : Fin n, k ≤ (a : ℕ) → ek a = 0 := fun a ha => by
    by_contra h; exact absurd ((hsupp a).1 h) (by omega)
  have hpos : ∀ a : Fin n, (a : ℕ) < k → (1 : ℚ) / d ≤ ek a := by
    intro a ha
    have h1 : ek a ≠ 0 := (hsupp a).2 ha
    have h2 : (w a : ℚ) = d * ek a := hw a
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    have hw1 : 1 ≤ w a := by
      by_contra h; push Not at h
      have : w a = 0 := by omega
      rw [this, Nat.cast_zero] at h2
      exact h1 ((mul_eq_zero.1 h2.symm).resolve_left hdq.ne')
    rw [div_le_iff₀ hdq, mul_comm, ← h2]; exact_mod_cast hw1
  -- the ring `S' = S[t]_{(𝔪,t)}`
  set t : PolyLoc S := polyT with htdef
  set ψ : S →+* PolyLoc S := toPolyLoc with hψdef
  -- Step 1: push the run forward
  obtain ⟨ck', hrun', hcompat, hext⟩ :=
    hrun.map (hnn := Nat.le_succ n) c.polyLoc c.compat_polyLoc
  have hck' : ck' = ck.polyLoc := by
    refine Chart.eq_of_x (funext fun j => ?_)
    cases j using Fin.lastCases with
    | last => rw [hext _ (by simp), c.polyLoc_x_last, ck.polyLoc_x_last]
    | cast a => rw [← castLE_succ_eq, hcompat.x a, ← ck.compat_polyLoc.x a]
  rw [hck', pad_zero'] at hrun'
  -- Step 2: one more step with `tᴺ`
  set C := ck.polyLoc with hCdef
  set It : Ideal (PolyLoc S) := I.map ψ ⊔ Ideal.span {t ^ N} with hItdef
  have htN : t ^ N ∈ It := Ideal.mem_sup_right (Ideal.subset_span rfl)
  have hCx : C.x (Fin.last n) = t := ck.polyLoc_x_last
  have hCd : C.d (Fin.last n) t = 1 := by rw [← hCx, C.d_x]; simp
  have hcastN : ∀ m : ℕ, (m : PolyLoc S) = algebraMap ℚ (PolyLoc S) m := fun m => by simp
  have hfunit : IsUnit ((N.factorial : ℕ) : PolyLoc S) := by
    rw [hcastN]; exact (isUnit_iff_ne_zero.2 (by exact_mod_cast (Nat.factorial_pos N).ne')).map _
  set β : Fin (n + 1) →₀ ℕ := Finsupp.single (Fin.last n) N with hβdef
  have hβsub : β - Finsupp.single (Fin.last n) 1 = Finsupp.single (Fin.last n) (N - 1) := by
    rw [hβdef]; ext j
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
    split_ifs <;> simp
  have hDv : C.Dv (β - Finsupp.single (Fin.last n) 1) (t ^ N) = (N : PolyLoc S) * t := by
    rw [hβsub, Chart.Dv, Chart.D_single, iterate_pow_of_eq_one _ hCd]
    have hfact : (∏ j, ((Finsupp.single (Fin.last n) (N - 1)) j).factorial) = (N - 1).factorial := by
      rw [Finset.prod_eq_single (Fin.last n)]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [hfact, show N - (N - 1) = 1 by omega, pow_one, ← smul_mul_assoc]
    congr 1
    have hdesc : N.descFactorial (N - 1) = N * (N - 1).factorial := by
      have h := Nat.factorial_mul_descFactorial (show N - 1 ≤ N by omega)
      rw [show N - (N - 1) = 1 by omega, Nat.factorial_one, one_mul] at h
      rw [h, Nat.mul_factorial_pred (by omega : N ≠ 0)]
    rw [hdesc, Algebra.smul_def, hcastN, hcastN N, ← map_mul]
    congr 1
    have : ((N - 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  set u : (PolyLoc S)ˣ := Units.map (algebraMap ℚ (PolyLoc S)).toMonoidHom
    (Units.mk0 (N : ℚ) (by exact_mod_cast hN.ne')) with hudef
  have hucoe : (u : PolyLoc S) = (N : PolyLoc S) := by
    rw [hudef, Units.coe_map, Units.val_mk0]
    simp
  have hu : C.d (Fin.last n) (C.Dv (β - Finsupp.single (Fin.last n) 1) (t ^ N)) = ↑u := by
    rw [hDv, Derivation.leibniz, hCd, Derivation.map_natCast, smul_zero, add_zero, smul_eq_mul,
      mul_one, hucoe]
  have hlam : lam (pad (n + 1) ek) β < 1 := by
    rw [hβdef, lam_single]
    simp [pad]
  have hNt : 0 < tailSum k β := by rw [tailSum_single_ge (by simp; omega)]; exact hN
  have hunit : IsUnit (C.D β (t ^ N)) := by
    rw [hβdef, Chart.D_single, iterate_pow_of_eq_one _ hCd, Nat.descFactorial_self, Nat.sub_self,
      pow_zero, mul_one]
    exact hfunit
  have hW : nextW (pad (n + 1) ek) k β = 1 / N := by
    rw [nextW, tailSum_single_ge (by simp; omega)]
    rw [hβdef, lam_single]
    simp [pad]
  have hb : ∀ i : Fin (n + 1), (i : ℕ) < k → nextW (pad (n + 1) ek) k β ≤ pad (n + 1) ek i := by
    intro i hi
    rw [hW]
    have hin : (i : ℕ) < n := by omega
    simp only [pad, dite_eq_left hin]
    refine le_trans ?_ (hpos ⟨i, hin⟩ hi)
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    rw [hNdef]; push_cast
    exact one_div_le_one_div_of_le hdq (by linarith)
  have hstep := IsRun.step (I := It) hk1 (t ^ N) htN β (Fin.last n) (by simp; omega)
    (by simp [hβdef]) hlam hNt hunit hb u hu (IsRun.refl _ _ _)
  have hfull := (hrun'.mono (le_sup_left : I.map ψ ≤ It)).trans hstep
  -- Step 3: the transfer bound on `S'`
  set C'' := nextChart C ⟨k, hk1⟩ (Fin.last n) (C.Dv (β - Finsupp.single (Fin.last n) 1) (t ^ N))
    u hu with hC''def
  set Et := nextE (pad (n + 1) ek) k (nextW (pad (n + 1) ek) k β) with hEtdef
  obtain ⟨C3, hC3, hbound⟩ := hfull.transfer_bound_pos (polyLoc_dec hdec)
    (hnn := le_refl (n + 1)) (Compat.id c.polyLoc)
  have hC3x : ∀ j, C3.x j = C''.x j := fun j => by
    have := hC3.x j; simpa [Fin.castLE_refl] using this
  have heq : ∀ J' : MC (PolyLoc S) (n + 1), J'.Adm It → J'.e = Et → ∀ v,
      J'.RF v = C''.RF Et v := by
    intro J' hJ' he v
    have h := (hbound J' (by rwa [Ideal.map_id])).2 (by rw [pad_refl]; exact he) v
    rw [h, pad_refl]
    exact Chart.RF_congr (fun j _ => hC3x j) v
  have hEt : Et = nextE (pad (n + 1) ek) k (1 / N) := by rw [hEtdef, hW]
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap ⟨k, hk1⟩ (Fin.last n) with hσdef
  have hEtσ : ∀ a : Fin n, Et (σ (Fin.castSucc a)) = ek a := fun a => by
    rw [hEt]; exact nextE_pad_swap hk1 hz _ a
  have hEtk : Et ⟨k, hk1⟩ = 1 / N := by rw [hEt]; exact nextE_pad_at hk1 _
  have hlamEt : ∀ α : Fin (n + 1) →₀ ℕ, lam Et α =
      lam ek (Finsupp.equivFunOnFinite.symm fun a => α (σ (Fin.castSucc a))) +
        α ⟨k, hk1⟩ * (1 / N) := by
    intro α
    rw [lam, sum_swap_last hk1, lam]
    simp only [Finsupp.coe_equivFunOnFinite_symm, hEtσ, hEtk, ← hσdef]
  -- Step 4: the flowed centre
  set y : Fin n → PolyLoc S := fun a => flowN δ N (ck.x a) with hydef
  have hy : ∀ a, ∃ h, y a = ψ (ck.x a) + t * h := fun a =>
    ⟨_, by simp only [hydef, hNdef]; exact flowN_succ δ d (ck.x a)⟩
  set z : Fin (n + 1) → PolyLoc S := Fin.lastCases t y with hzdef
  have hzunit := flow_jac_isUnit ck y hy
  set cz := C.change z hzunit with hczdef
  have hcz : cz.IsCentred :=
    Chart.IsCentred.change' (Chart.polyLoc_isCentred ck hck) z hzunit (flow_span_eq ck y hy)
  have hczx : cz.x (Fin.last n) = t := by simp [hczdef, hzdef]
  have hczd : cz.d (Fin.last n) t = 1 := by rw [← hczx, cz.d_x]; simp
  have hu2 : cz.d (Fin.last n) ((N : PolyLoc S) * t) = ↑u := by
    rw [Derivation.leibniz, hczd, Derivation.map_natCast, smul_zero, add_zero, smul_eq_mul,
      mul_one, hucoe]
  set J2c := nextChart cz ⟨k, hk1⟩ (Fin.last n) ((N : PolyLoc S) * t) u hu2 with hJ2cdef
  have hNtm : (N : PolyLoc S) * t ∈ maximalIdeal (PolyLoc S) :=
    Ideal.mul_mem_left _ _ polyT_mem_maximal
  have hJ2c : J2c.IsCentred := (hcz.replace (Fin.last n) _ u hu2 hNtm).reindex _
  have hNinvq : (0 : ℚ) ≤ 1 / N := by positivity
  have hEt_nn : ∀ j, 0 ≤ Et j := fun j => by
    rw [hEt]; simp only [nextE]; split_ifs
    · simp only [pad]; split_ifs
      · exact hnn _
      · exact le_rfl
    · exact hNinvq
    · exact le_rfl
  have hbk : ∀ a : Fin n, (a : ℕ) < k → (1 : ℚ) / N ≤ ek a := fun a ha => by
    refine le_trans ?_ (hpos a ha)
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    rw [hNdef]; push_cast
    exact one_div_le_one_div_of_le hdq (by linarith)
  have hEt_anti : Antitone Et := by
    rw [hEt]; exact nextE_pad_antitone hnn hanti hkn hNinvq hbk
  -- `tᴺ` has weight `1`
  have hJ2xk : J2c.x ⟨k, hk1⟩ = (N : PolyLoc S) * t := by
    simp only [hJ2cdef, nextChart, Chart.reindex_x, Equiv.swap_apply_left, Chart.replace_x_self]
  have htN_RF : t ^ N ∈ J2c.RF Et 1 := by
    have h1 : (N : PolyLoc S) * t ∈ J2c.RF Et (1 / N) := by
      rw [← hJ2xk, ← hEtk]; exact J2c.x_mem_RF Et _ (by rw [hEtk]; positivity)
    have h2 := J2c.pow_mem_RF Et h1 N
    rw [show ((N : ℕ) : ℚ) * (1 / N) = 1 by field_simp] at h2
    have : t ^ N = ((u⁻¹ : (PolyLoc S)ˣ) : PolyLoc S) ^ N * ((N : PolyLoc S) * t) ^ N := by
      rw [← mul_pow, ← mul_assoc, show (N : PolyLoc S) = ↑u from hucoe.symm,
        Units.inv_mul, one_mul]
    rw [this]; exact Ideal.mul_mem_left _ _ h2
  -- Claim A: the flow maps weighted ideals into those of the flowed chart
  have hΦx : ∀ a, flowHom δ N hN (ck.x a) = Ideal.Quotient.mk (Ideal.span {t ^ N}) (y a) :=
    fun a => rfl
  have hczxa : ∀ a : Fin n, cz.x (Fin.castSucc a) = y a := fun a => by simp [hczdef, hzdef]
  have hmono : ∀ α : Fin n →₀ ℕ, (∀ a, ek a = 0 → α a = 0) → ∀ v, v ≤ lam ek α →
      ∏ a, y a ^ α a ∈ J2c.RF Et v := by
    intro α hα0 v hv
    set α' : Fin (n + 1) →₀ ℕ := Finsupp.equivMapDomain σ (pushIdx (Nat.le_succ n) α) with hα'def
    have hα'σ : ∀ a, α' (σ (Fin.castSucc a)) = α a := fun a => by
      rw [hα'def, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply, ← castLE_succ_eq,
        pushIdx_apply]
    have hα'k : α' ⟨k, hk1⟩ = 0 := by
      rw [hα'def, Finsupp.equivMapDomain_apply, hσdef, Equiv.symm_swap, Equiv.swap_apply_left]
      exact pushIdx_apply_ge _ _ _ (by simp)
    have hprod : ∏ j, J2c.x j ^ α' j = ∏ a, y a ^ α a := by
      rw [hJ2cdef, prod_nextChart_last cz hk1 _ u hu2 α', hα'k, pow_zero, mul_one]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← hσdef, hα'σ, hczxa]
    rw [← hprod]
    refine Ideal.subset_span ⟨α', fun j hj => ?_, ?_, rfl⟩
    · obtain ⟨j', rfl⟩ : ∃ j', σ j' = j := ⟨σ.symm j, by simp⟩
      rw [hα'def, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
      cases j' using Fin.lastCases with
      | last => exact pushIdx_apply_ge _ _ _ (by simp)
      | cast a =>
        rw [← castLE_succ_eq, pushIdx_apply]
        exact hα0 a (by rw [← hEtσ a]; exact hj)
    · rw [hlamEt, hα'k]
      simp only [Nat.cast_zero, zero_mul, add_zero]
      convert hv using 2
      ext a; simp [hα'σ]
  have hclaimA : ∀ v ≤ (1 : ℚ), ∀ f ∈ ck.RF ek v, flowN δ N f ∈ J2c.RF Et v := by
    intro v hv f hf
    have hmap : Ideal.map (flowHom δ N hN) (ck.RF ek v) ≤
        Ideal.map (Ideal.Quotient.mk (Ideal.span {t ^ N})) (J2c.RF Et v) := by
      rw [Chart.RF, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨α, hα0, hαv, rfl⟩, rfl⟩
      have : flowHom δ N hN (∏ a, ck.x a ^ α a) =
          Ideal.Quotient.mk (Ideal.span {t ^ N}) (∏ a, y a ^ α a) := by
        simp only [map_prod, map_pow, hΦx]
      rw [SetLike.mem_coe, this]
      exact Ideal.mem_map_of_mem _ (hmono α hα0 v hαv)
    have h1 := hmap (Ideal.mem_map_of_mem _ hf)
    rw [flowHom_apply, ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h1
    have hle : J2c.RF Et v ⊔ Ideal.span {t ^ N} ≤ J2c.RF Et v := sup_le le_rfl (by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact J2c.RF_antitone Et hv htN_RF)
    exact hle h1
  -- Claim B: `ψ(I)` is admissible for the flowed centre
  have hiter : ∀ m, ∀ f ∈ I, δ^[m] f ∈ I := by
    intro m
    induction m with
    | zero => intro f hf; exact hf
    | succ m ih => intro f hf; rw [Function.iterate_succ_apply']; exact hδ _ (ih f hf)
  have hclaimB : I.map ψ ≤ J2c.RF Et 1 := by
    have key : ∀ r : ℕ, I.map ψ ≤ J2c.RF Et 1 ⊔ Ideal.span {t ^ r} * I.map ψ := by
      intro r
      induction r with
      | zero =>
        rw [pow_zero, Ideal.span_singleton_one, Ideal.top_mul]; exact le_sup_right
      | succ r ih =>
        rw [Ideal.map_le_iff_le_comap]
        intro f hf
        rw [Ideal.mem_comap]
        have hflow := flowN_succ δ d f
        rw [← hNdef] at hflow
        set sumT := ∑ m ∈ Finset.range d,
          toPolyLoc (((m + 1).factorial : ℚ)⁻¹ • δ^[m + 1] f) * polyT ^ m with hsumTdef
        have hsum : sumT ∈ I.map ψ := Ideal.sum_mem _ fun m _ =>
          Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem ψ
            (Submodule.smul_of_tower_mem I _ (hiter (m + 1) f hf)))
        have hA : flowN δ N f ∈ J2c.RF Et 1 := hclaimA 1 le_rfl f (hadm hf)
        have hψf : ψ f = flowN δ N f - t * sumT := by rw [hflow]; ring
        rw [hψf]
        refine Ideal.sub_mem _ (Ideal.mem_sup_left hA) ?_
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (ih hsum)
        rw [← hab, mul_add]
        refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ ha))
          (Ideal.mem_sup_right ?_)
        rw [pow_succ', ← Ideal.span_singleton_mul_span_singleton, mul_assoc]
        exact Ideal.mul_mem_mul (Ideal.subset_span rfl) hb
    have hN' : Ideal.span {t ^ N} * I.map ψ ≤ J2c.RF Et 1 := by
      refine le_trans Ideal.mul_le_left ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact htN_RF
    exact (key N).trans (sup_le le_rfl hN')
  -- the flowed centre is admissible, hence has the same weighted ideals as the run
  have hadm2 : It ≤ J2c.RF Et 1 :=
    sup_le hclaimB (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact htN_RF)
  have hRF := heq ⟨J2c, Et, hJ2c, hEt_nn, hEt_anti⟩ hadm2 rfl
  have hi1 : Fin.castSucc i ≠ ⟨k, hk1⟩ := fun h => by
    have := congrArg Fin.val h; simp at this; omega
  have hi2 : Fin.castSucc i ≠ Fin.last n := (Fin.castSucc_lt_last i).ne
  have hJ2x : J2c.x (Fin.castSucc i) = y i := by
    simp only [hJ2cdef, nextChart, Chart.reindex_x, Equiv.swap_apply_of_ne_of_ne hi1 hi2]
    rw [Chart.replace_x_ne _ _ _ _ _ hi2, hczxa]
  have hEti : Et (Fin.castSucc i) = ek i := by
    have := hEtσ i
    rwa [hσdef, Equiv.swap_apply_of_ne_of_ne hi1 hi2] at this
  have hyi : y i ∈ C''.RF Et (ek i) := by
    have h1 : y i ∈ J2c.RF Et (Et (Fin.castSucc i)) := by
      rw [← hJ2x]; exact J2c.x_mem_RF Et _ (by rw [hEti]; exact (hsupp i).2 hi)
    rw [hEti] at h1
    have h2 := hRF (ek i)
    exact h2 ▸ h1
  -- extraction of the `t`-coefficient
  have hgen : ∀ g ∈ {f | ∃ α : Fin (n + 1) →₀ ℕ, (∀ j, Et j = 0 → α j = 0) ∧ ek i ≤ lam Et α ∧
      f = ∏ j, C''.x j ^ α j},
      (dualLoc g).fst ∈ ck.RF ek (ek i) ∧ (dualLoc g).snd ∈ ck.RF ek (ek i - 1 / N) := by
    rintro _ ⟨α, hα0, hαv, rfl⟩
    set β' : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => α (σ (Fin.castSucc a))
      with hβ'def
    have hβ'0 : ∀ a, ek a = 0 → β' a = 0 := fun a ha => by
      simp only [hβ'def, Finsupp.coe_equivFunOnFinite_symm]
      exact hα0 _ (by rw [hEtσ]; exact ha)
    have hlamβ := hlamEt α
    rw [hC''def, prod_nextChart_last C hk1 _ u hu α, hDv, map_mul, map_prod, map_pow]
    have hP : (∏ a : Fin n, dualLoc (C.x (Fin.castSucc a) ^ α (σ (Fin.castSucc a)))) =
        inl (∏ a, ck.x a ^ β' a) := by
      rw [← inlHom_apply, map_prod]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [map_pow, Chart.polyLoc_x_castSucc, dualLoc_toPolyLoc, hβ'def,
        Finsupp.coe_equivFunOnFinite_symm, map_pow]
      rfl
    have hNt : dualLoc ((N : PolyLoc S) * t) = inr (N : S) := by
      rw [map_mul, map_natCast, dualLoc_polyT, ← inl_natCast, inl_mul_inr, smul_eq_mul, mul_one]
    rw [← hσdef, hP, hNt]
    have hmem0 : ∀ v, v ≤ lam ek β' → ∏ a, ck.x a ^ β' a ∈ ck.RF ek v := fun v hv =>
      Ideal.subset_span ⟨β', hβ'0, hv, rfl⟩
    rcases Nat.lt_or_ge (α ⟨k, hk1⟩) 2 with hm | hm
    · interval_cases hmk : α ⟨k, hk1⟩
      · rw [pow_zero, mul_one]
        simp only [fst_inl, snd_inl]
        refine ⟨hmem0 _ ?_, zero_mem _⟩
        have h0 : lam ek β' = lam Et α := by rw [hlamβ, hβ'def]; simp
        linarith
      · rw [pow_one, inl_mul_inr]
        simp only [fst_inr, snd_inr, smul_eq_mul]
        refine ⟨zero_mem _, Ideal.mul_mem_right _ _ (hmem0 _ ?_)⟩
        have h1 : lam ek β' = lam Et α - 1 / N := by rw [hlamβ, hβ'def]; push_cast; ring
        linarith
    · obtain ⟨m, hm'⟩ : ∃ m, α ⟨k, hk1⟩ = m + 2 := ⟨α ⟨k, hk1⟩ - 2, by omega⟩
      rw [hm', pow_add, pow_two, inr_mul_inr, mul_zero, mul_zero]
      simp
  have hext := dualLoc_span (ck.RF_antitone ek (by
    have : (0 : ℚ) ≤ 1 / N := hNinvq; linarith)) hgen (y i) hyi
  rw [hydef] at hext
  simp only at hext
  rw [dualLoc_flowN δ hN2] at hext
  simp only [snd_add, snd_inl, snd_inr, zero_add] at hext
  -- discreteness of the weights
  have hdisc : ck.RF ek (ek i - 1 / N) ≤ ck.RF ek (ek i) := by
    apply Ideal.span_mono
    rintro _ ⟨α, hα0, hαv, rfl⟩
    refine ⟨α, hα0, ?_, rfl⟩
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    have hlamw : (d : ℚ) * lam ek α = ((∑ j, α j * w j : ℕ) : ℚ) := by
      rw [lam, Finset.mul_sum]; push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hw j]; ring
    have hwi : (d : ℚ) * ek i = w i := (hw i).symm
    have h1 : (w i : ℚ) - d / N ≤ ((∑ j, α j * w j : ℕ) : ℚ) := by
      rw [← hwi, ← hlamw]
      have := mul_le_mul_of_nonneg_left hαv hdq.le
      calc (d : ℚ) * ek i - d / N = d * (ek i - 1 / N) := by ring
        _ ≤ d * lam ek α := this
    have h2 : (d : ℚ) / N < 1 := by
      rw [div_lt_one (by positivity)]; rw [hNdef]; push_cast; linarith
    have h3 : w i ≤ ∑ j, α j * w j := by
      have : (w i : ℚ) < ((∑ j, α j * w j : ℕ) : ℚ) + 1 := by linarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    have h4 : (d : ℚ) * ek i ≤ d * lam ek α := by
      rw [hwi, hlamw]; exact_mod_cast h3
    exact le_of_mul_le_mul_left h4 hdq
  exact hdisc hext.2

end K

section Length

variable {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {n : ℕ}

theorem length_le_of_derivations_pos (hdec : ∀ x : S, x ∈ maximalIdeal S ∨ IsUnit x)
    {I : Ideal S} {c : Chart S n} {k : ℕ} {ck : Chart S n}
    {ek : Fin n → ℚ} (hrun : IsRun I 0 c 0 k ck ek) (hadm : I ≤ ck.RF ek 1) (hck : ck.IsCentred)
    (hnn : ∀ i, 0 ≤ ek i) (hanti : Antitone ek) (hsupp : ∀ i, ek i ≠ 0 ↔ (i : ℕ) < k)
    {m : ℕ} (δ : Fin m → Derivation ℚ S S) (hδ : ∀ j, ∀ f ∈ I, δ j f ∈ I) (y : Fin m → S)
    (hy : IsUnit (Matrix.of fun j l => δ j (y l)).det) : k + m ≤ n := by
  have hkn : k ≤ n := hrun.stage_le (Nat.zero_le _)
  -- `δ_j` maps the centre coordinates into `𝔪`
  have hmem : ∀ j, ∀ i : Fin n, (i : ℕ) < k → δ j (ck.x i) ∈ maximalIdeal S := by
    intro j i hi
    have h := deriv_mem_RF_pos hdec hrun hadm hck hnn hanti hsupp (δ j) (hδ j) i hi
    exact hck.RF_le_maximalIdeal (lt_of_le_of_ne (hnn i) (Ne.symm ((hsupp i).2 hi))) h
  set T := {i : Fin n // k ≤ (i : ℕ)}
  set A : Matrix (Fin m) T (ResidueField S) := Matrix.of fun j t => residue S (δ j (ck.x t.1))
  set B : Matrix T (Fin m) (ResidueField S) := Matrix.of fun t l => residue S (ck.d t.1 (y l))
  have hM : (residue S).mapMatrix (Matrix.of fun j l => δ j (y l)) = A * B := by
    ext j l
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, A, B]
    have h1 : δ j (y l) = ∑ i, δ j (ck.x i) * ck.d i (y l) := by
      conv_lhs => rw [ck.eq_sum (δ j)]
      rw [Derivation.sum_apply']
      simp only [Derivation.smul_apply, smul_eq_mul]
    rw [h1, map_sum]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => k ≤ (i : ℕ))]
    have h2 : ∑ i : {i : Fin n // ¬ k ≤ (i : ℕ)}, residue S (δ j (ck.x i.1) * ck.d i.1 (y l)) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [map_mul, (residue_eq_zero_iff _).2 (hmem j i.1 (by have := i.2; omega)), zero_mul]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
  have hdet : IsUnit (A * B).det := by
    rw [← hM, ← RingHom.map_det]
    exact hy.map _
  have hrank : (A * B).rank = m := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 hdet), Fintype.card_fin]
  have hle : (A * B).rank ≤ Fintype.card T := (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width
  have hcard : Fintype.card T = n - k := by
    rw [Fintype.card_subtype, ← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
    have : (Finset.univ.filter fun i : Fin n => k ≤ (i : ℕ)).map ⟨Fin.val, Fin.val_injective⟩ =
        Finset.Ico k n := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk, Finset.mem_Ico]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact ⟨hi, i.2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨x, h2⟩, h1, rfl⟩
    rw [this, Nat.card_Ico]
  omega

end Length

end BezoutCounterexample.Principalization
