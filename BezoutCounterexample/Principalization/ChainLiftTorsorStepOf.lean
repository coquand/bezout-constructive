import BezoutCounterexample.Principalization.ChainLiftBridgePtL
import BezoutCounterexample.Constructive.ChainLiftOffPresData

/-!
# Chain lifting for a torsor step, with given lifts and the canonical presentation (leaf, C2)

`chainLift_torsor_step` (ChainLiftBridgeFinal) produces its integer lifts `gZ, Dg` (by
`finite_choice`) and its relations `G'` (by `exists_offStep`) as existential witnesses. Here the
lifts are parameters and the relations are the canonical `presList` (ChainLiftOffPresData), so the
torsor presentation of the next stage can be built as data:

* `chainLift_torsor_step_of`: `ChainLift (PtG G) (PtG (presList G gZ dd)) π` (same proof after
  the witnesses; `OffStep` = `offStepOf`).

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive IsLocalization
open scoped Matrix

section HM

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (d : ℕ) (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hd hw in
/-- **Chain lifting for one of HM's torsor steps, with given integer lifts** (twin of
`chainLift_torsor_step`): for integer lifts `gZ` of the torsor generators (`toA (gZ i) = Dg₀ · gᵢ`),
the canonical torsor presentation `presList G gZ dd` lifts chains. -/
theorem chainLift_torsor_step_of [Constructive.Enum A] [Fact (Constructive.HasPres A)] {π : A}
    (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
    {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ)) (e : Quo (GQ G) ≃+* A)
    (C : ChartCoverPtL I v₀ 𝔭) (hdim₀ : ∃ k, (C.D k).n = n) (hv1 : v₀ 1 ≠ 0)
    (hcon : ∃ Dc : ℕ, 0 < Dc ∧ ConormalInj G (Dc : MvPolynomial (Fin (m + n)) ℤ))
    (gZ : Fin (nGen hI hmax h𝔭 d + 1) → MvPolynomial (Fin (m + n)) ℤ) (Dg₀ : ℕ) (hDg₀ : 0 < Dg₀)
    (hgZA : ∀ i, toA G e (gZ i) = (Dg₀ : A) * genCoeff hI hmax h𝔭 d π i) :
    ChainLift (PtG G) (PtG (presList G gZ (fun i => (genDeg hI hmax h𝔭 d i).toNat))) (fun x k => x (Fin.castAdd _ k)) := by
  revert gZ Dg₀ hDg₀ hgZA
  -- destructure first, so that `omega` below does not see `hcon` (it would use `hcon.choose`)
  obtain ⟨Dc, hDc, hinj⟩ := hcon
  -- all charts have `n` functions
  obtain ⟨k₁, hk₁⟩ := hdim₀
  have hdim : ∀ k, (C.D k).n = n := fun k => (LocDataPt.n_eq (C.D k) (C.D k₁)).trans hk₁
  -- the head count from the invariant
  set kc := (Finset.univ.filter fun j : Fin n => v₀ j ≠ 0).card
  have hkn : kc ≤ n := (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  obtain ⟨k₀⟩ : Nonempty (Fin C.n) := by
    rcases Nat.eq_zero_or_pos C.n with h0 | h0
    · exfalso
      have h1 := C.one
      have : C.i = 1 := by
        rw [← h1, Finset.sum_eq_zero (fun k _ => absurd k.2 (by omega)), add_zero]
      exact h𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (this ▸ C.hi))
    · exact ⟨⟨0, h0⟩⟩
  have hhead := fun k => head_support_pt (C.D k) (hdim k)
  have h1n : 1 < n := by
    by_contra h
    apply hv1
    have := congrFun (C.D k₀).hv 1
    rw [← this]
    simp only [ext0]
    rw [dif_neg (by rw [hdim k₀]; omega)]
  have hn : 0 < n := by omega
  have hk2 : 2 ≤ kc := by
    have hek : ∀ j : Fin (C.D k₀).n, (C.D k₀).ek j = v₀ j := fun j => by
      have := congrFun (C.D k₀).hv j; rwa [ext0_apply] at this
    have hn' : 1 < (C.D k₀).n := by rw [hdim k₀]; exact h1n
    have hv1' : v₀ 1 ≠ 0 := hv1
    have hv0 : v₀ 0 ≠ 0 := by
      have hle : (C.D k₀).ek ⟨1, hn'⟩ ≤ (C.D k₀).ek ⟨0, by omega⟩ :=
        (C.D k₀).inv.anti (Fin.le_def.2 (by simp))
      rw [hek, hek] at hle
      have hnn : 0 ≤ v₀ 1 := by rw [← hek ⟨1, hn'⟩]; exact (C.D k₀).inv.nonneg _
      intro h0
      exact hv1 (le_antisymm (h0 ▸ hle) hnn)
    have hsub : ({⟨0, by omega⟩, ⟨1, h1n⟩} : Finset (Fin n)) ⊆
        Finset.univ.filter fun j : Fin n => v₀ j ≠ 0 := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp [hv0, hv1]
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (by simp [Fin.ext_iff])] at this
  set ι := Fin (nGen hI hmax h𝔭 d + 1)
  set gen := genCoeff hI hmax h𝔭 d π
  set dd : ι → ℕ := fun i => (genDeg hI hmax h𝔭 d i).toNat
  have hdd : ∀ i, 0 < dd i := fun i => by
    have := genDeg_pos hI hmax h𝔭 d i; simp only [dd]; omega
  have hddZ : ∀ i, ((dd i : ℕ) : ℤ) = genDeg hI hmax h𝔭 d i := fun i => by
    have := genDeg_pos hI hmax h𝔭 d i; simp only [dd]; omega
  -- 1. integer lifts of the torsor generators
  have hsurj : ∀ x : A, ∃ p, e (Ideal.Quotient.mk _ p) = x := fun x => by
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨p, rfl⟩
  intro gZ Dg₀ hDg₀ hgZA
  -- the torsor presentation `presList` and its `OffStep` (data, `offStepOf`)
  obtain ⟨D₂, E, hD₂, hEd, hE⟩ := exists_E dd hdd
  have hspec := offStepOf_spec G gZ dd hD₂ E hEd hE
  rw [← hspec.1, ← hspec.2.1, ← hspec.2.2.2.2.2]
  obtain ⟨hPt, hPt', hOg, hOd, hOE, hOπ⟩ := hspec
  set O := offStepOf G gZ dd hD₂ E hEd hE with hOdef
  set G' := presList G gZ dd with hG'def
  -- 3. conormal injectivity (given: from smoothness or from a certificate; destructured above)
  -- 4. the charts
  have hP := fun k => chart_partition_pt G e (C.D k) (hdim k) hkn hn
  obtain ⟨sC, hP⟩ := finite_choice hP
  obtain ⟨aC, hP⟩ := finite_choice hP
  obtain ⟨ãC, hP⟩ := finite_choice hP
  obtain ⟨DqC, hP⟩ := finite_choice hP
  obtain ⟨TC, hP⟩ := finite_choice hP
  obtain ⟨MC, hP⟩ := finite_choice hP
  obtain ⟨βC, hP⟩ := finite_choice hP
  obtain ⟨ωC, hP⟩ := finite_choice hP
  have hDqC := fun k => (hP k).1
  have hTxC := fun k => (hP k).2.1
  have hnumC := fun k => (hP k).2.2.1
  have hpartC := fun k => (hP k).2.2.2
  obtain ⟨pgk, hpgk⟩ := finite_choice fun k : Fin C.n => hsurj (C.D k).g
  obtain ⟨Dgk, gk, hDgk, hgk⟩ := exists_int_mul_fin pgk
  have hgkA : ∀ k, toA G e (gk k) = (Dgk : A) * (C.D k).g := fun k => by
    rw [toA, hgk k, map_mul, map_mul, map_natCast, map_natCast, hpgk]
  have hH := fun k => chart_heads_L hI hmax h𝔭 d hd hw C k G e (hdim k)
    hkn (hhead k) hπ (sC k) (aC k) (hnumC k) (ãC k) (DqC k) (fun q => (hDqC k q).1)
    (fun q => (hDqC k q).2) gZ Dg₀ hDg₀ hgZA (gk k) Dgk hDgk (hgkA k)
  obtain ⟨Kk, hH⟩ := finite_choice hH
  obtain ⟨ℓk, hH⟩ := finite_choice hH
  have hKk := fun k => (hH k).1
  have hℓk := fun k => (hH k).2.1
  have hlidk := fun k => (hH k).2.2.1
  have hHk := fun k => (hH k).2.2.2
  set uk : Fin C.n → MvPolynomial (Fin (m + n)) ℤ := fun k => (Kk k : _) * gk k ^ ℓk k
  set T' : (Σ k : Fin C.n, RowIdx (m + n) (n - kc)) → ChartData G :=
    fun p => (TC p.1 p.2).scale (uk p.1)
  obtain ⟨H'⟩ : Nonempty (∀ p, ChartHead (T' p) gZ dd kc) :=
    finite_nonempty_pi fun p => hHk p.1 (TC p.1 p.2) p.2 (hTxC p.1 p.2)
  -- 5. the global partition in `A`
  set 𝔉 : Ideal A := Ideal.span (Set.range gen)
  set 𝔅 : Ideal A := 𝔉 ⊔ Ideal.span (Set.range fun p => toA G e (T' p).c)
  have hF1 : (compFil hI hmax h𝔭 d).F 1 ≤ 𝔉 := by
    rw [← span_gensF, Ideal.span_le]
    intro x hx
    obtain ⟨i, hi, -⟩ := gen_covers hI hmax h𝔭 d π 1 le_rfl (by exact_mod_cast hd) x hx
    exact Ideal.subset_span ⟨i, hi⟩
  have hinvA : ∀ D : ℕ, 0 < D → algebraMap ℚ A ((D : ℚ))⁻¹ * (D : A) = 1 := fun D hD => by
    rw [← map_natCast (algebraMap ℚ A), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hD.ne'),
      map_one]
  have hone : (1 : A) ∈ 𝔅 := by
    refine one_mem_of_radical 𝔉 𝔅 le_sup_left C.i C.f (fun k => (C.D k).g) C.one
      (Ideal.le_radical (hF1 (comp_le_F1 hI hmax h𝔭 d hd hw C.hi))) fun k => ?_
    -- `g_k ∈ √𝔅`
    have hga : ∀ q, (C.D k).g ^ ℓk k * aC k (headIdx hkn q) ∈ 𝔅.radical := fun q => by
      obtain ⟨N, hN⟩ := hlidk k q
      refine ⟨N + 1, ?_⟩
      have : ((C.D k).g ^ ℓk k * aC k (headIdx hkn q)) ^ (N + 1) =
          ((C.D k).g ^ N * aC k (headIdx hkn q)) *
            ((C.D k).g ^ (ℓk k * (N + 1) - N) * aC k (headIdx hkn q) ^ N) := by
        have hle : N ≤ ℓk k * (N + 1) := by nlinarith [hℓk k]
        rw [mul_pow, ← pow_mul, pow_succ (aC k _)]
        conv_lhs => rw [show ℓk k * (N + 1) = N + (ℓk k * (N + 1) - N) by omega, pow_add]
        ring
      rw [this]
      exact le_sup_left (α := Ideal A) (Ideal.mul_mem_right _ _ hN)
    have hc' : ∀ τ, toA G e (T' ⟨k, τ⟩).c =
        (Kk k : A) * (Dgk : A) ^ ℓk k * (C.D k).g ^ ℓk k * e (Ideal.Quotient.mk _ (toQ (TC k τ).c)) :=
      fun τ => by
        show toA G e ((Kk k : MvPolynomial (Fin (m + n)) ℤ) * gk k ^ ℓk k * (TC k τ).c) = _
        have h1 : toA G e ((Kk k : MvPolynomial (Fin (m + n)) ℤ)) = (Kk k : A) := by simp [toA]
        have h2 : toA G e (gk k ^ ℓk k) = toA G e (gk k) ^ ℓk k := by
          rw [← toAHom_apply, map_pow]; rfl
        rw [toA_mul, toA_mul, h1, h2, hgkA k, toA]; ring
    have hpow : (C.D k).g ^ (MC k + ℓk k) ∈ 𝔅.radical := by
      have hmem : ((Kk k : A) * (Dgk : A) ^ ℓk k) * (C.D k).g ^ (MC k + ℓk k) ∈ 𝔅.radical := by
        have : ((Kk k : A) * (Dgk : A) ^ ℓk k) * (C.D k).g ^ (MC k + ℓk k) =
            ∑ τ, βC k τ * toA G e (T' ⟨k, τ⟩).c + ∑ q, ((Kk k : A) * (Dgk : A) ^ ℓk k * ωC k q) *
              ((C.D k).g ^ ℓk k * aC k (headIdx hkn q)) := by
          rw [pow_add, hpartC k]
          simp only [hc', add_mul, Finset.sum_mul, mul_add, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
        rw [this]
        refine Ideal.add_mem _ (Ideal.le_radical (Ideal.sum_mem _ fun τ _ =>
          Ideal.mul_mem_left _ _ (le_sup_right (α := Ideal A) (Ideal.subset_span ⟨⟨k, τ⟩, rfl⟩))))
          (Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (hga q))
      have hunit : algebraMap ℚ A (((Kk k : ℚ) * (Dgk : ℚ) ^ ℓk k))⁻¹ *
          ((Kk k : A) * (Dgk : A) ^ ℓk k) = 1 := by
        have := hinvA (Kk k * Dgk ^ ℓk k) (Nat.mul_pos (hKk k) (pow_pos hDgk _))
        push_cast at this; exact this
      have := Ideal.mul_mem_left (𝔅.radical) (algebraMap ℚ A (((Kk k : ℚ) * (Dgk : ℚ) ^ ℓk k))⁻¹) hmem
      rwa [← mul_assoc, hunit, one_mul] at this
    obtain ⟨r, hr⟩ := hpow
    exact ⟨(MC k + ℓk k) * r, by rw [pow_mul]; exact hr⟩
  -- 6. the partition as a combination
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hone
  rw [Ideal.mem_span_range_iff_exists_fun] at hx hy
  obtain ⟨β, rfl⟩ := hx
  obtain ⟨ε, rfl⟩ := hy
  -- 7. the integer cover
  obtain ⟨K₀, q, hK₀, hq⟩ := int_cong_of_A G e (1 : MvPolynomial (Fin (m + n)) ℤ)
    (Sum.elim gZ fun p => (T' p).c * (Dc : MvPolynomial (Fin (m + n)) ℤ))
    (Sum.elim (fun i => β i * algebraMap ℚ A ((Dg₀ : ℚ))⁻¹)
      (fun p => ε p * algebraMap ℚ A ((Dc : ℚ))⁻¹)) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have h1 : toA G e (1 : MvPolynomial (Fin (m + n)) ℤ) = 1 := by simp [toA]
    rw [h1, ← hxy]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hgZA i]
      linear_combination (-(β i * gen i)) * hinvA Dg₀ hDg₀
    · refine Finset.sum_congr rfl fun p _ => ?_
      have h2 : toA G e ((T' p).c * (Dc : MvPolynomial (Fin (m + n)) ℤ)) =
          toA G e (T' p).c * (Dc : A) := by rw [toA_mul]; simp [toA]
      rw [h2]
      linear_combination (-(ε p * toA G e (T' p).c)) * hinvA Dc hDc)
  -- 8. flatten the chart index and conclude
  set eqv := (Fintype.equivFin (Σ k : Fin C.n, RowIdx (m + n) (n - kc))).symm
  have hd' : O.d = dd := hOd
  have Hf : ∀ j, ChartHead (T' (eqv j)) gZ O.d kc := fun j => hd' ▸ H' (eqv j)
  refine ChainLift.of_charts hn hk2 O hPt gZ hOg (fun j => T' (eqv j))
    (fun _ => (Dc : MvPolynomial (Fin (m + n)) ℤ)) (fun _ => hinj) Hf K₀ hK₀
    (fun i => q (Sum.inl i)) (fun j => q (Sum.inr (eqv j))) ?_
  have hsum := hq
  rw [Fintype.sum_sum_type, mul_one] at hsum
  simp only [Sum.elim_inl, Sum.elim_inr] at hsum
  convert hsum using 3
  rw [← eqv.sum_comp (fun p => q (Sum.inr p) * ((T' p).c * (Dc : MvPolynomial (Fin (m + n)) ℤ)))]
  exact Finset.sum_congr rfl fun j _ => by ring

end HM

end BezoutCounterexample.Principalization
