import BezoutCounterexample.Principalization.TorsorPt
import BezoutCounterexample.Principalization.LocDataPtProd
import BezoutCounterexample.Principalization.DropPt
import BezoutCounterexample.Principalization.ReesI4
import BezoutCounterexample.Principalization.ChartDimPt
import BezoutCounterexample.Principalization.ReesSmoothCert
import BezoutCounterexample.Principalization.TransferInvPos

/-!
# The torsor invariant at explicit points of `U` (D3.5 overnight, leaf)

`torsor_invAt` (TorsorInv) works at a maximal ideal `Q` of the torsor `U`: it finds a coordinate
`y_l ∉ Q` by `by_contra`, decides `s ∈ Q` by `by_cases`, and takes invariants at `Q ∩ R` and
`Q ∩ A` from `exists_invAt` (classical `local_structure`). At an explicit point `q` of `U`:

* `exists_torsorY_not_mem_pt`: the coordinate is found by a search over `Fin`, decided by the zero
  test of `q` (`∑ σᵢ yᵢ = 1`);
* `s ∈ q.ker` is decided by the zero test;
* off the exceptional divisor, the invariant at the point `q ∩ A` comes from
  `exists_invAt_semicont_ptL` (D3.4, through `local_structure_pt`; `hchart` and generators of `I`),
  and is carried to `q` by `invAt_rees_of_base` and `invAt_torsor_of_rees`, without an invariant at
  `q ∩ R`.

On the exceptional divisor the drop is `drop_pt` (coll-8a) at the point `q ∩ R`, with `ChartDim A`,
`hR4b` (`FormallySmooth R_q`, open) and charts of `R` as hypotheses (D3.7a); the invariant at
`q ∩ R` still comes from `exists_invAt`.

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing IsLocalization LaurentPolynomial

/-- Decided predicates on `Fin K`: one holds or none does. -/
lemma fin_exists_or_forall_pt {K : ℕ} (p : Fin K → Prop) (hp : ∀ k, p k ∨ ¬ p k) :
    (∃ k, p k) ∨ ∀ k, ¬ p k := by
  induction K with
  | zero => exact Or.inr fun k => k.elim0
  | succ K ih =>
    rcases hp 0 with h | h
    · exact Or.inl ⟨0, h⟩
    · rcases ih (fun k => p k.succ) (fun k => hp k.succ) with ⟨k, hk⟩ | hk
      · exact Or.inl ⟨k.succ, hk⟩
      · exact Or.inr fun k => Fin.cases h hk k

section TorsorInvPt

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] [hpA : Fact (HasPres A)]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  (hπ0 : π ≠ 0)

omit hpA in
/-- **A torsor coordinate off an explicit point**, by a decided search. -/
lemma exists_torsorY_not_mem_pt [Fact (Constructive.HasPres A)] [Constructive.Enum A] (q : Pt (Torsor hI hmax h𝔭 d hπ)) :
    ∃ l, torsorY hI hmax h𝔭 d hπ l ∉
      q.ker.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)) := by
  rcases fin_exists_or_forall_pt (fun l => torsorY hI hmax h𝔭 d hπ l ∉
      q.ker.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)))
    (fun l => (q.mem_ker_dec _).elim (fun h => Or.inr fun h' => h' h) Or.inl) with h | h
  · exact h
  · exfalso
    apply (Pt.ker_isMaximal q).ne_top
    rw [Ideal.eq_top_iff_one, ← Jou.sum_σ_mul (torsorY hI hmax h𝔭 d hπ)]
    refine Ideal.sum_mem _ fun l _ => q.ker.mul_mem_left _ ?_
    rcases q.mem_ker_dec (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)
      (torsorY hI hmax h𝔭 d hπ l)) with h' | h'
    · exact h'
    · exact absurd h' (h l)

omit hpA in
include hd hw in
/-- **Off the exceptional divisor, explicit points lie away from `V(𝔭)`** (point form of
`torsor_not_le_of_s_not_mem`: `exists_torsorY_not_mem_pt`, `compFPt_antitoneP'`, `compFPt_one_divP`). -/
lemma torsor_not_le_of_s_not_mem_pt [Constructive.Enum A] [Fact (Constructive.HasPres A)]
    (q : Pt (Torsor hI hmax h𝔭 d hπ)) (hsQ : torsorS hI hmax h𝔭 hπ ∉ q.ker) :
    ¬ 𝔭 ≤ q.ker.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
  set Q := q.ker
  intro hle
  obtain ⟨l, hl⟩ := exists_torsorY_not_mem_pt hI hmax h𝔭 hπ q
  apply hl
  set P := Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ))
  have hsP : reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) ∉ P := hsQ
  have hj := genDeg_pos hI hmax h𝔭 d l
  obtain ⟨m, hm⟩ : ∃ m : ℕ, genDeg hI hmax h𝔭 d l = m := ⟨(genDeg hI hmax h𝔭 d l).toNat, by omega⟩
  have hg : genCoeff hI hmax h𝔭 d π l ∈ 𝔭 := by
    have h1 := genCoeff_mem hI hmax h𝔭 d hπ l
    rw [compFil_F] at h1
    have h2 : compFPt I 𝔭 ((genDeg hI hmax h𝔭 d l : ℚ) / d) ≤ compFPt I 𝔭 (1 / d) := by
      refine h𝔭.compFPt_antitoneP' hI hmax ?_
      have : (1 : ℚ) ≤ genDeg hI hmax h𝔭 d l := by exact_mod_cast hj
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      exact div_le_div_of_nonneg_right this hd'.le
    rw [h𝔭.compFPt_one_divP hI hmax hd hw] at h2
    exact h2 h1
  have hgP : algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) (genCoeff hI hmax h𝔭 d π l) ∈ P := by
    have := hle hg
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A (ReesAlg (compFil hI hmax h𝔭 d))] at this
    exact this
  have heq : torsorY hI hmax h𝔭 d hπ l *
      reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) ^ m =
      algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)) (genCoeff hI hmax h𝔭 d π l) := by
    apply Subtype.ext
    show (LaurentPolynomial.C (genCoeff hI hmax h𝔭 d π l) * T (genDeg hI hmax h𝔭 d l)) *
      ((reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj) ^ m :
        ReesAlg (compFil hI hmax h𝔭 d)) : A[T;T⁻¹]) = algebraMap A A[T;T⁻¹] _
    rw [reesS_pow_coe, hm, mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one,
      LaurentPolynomial.C_eq_algebraMap]
  rw [← heq] at hgP
  have : P.IsPrime := Ideal.comap_isPrime _ _
  rcases ‹P.IsPrime›.mem_or_mem hgP with h | h
  · exact h
  · exact absurd (‹P.IsPrime›.mem_of_pow_mem m h) hsP

include hd hw hπ0 in
/-- **The invariant on the torsor at an explicit point** (point form of `torsor_invAt`). -/
theorem torsor_invAt_pt [Fact (Constructive.HasPres A)] [Constructive.Enum A] (lA : List A) (hlA : I = lspan lA)
    (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
    {dim : ℕ} (hN : ChartDim A dim)
    (hR4b : ∀ q : Pt (ReesAlg (compFil hI hmax h𝔭 d)),
      Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker))
    (hchartR : ∀ p : Pt (ReesAlg (compFil hI hmax h𝔭 d)), ∃ f, f ∉ p.ker ∧ ∃ n : ℕ,
      Nonempty (Chart (Localization.Away f) n))
    (q : Pt (Torsor hI hmax h𝔭 d hπ)) (hIq : torsorI hI hmax h𝔭 hd hπ ≤ q.ker) {v : ℕ → ℚ}
    (hv : InvAt (torsorI hI hmax h𝔭 hd hπ) q.ker v) :
    (torsorS hI hmax h𝔭 hπ ∈ q.ker ∧ toLex v₀ < toLex v) ∨
    (torsorS hI hmax h𝔭 hπ ∉ q.ker ∧
      I ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker ∧
      ¬ 𝔭 ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker ∧
      InvAt I (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker v) := by
  have hneg : ∀ j : ℤ, j ≤ 0 → (compFil hI hmax h𝔭 d).F j = ⊤ :=
    fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj
  have hId := I_le_compFil hI hmax h𝔭 hd
  have : Algebra.FiniteType A (ReesAlg (compFil hI hmax h𝔭 d)) :=
    reesAlg_finiteType hI hmax h𝔭 d hd hw
  have : Algebra.FiniteType ℚ (ReesAlg (compFil hI hmax h𝔭 d)) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : IsNoetherianRing (ReesAlg (compFil hI hmax h𝔭 d)) :=
    Algebra.FiniteType.isNoetherianRing A (ReesAlg (compFil hI hmax h𝔭 d))
  have : Algebra.Smooth ℚ (ReesAlg (compFil hI hmax h𝔭 d)) :=
    rees_smooth_cert hI hmax h𝔭 hd hw ⟨dim, hN⟩ lA hlA
  have : IsDomain (Torsor hI hmax h𝔭 d hπ) := torsor_isDomain hI hmax h𝔭 hπ hπ0
  have : Algebra.FiniteType ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_finiteType hI hmax h𝔭 hd hw hπ
  have : IsNoetherianRing (Torsor hI hmax h𝔭 d hπ) :=
    Algebra.FiniteType.isNoetherianRing ℚ (Torsor hI hmax h𝔭 d hπ)
  -- `torsor_smooth`, with the smoothness of the Rees algebra from its certificate (above)
  have : Algebra.Smooth ℚ (Torsor hI hmax h𝔭 d hπ) := by
    have := Jou.formallySmooth (torsorY hI hmax h𝔭 d hπ)
    refine ⟨Algebra.FormallySmooth.comp ℚ (ReesAlg (compFil hI hmax h𝔭 d)) _, ?_⟩
    exact Algebra.FinitePresentation.of_finiteType.1 inferInstance
  set Q := q.ker with hQ
  have hPm : (Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d))
    (Torsor hI hmax h𝔭 d hπ))).IsMaximal := comap_isMaximal_of_finiteType Q
  have hIwP : weakT (compFil hI hmax h𝔭 d) I d hId ≤
      Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)) :=
    Ideal.map_le_iff_le_comap.1 hIq
  obtain ⟨l, hl⟩ := exists_torsorY_not_mem_pt hI hmax h𝔭 hπ q
  have hIw0 : weakT (compFil hI hmax h𝔭 d) I d hId ≠ ⊥ :=
    weakT_ne_bot (compFil hI hmax h𝔭 d) hI d hId
  -- D3.8 (E4): the residue fields at the points below `q` are decided (`Pt.dec_local`)
  have hQrU := Pt.ker_comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)) q
  have hlW := weakT_eq_lspan (compFil hI hmax h𝔭 d) I hId lA hlA
  rcases q.mem_ker_dec (torsorS hI hmax h𝔭 hπ) with hsQ | hsQ
  · left
    refine ⟨hsQ, ?_⟩
    -- D3.8 (E2): the invariant at the point of `R` below `q` (`exists_invAt_semicont_ptL`, with the
    -- generators of the weak transform and the charts `hchartR`)
    have hQr0 : (q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d))
        (Torsor hI hmax h𝔭 d hπ))).ker =
        Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)) :=
      Pt.ker_comap _ q
    obtain ⟨w, hw0, -⟩ := exists_invAt_semicont_ptL hIw0 _
      (weakT_eq_lspan (compFil hI hmax h𝔭 d) I hId lA hlA) hchartR _ (by rw [hQr0]; exact hIwP)
    have hw' : InvAt (weakT (compFil hI hmax h𝔭 d) I d hId)
        (Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ))) w :=
      InvAt.congr_pt hQr0 hw0
    have hwU : InvAt (torsorI hI hmax h𝔭 hd hπ) Q w :=
      invAt_torsor_of_rees_pt (torsorY hI hmax h𝔭 d hπ) Q hl (Pt.dec_local_of_eq _ hQrU) q.dec_local
        _ hlW hIw0 hIwP hw'
    obtain rfl : v = w := hv.unique hwU
    -- `drop_pt` at the point of `R` below `q`
    have hQr : (q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ))).ker =
        Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)) :=
      Pt.ker_comap _ q
    have hcongr : ∀ {𝔪 𝔪' : Ideal (ReesAlg (compFil hI hmax h𝔭 d))} [𝔪.IsPrime] [𝔪'.IsPrime],
        𝔪 = 𝔪' → InvAt (weakT (compFil hI hmax h𝔭 d) I d hId) 𝔪 v →
        InvAt (weakT (compFil hI hmax h𝔭 d) I d hId) 𝔪' v := by
      intro _ _ _ _ h hv; subst h; exact hv
    exact drop_pt hI lA hlA hmax h𝔭 hN.exists_chart_away hd hw
      (hR4a := fun q' => rees_i4a_ptL hI lA hlA hmax h𝔭 hd hw hN.exists_chart_away q')
      (hR4b := hR4b) (hR4c := fun q' => Pt.formallySmooth_residueField q') hchartR _
      (by rw [hQr]; exact hIwP) (by rw [hQr]; exact hsQ) (genDeg_pos hI hmax h𝔭 d l)
      (genCoeff_mem hI hmax h𝔭 d hπ l) (by rw [hQr]; exact hl) (hcongr hQr.symm hw')
  · right
    have hk := Pt.ker_comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) q
    have hcomap : Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) =
        (Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ))).comap
          (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d))) := by
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    have hI𝔪 : I ≤ Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
      rw [← Ideal.map_le_iff_le_comap, torsor_map_eq hI hmax h𝔭 hd hπ]
      exact Ideal.mul_le_right.trans hIq
    refine ⟨hsQ, hI𝔪.trans hk.ge,
      fun h => torsor_not_le_of_s_not_mem_pt hI hmax h𝔭 hd hw hπ q hsQ (h.trans hk.le), ?_⟩
    obtain ⟨u, hu, -⟩ := exists_invAt_semicont_ptL hI lA hlA hchart
      (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))) (hI𝔪.trans hk.ge)
    have hu' := InvAt.congr_pt (hk.trans hcomap) hu
    have hI𝔪' : I ≤ (Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d))
        (Torsor hI hmax h𝔭 d hπ))).comap (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d))) :=
      hcomap ▸ hI𝔪
    have hR := invAt_rees_of_base_pt (compFil hI hmax h𝔭 d) hneg _ hsQ
      (Pt.dec_local_of_eq _ (hk.trans hcomap)) (Pt.dec_local_of_eq _ hQrU) lA hlA hI hI𝔪' hu'
    rw [map_eq_weakT _ hneg I d hId] at hR
    have hR' := InvAt.of_Iloc_eq (Iloc_span_unit_mul (s := reesS (compFil hI hmax h𝔭 d) hneg)
      (𝔪 := Q.comap (algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ))) hsQ d) hR
    have hwU : InvAt (torsorI hI hmax h𝔭 hd hπ) Q u :=
      invAt_torsor_of_rees_pt (torsorY hI hmax h𝔭 d hπ) Q hl (Pt.dec_local_of_eq _ hQrU) q.dec_local
        _ hlW hIw0 hIwP hR'
    obtain rfl : v = u := hv.unique hwU
    exact hu

end TorsorInvPt

end BezoutCounterexample.Principalization
