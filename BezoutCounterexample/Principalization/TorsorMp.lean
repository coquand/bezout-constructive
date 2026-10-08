import BezoutCounterexample.Principalization.TorsorPt
import BezoutCounterexample.Principalization.TorsorInvPt
import BezoutCounterexample.Principalization.MaxInvPt0
import BezoutCounterexample.Principalization.LocDataPtMp

/-!
# The torsor step at points with `IsMaxInvPt` (leaf, for the top-chain switch)

`torsor_inv_ge` (TorsorInv) is the only torsor lemma that applies `hmax` itself (at the contraction
of a maximal ideal of `U`); `torsor_locus_down`/`_up` and `torsor_decrease_pt` (TorsorPt) reach the
engine through the classical `torsor_invAt`. Here all four are stated at explicit points of `U`,
through `torsor_invAt_pt` (TorsorInvPt), with `hmaxPt : IsMaxInvPt I v₀` for the comparison:

* `torsor_inv_ge_mp`, `torsor_locus_down_mp`, `torsor_locus_up_mp`;
* the counting chain `torsor_map_locusPt_le_mp`, `torsor_locusPt_le_map_mp`,
  `torsor_mem_locusPt_of_forall_mp`, `torsor_count_pt_mp` (TorsorPt, through the two above);
* `torsor_decrease_pt_mp`.

`hmax` (maximal-ideal form) is still a binder, but only to type `compFil`/`Torsor` and to call
`torsor_invAt_pt`; at the switch (`hmax := hmaxPt`) the two coincide. Extra inputs: those of
`torsor_invAt_pt` (`lA`, `hlA`, `hchart`, `hN`, `hR4b`, `hchartR`); `torsor_locus_up_mp` takes the
existence of invariants at points of `U` (`hexU`, from `exists_invAt_semicont_ptL` on `U`) instead
of the classical `exists_invAt`; `torsor_decrease_pt_mp` takes the attainment of `v₁` at an explicit
point (`hq₁`) instead of `IsMaxInv`. Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

section TorsorMp

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] [hpA : Fact (HasPres A)]

variable [Fact (Constructive.HasPres A)] [Constructive.Enum A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  (hmaxPt : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  (hπ0 : π ≠ 0)
  (lA : List A) (hlA : I = lspan lA)
  (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
  {dim : ℕ} (hN : ChartDim A dim)
  (hR4b : ∀ q : Pt (ReesAlg (compFil hI hmax h𝔭 d)),
    Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker))
  (hchartR : ∀ p : Pt (ReesAlg (compFil hI hmax h𝔭 d)), ∃ f, f ∉ p.ker ∧ ∃ n : ℕ,
    Nonempty (Chart (Localization.Away f) n))
  (hexU : ∀ q : Pt (Torsor hI hmax h𝔭 d hπ), torsorI hI hmax h𝔭 hd hπ ≤ q.ker →
    ∃ v, InvAt (torsorI hI hmax h𝔭 hd hπ) q.ker v)

include hd hw hπ0 hmaxPt lA hlA hchart hN hR4b hchartR in
/-- **`torsor_inv_ge` at an explicit point of `U`.** -/
theorem torsor_inv_ge_mp (q : Pt (Torsor hI hmax h𝔭 d hπ))
    (hIq : torsorI hI hmax h𝔭 hd hπ ≤ q.ker) {v : ℕ → ℚ}
    (hv : InvAt (torsorI hI hmax h𝔭 hd hπ) q.ker v) : toLex v₀ ≤ toLex v := by
  rcases torsor_invAt_pt hI hmax h𝔭 hd hw hπ hπ0 lA hlA hchart hN hR4b hchartR q hIq hv with
    ⟨-, hlt⟩ | ⟨-, hI', -, hv'⟩
  · exact hlt.le
  · exact hmaxPt _ hI' v hv'

include hd hw hπ0 lA hlA hchart hN hR4b hchartR in
/-- **`torsor_locus_down` at points**, through `torsor_invAt_pt`. -/
theorem torsor_locus_down_mp (q : Pt (Torsor hI hmax h𝔭 d hπ))
    (hIq : torsorI hI hmax h𝔭 hd hπ ≤ q.ker) (hv : InvAt (torsorI hI hmax h𝔭 hd hπ) q.ker v₀) :
    torsorS hI hmax h𝔭 hπ ∉ q.ker ∧
      I ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker ∧
      ¬ 𝔭 ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker ∧
      InvAt I (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker v₀ := by
  rcases torsor_invAt_pt hI hmax h𝔭 hd hw hπ hπ0 lA hlA hchart hN hR4b hchartR q hIq hv with
    ⟨-, hlt⟩ | h
  · exact absurd hlt (lt_irrefl _)
  · exact h

include hd hw hπ0 lA hlA hchart hN hR4b hchartR hexU in
/-- **`torsor_locus_up` at points**: the invariant at `q` comes from `hexU`. -/
theorem torsor_locus_up_mp (q : Pt (Torsor hI hmax h𝔭 d hπ)) (hs : torsorS hI hmax h𝔭 hπ ∉ q.ker)
    (hIq : I ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker)
    (hv : InvAt I (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker v₀) :
    torsorI hI hmax h𝔭 hd hπ ≤ q.ker ∧ InvAt (torsorI hI hmax h𝔭 hd hπ) q.ker v₀ := by
  have hP := q.ker_isMaximal.isPrime
  have hle : torsorI hI hmax h𝔭 hd hπ ≤ q.ker := by
    have h1 : I.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) ≤ q.ker :=
      Ideal.map_le_iff_le_comap.2
        (hIq.trans (Pt.ker_comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) q).le)
    rw [torsor_map_eq hI hmax h𝔭 hd hπ] at h1
    intro f hf
    rcases hP.mem_or_mem (h1 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hf)) with h | h
    · exact absurd (hP.mem_of_pow_mem d h) hs
    · exact h
  refine ⟨hle, ?_⟩
  obtain ⟨v, hv'⟩ := hexU q hle
  rcases torsor_invAt_pt hI hmax h𝔭 hd hw hπ hπ0 lA hlA hchart hN hR4b hchartR q hle hv' with
    ⟨hs', -⟩ | ⟨-, -, -, hv''⟩
  · exact absurd hs' hs
  · obtain rfl : v = v₀ := hv''.unique hv
    exact hv'

include hd hw hπ0 hmaxPt lA hlA hchart hN hR4b hchartR hexU in
/-- The old locus ideal maps into the new one. -/
theorem torsor_map_locusPt_le_mp [Fact (∃ k, ChartDim A k)] :
    (locusPt I v₀).map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) ≤
      locusPt (torsorI hI hmax h𝔭 hd hπ) v₀ := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx q hIq hv
  obtain ⟨-, hI', -, hv'⟩ := torsor_locus_down_mp hI hmax h𝔭 hd hw hπ hπ0 lA hlA hchart hN hR4b hchartR q hIq hv
  have := hx _ hI' hv'
  rw [Pt.ker_comap] at this
  exact this


include hd hw hπ0 hmaxPt lA hlA hchart hN hR4b hchartR hexU in
/-- **The new locus lies in `𝔭' U`** for every other component `𝔭'`: at a point of `V(𝔭' U)`
off `s · y` (`exists_pt_away` on the presented torsor), `y` would vanish. -/
theorem torsor_locusPt_le_map_mp [Fact (∃ k, ChartDim A k)] {𝔭' : Ideal A} (h𝔭' : LocusComp I v₀ 𝔭') (hne : 𝔭 ≠ 𝔭') :
    locusPt (torsorI hI hmax h𝔭 hd hπ) v₀ ≤ 𝔭'.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
  have hU : HasPres (Torsor hI hmax h𝔭 d hπ) := hasPres_torsor hI hmax h𝔭 hd hw hpA.out hπ
  have hP := torsor_comp_isPrime_pt hI hmax h𝔭 hd hw hπ h𝔭' hne
  have hs := torsor_s_not_mem_map hI hmax h𝔭 hd hw hπ h𝔭' hne
  obtain ⟨C, hC, -⟩ := h𝔭'.gens
  have hCU : 𝔭'.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) =
      lspan (C.map (algebraMap A (Torsor hI hmax h𝔭 d hπ))) := by
    rw [lspan_map, hC]
  intro y hy
  rcases (HasPres.mem_dec hU) (C.map (algebraMap A (Torsor hI hmax h𝔭 d hπ))) y with h | h
  · exact hCU ▸ h
  · exfalso
    rw [← hCU] at h
    have hsy : ∀ k : ℕ, (torsorS hI hmax h𝔭 hπ * y) ^ k ∉
        lspan (C.map (algebraMap A (Torsor hI hmax h𝔭 d hπ))) := fun k hk =>
      (hP.mem_or_mem (hP.mem_of_pow_mem k (hCU ▸ hk))).elim hs h
    obtain ⟨q, hq, hqy⟩ := (HasPres.exists_pt_away hU) _ _ hsy
    rw [← hCU] at hq
    have hp : 𝔭' ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker := by
      rw [Pt.ker_comap]; exact Ideal.map_le_iff_le_comap.1 hq
    obtain ⟨hIp, hv⟩ := LocusComp.mem_ptL_mp hI lA hlA hchart hmaxPt h𝔭' _ hp
    have hsq : torsorS hI hmax h𝔭 hπ ∉ q.ker := fun h' => hqy (Ideal.mul_mem_right _ _ h')
    obtain ⟨h₁, hv₁⟩ := torsor_locus_up_mp hI hmax h𝔭 hd hw hπ hπ0 lA hlA hchart hN hR4b hchartR hexU q hsq hIp hv
    exact hqy (Ideal.mul_mem_left _ _ (hy q h₁ hv₁))


include hd hw hπ0 hmaxPt lA hlA hchart hN hR4b hchartR hexU in
/-- **`⋂_{𝔭' ≠ 𝔭} 𝔭' U` lies in the new locus**: a point of the new locus lies over a point of the
old locus off `𝔭`, hence above some other component. -/
theorem torsor_mem_locusPt_of_forall_mp [Fact (∃ k, ChartDim A k)] {Pg : List A} (hPg : locusPt I v₀ = lspan Pg)
    {Cs : List (List A)} (hC : IsCompList Pg Cs) {y : Torsor hI hmax h𝔭 d hπ}
    (hy : ∀ C ∈ Cs, lspan C ≠ 𝔭 → y ∈ (lspan C).map (algebraMap A (Torsor hI hmax h𝔭 d hπ))) :
    y ∈ locusPt (torsorI hI hmax h𝔭 hd hπ) v₀ := by
  intro q hIq hv
  obtain ⟨-, hI', h𝔭q, hv'⟩ := torsor_locus_down_mp hI hmax h𝔭 hd hw hπ hπ0 lA hlA hchart hN hR4b hchartR q hIq hv
  have hL : lspan Pg ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker :=
    hPg ▸ fun f hf => hf _ hI' hv'
  obtain ⟨C, hCm, hCq⟩ := hC.exists_le (Pt.ker_isMaximal _).isPrime hL
  have hne : lspan C ≠ 𝔭 := fun h' => h𝔭q (h' ▸ hCq)
  have := hy C hCm hne
  rw [Pt.ker_comap] at hCq
  exact Ideal.map_le_iff_le_comap.2 hCq this


include hd hw hπ0 hmaxPt lA hlA hchart hN hR4b hchartR hexU in
/-- **The number of components drops on the torsor** (the `NumComp` form of `torsor_count`). -/
theorem torsor_count_pt_mp [Fact (∃ k, ChartDim A k)] {Pg : List A} (hPg : locusPt I v₀ = lspan Pg)
    {Pg₁ : List (Torsor hI hmax h𝔭 d hπ)}
    (hPg₁ : locusPt (torsorI hI hmax h𝔭 hd hπ) v₀ = lspan Pg₁) {k k₁ : ℕ} (hk : NumComp Pg k)
    (hk₁ : NumComp Pg₁ k₁) : k₁ < k := by
  have hU : HasPres (Torsor hI hmax h𝔭 d hπ) := hasPres_torsor hI hmax h𝔭 hd hw hpA.out hπ
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  obtain ⟨Cs, hC, rfl⟩ := hk
  obtain ⟨Ds, hD, rfl⟩ := hk₁
  obtain ⟨G, hG, -⟩ := h𝔭.gens
  have hgood : ∀ C : List A, lspan C ≠ 𝔭 ∨ ¬ lspan C ≠ 𝔭 := fun C => by
    rcases (HasPres.le_dec hpA.out) C G with h1 | h1
    · rcases (HasPres.le_dec hpA.out) G C with h2 | h2
      · exact Or.inr fun h' => h' (hG ▸ le_antisymm h1 h2)
      · exact Or.inl fun h' => h2 (hG ▸ h' ▸ le_rfl)
    · exact Or.inl fun h' => h1 (hG ▸ h' ▸ le_rfl)
  have hcomp : ∀ C ∈ Cs, LocusComp I v₀ (lspan C) := fun C hCm =>
    hC.locusComp hPg hbd hb₀ h𝔭.gensI h𝔭.chartn hCm
  -- each component of `I₁` is `𝔭' U` for another component `𝔭'` of `I`
  have hmap : ∀ D ∈ Ds, ∃ C ∈ Cs, lspan C ≠ 𝔭 ∧
      lspan D = (lspan C).map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
    intro D hDm
    have hDp := hD.isPrime hDm
    obtain ⟨C, hCm, hCg, hCD⟩ := exists_le_of_forall_mem hU hDp (fun C => lspan C ≠ 𝔭) hgood
      (fun C => C.map (algebraMap A (Torsor hI hmax h𝔭 d hπ))) Cs fun y hy =>
        hD.le D hDm (hPg₁ ▸ torsor_mem_locusPt_of_forall_mp hI hmax hmaxPt h𝔭 hd hw hπ hπ0 lA hlA hchart hN hR4b hchartR hexU hPg hC
          fun C hCm hCg => lspan_map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) C ▸ hy C hCm hCg)
    rw [lspan_map] at hCD
    have hne : 𝔭 ≠ lspan C := fun h' => hCg h'.symm
    have hle : lspan Pg₁ ≤ (lspan C).map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) :=
      hPg₁ ▸ torsor_locusPt_le_map_mp hI hmax hmaxPt h𝔭 hd hw hπ hπ0 lA hlA hchart hN hR4b hchartR hexU (hcomp C hCm) hne
    exact ⟨C, hCm, hCg, (hD.minimal D hDm _ (torsor_comp_isPrime_pt hI hmax h𝔭 hd hw hπ
      (hcomp C hCm) hne) hle hCD).symm⟩
  -- `𝔭` is a component of `I`
  obtain ⟨C₀, hC₀m, hC₀⟩ := hC.exists_eq_of_mem_minimalPrimes (hPg ▸ h𝔭.min)
  have hsub : 𝔭.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) :: Ds.map lspan ⊆
      Cs.map fun C => (lspan C).map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
    intro P hP
    rcases List.mem_cons.1 hP with rfl | hP
    · exact List.mem_map.2 ⟨C₀, hC₀m, by rw [hC₀]⟩
    · obtain ⟨D, hDm, rfl⟩ := List.mem_map.1 hP
      obtain ⟨C, hCm, -, hDC⟩ := hmap D hDm
      exact List.mem_map.2 ⟨C, hCm, hDC.symm⟩
  have hnd : (𝔭.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) :: Ds.map lspan).Nodup := by
    refine List.nodup_cons.2 ⟨fun h' => ?_, hD.nodup_map⟩
    obtain ⟨D, hDm, hD𝔭⟩ := List.mem_map.1 h'
    obtain ⟨C, hCm, hCg, hDC⟩ := hmap D hDm
    have hne : 𝔭 ≠ lspan C := fun h'' => hCg h''.symm
    have h2 := torsor_map_sup_eq_top hI hmax h𝔭 hd hw hπ (hcomp C hCm) hne
    rw [← hD𝔭, hDC, sup_idem] at h2
    exact (torsor_comp_isPrime_pt hI hmax h𝔭 hd hw hπ (hcomp C hCm) hne).ne_top h2
  have := hnd.length_le_of_subset hsub
  rw [List.length_cons, List.length_map, List.length_map] at this
  omega


include hd hw hπ0 hmaxPt lA hlA hchart hN hR4b hchartR hexU in
/-- **Lemma 4.3 at points** with `IsMaxInvPt` and the attainment of `v₁` at an explicit point. -/
theorem torsor_decrease_pt_mp [Fact (∃ k, ChartDim A k)] {v₁ : ℕ → ℚ}
    (hq₁ : ∃ q : Pt (Torsor hI hmax h𝔭 d hπ), torsorI hI hmax h𝔭 hd hπ ≤ q.ker ∧
      InvAt (torsorI hI hmax h𝔭 hd hπ) q.ker v₁)
    {Pg : List A} (hPg : locusPt I v₀ = lspan Pg) {Pg₁ : List (Torsor hI hmax h𝔭 d hπ)}
    (hPg₁ : locusPt (torsorI hI hmax h𝔭 hd hπ) v₁ = lspan Pg₁) {k k₁ : ℕ} (hk : NumComp Pg k)
    (hk₁ : NumComp Pg₁ k₁) : v₁ ≺ v₀ ∨ (v₁ = v₀ ∧ k₁ < k) := by
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  obtain ⟨q₁, hI₁, hv₁⟩ := hq₁
  have hle : v₁ ⪯ v₀ :=
    torsor_inv_ge_mp hI hmax hmaxPt h𝔭 hd hw hπ hπ0 lA hlA hchart hN hR4b hchartR q₁ hI₁ hv₁
  rcases torsor_invAt_pt hI hmax h𝔭 hd hw hπ hπ0 lA hlA hchart hN hR4b hchartR q₁ hI₁ hv₁ with
    ⟨-, hlt⟩ | ⟨-, -, -, hv'⟩
  · exact Or.inl ⟨hle, fun h => (lt_irrefl _) (h ▸ hlt)⟩
  · rcases weight_le_dec (hbd _ v₁ hv') hb₀ hle with h | rfl
    · exact Or.inl h
    · exact Or.inr ⟨rfl, torsor_count_pt_mp hI hmax hmaxPt h𝔭 hd hw hπ hπ0 lA hlA hchart hN hR4b hchartR hexU hPg hPg₁ hk hk₁⟩

end TorsorMp

end BezoutCounterexample.Principalization
