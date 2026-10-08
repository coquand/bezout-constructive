import BezoutCounterexample.Principalization.VertexPos
import BezoutCounterexample.Principalization.ReesVertexPtL
import BezoutCounterexample.Principalization.CRFGen

/-!
# The weak transform at the vertex, at a decided point (leaf; (B) step B6)

* `vertex_isInv_pos`: `vertex_isInv` through `vertex_invariant_pos` and `VLoc_polyIndNoeth_dec`;
* `I_le_compFil_gen`: `I_le_compFil` by `Iloc_le_cRF_one` (no `LocusComp.mem`, no `cRF_eq`);
* `Iloc_eq_lspan`: `I = (l)` gives `I A_𝔪 = (l/1)`;
* `VertexData.vertexG_data_pos`: `VertexData.vertexG_data` with the residue field of `A_𝔪` decided
  (`hdec𝔪`; at an explicit point: `Pt.dec_local`) and `I = (l)`. The weak transform in the
  statement is `weakT … (I_le_compFil_gen …)`, equal by proof irrelevance.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial Constructive

section Vertexp

variable {B : Type*} [CommRing B] [Algebra ℚ B] [IsLocalRing B] [Fact (Constructive.PolyIndNoeth B)]
  [IsDomain B]
  {n : ℕ} {e : Fin n → ℚ} {d : ℕ} {w : Fin n → ℕ} {Φ : WFil B}
  (he : ∀ i, 0 ≤ e i) (hanti : Antitone e) (hd : 0 < d) (hw : ∀ i, (w i : ℚ) = d * e i)

  (hpos : ∀ j : ℤ, 0 < j → Φ.F j ≤ maximalIdeal B)

include he hanti hd hw in
/-- **The invariant of the weak transform at the vertex.** -/
theorem vertex_isInv_pos (c₀ : Chart B n) (hc₀ : c₀.IsCentred)
    (hF₀ : ∀ m, Φ.F m = chartFil c₀ e d m) {k : ℕ} (hsupp : ∀ i, e i ≠ 0 ↔ (i : ℕ) < k)
    (hkn : k ≤ n) (I : Ideal B)
    (hdecB : ∀ x : B, x ∈ maximalIdeal B ∨ IsUnit x) (lI : List B) (hlI : I = lspan lI) (hI0 : I ≠ ⊥) (hId : I ≤ Φ.F d)
    (hmax : ∀ J' : MC B n, J'.Adm I → toLex e ≤ toLex J'.e) :
    ∃ (c' : Chart B n) (hF' : ∀ m, Φ.F m = chartFil c' e d m),
      IsInv (S := VLoc hpos) (weakV hpos I hId) (n + 1) (pad (n + 1) e) ∧
      (vChart he hd hw hpos c' hF').IsCentred ∧
      weakV hpos I hId ≤ (vChart he hd hw hpos c' hF').RF (pad (n + 1) e) 1 := by
  have := VLoc_polyIndNoeth_dec hpos c₀ hF₀ he hd hw
  obtain ⟨c', hc', hF', hSA⟩ := vertex_invariant_pos he hanti hd hw hpos c₀ hc₀ hF₀ hsupp hkn I hdecB lI hlI hI0 hId hmax
  have hadm : weakV hpos I hId ≤ (vChart he hd hw hpos c' hF').RF (pad (n + 1) e) 1 := by
    rw [vChart, Chart.localization_RF]
    exact Ideal.map_mono (weak_le_reesRF he hd hw c' hF' I hId)
  exact ⟨c', hF', hSA.isInv hadm, vChart_isCentred he hd hw hpos c' hF' hc', hadm⟩

end Vertexp

lemma Iloc_eq_lspan {A : Type} [CommRing A] [Algebra ℚ A] (I : Ideal A) (𝔪 : Ideal A) [𝔪.IsPrime]
    (l : List A) (hl : I = lspan l) :
    Iloc I 𝔪 = lspan (l.map (algebraMap A (Localization.AtPrime 𝔪))) := by
  rw [Iloc, hl, lspan, Ideal.map_span, lspan]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map]

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} {hI : I ≠ ⊥} {v₀ : ℕ → ℚ}
  {hmax : IsMaxInvPt I v₀}
  {𝔭 : Ideal A} {h𝔭 : LocusComp I v₀ 𝔭} {d : ℕ} (hd : 0 < d)

omit [IsNoetherianRing A] in
/-- `I_le_compFil` without `LocusComp.mem`/`cRF_eq`. -/
lemma I_le_compFil_gen (hI : I ≠ ⊥)
    (hmax : IsMaxInvPt I v₀)
    (h𝔭 : LocusComp I v₀ 𝔭) (hd : 0 < d) : I ≤ (compFil hI hmax h𝔭 d).F d := by
  intro f hf
  rw [compFil_F, mem_compFPt]
  intro p _
  rw [show ((d : ℤ) : ℚ) / d = 1 by push_cast; exact div_self (by exact_mod_cast hd.ne')]
  exact Iloc_le_cRF_one I p.ker (Ideal.mem_map_of_mem _ hf)


set_option maxHeartbeats 800000 in
/-- **The weak transform at the global vertex.** -/
theorem VertexData.vertexG_data_pos {𝔪 : Ideal A} [𝔪.IsMaximal]
    (D : VertexData hI hmax h𝔭 (d := d) (v₀ := v₀) 𝔪)
    (hdec𝔪 : ∀ x : Localization.AtPrime 𝔪, x ∈ maximalIdeal _ ∨ IsUnit x) (l : List A) (hl : I = lspan l) :
    ∃ J₀ : MC (Localization.AtPrime (vertexG (compFil hI hmax h𝔭 d) 𝔪 (D.hpos hd))) (D.n + 1),
      J₀.Adm (Iloc (weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil_gen hI hmax h𝔭 hd))
        (vertexG (compFil hI hmax h𝔭 d) 𝔪 (D.hpos hd))) ∧
      J₀.e = pad (D.n + 1) D.J.e ∧
      IsInv (Iloc (weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil_gen hI hmax h𝔭 hd))
        (vertexG (compFil hI hmax h𝔭 d) 𝔪 (D.hpos hd))) (D.n + 1) J₀.e ∧
      ∀ (j : ℤ), 1 ≤ j → ∀ (f : A) (hf : f ∈ (compFil hI hmax h𝔭 d).F j),
        algebraMap (ReesAlg (compFil hI hmax h𝔭 d))
          (Localization.AtPrime (vertexG (compFil hI hmax h𝔭 d) 𝔪 (D.hpos hd)))
          ⟨LaurentPolynomial.C f * T j, C_mul_T_mem_ReesAlg hf⟩ ∈ J₀.RF (1 / d) := by
  set Φ := compFil hI hmax h𝔭 d
  set R := ReesAlg Φ
  set hpos := D.hpos hd
  set P₀ := vertexG Φ 𝔪 hpos
  set hId := I_le_compFil_gen hI hmax h𝔭 hd
  have hIdm : Iloc I 𝔪 ≤ (Φ.loc (Localization.AtPrime 𝔪)).F d := Ideal.map_mono hId
  have : IsNoetherianRing (Localization.AtPrime 𝔪) := inferInstance
  obtain ⟨c', hF', hinvV, hcentV, hadmV⟩ := vertex_isInv_pos D.J.nonneg D.J.anti hd D.hwe hpos D.J.c
    D.J.centred D.hF D.hsupp D.hkn (Iloc I 𝔪) hdec𝔪 _ (Iloc_eq_lspan I 𝔪 l hl) (Iloc_ne_bot hI 𝔪) hIdm D.hinv.2
  let := reesAlgLoc Φ 𝔪
  have : IsLocalization.AtPrime (VLoc hpos) P₀ := isLocalization_VLoc Φ 𝔪 hpos
  let eV : Localization.AtPrime P₀ ≃ₐ[R] VLoc hpos :=
    IsLocalization.algEquiv P₀.primeCompl (Localization.AtPrime P₀) (VLoc hpos)
  let eq : VLoc hpos ≃+* Localization.AtPrime P₀ := eV.symm.toRingEquiv
  have heq : ∀ x : R, eq (algebraMap R (VLoc hpos) x) = algebraMap R (Localization.AtPrime P₀) x :=
    fun x => eV.symm.commutes x
  have hVR : ∀ x : R, algebraMap (ReesAlg (Φ.loc (Localization.AtPrime 𝔪))) (VLoc hpos)
      (reesMap Φ (Localization.AtPrime 𝔪) x) = algebraMap R (VLoc hpos) x := fun x => rfl
  -- the weak transforms correspond
  have hweak : (weakV hpos (Iloc I 𝔪) hIdm).map eq =
      Iloc (weakT Φ I d hId) P₀ := by
    show (weakV hpos (Iloc I 𝔪) hIdm).map (eq : VLoc hpos →+* Localization.AtPrime P₀) = _
    rw [weakV, ← weakT_map_eq Φ 𝔪 I d hId, Ideal.map_map, Ideal.map_map]
    congr 1
    ext x
    simp only [RingHom.comp_apply]
    rw [show (reesMap Φ (Localization.AtPrime 𝔪)) x = algebraMap R _ x from rfl]
    exact heq x
  set JV : MC (VLoc hpos) (D.n + 1) := ⟨vChart D.J.nonneg hd D.hwe hpos c' hF', pad (D.n + 1) D.J.e,
    hcentV, pad_nonneg' D.J.e D.J.nonneg, pad_antitone' D.J.nonneg D.J.anti⟩
  refine ⟨JV.mapRingEquiv (S' := Localization.AtPrime P₀) eq, ?_, rfl, ?_, ?_⟩
  · have := MC.Adm.mapRingEquiv (S' := Localization.AtPrime P₀) (J := JV) hadmV eq
    rwa [hweak] at this
  · have := IsInv.mapRingEquiv (S' := Localization.AtPrime P₀) hinvV eq
    rwa [hweak] at this
  · intro j hj f hf
    have h1 : (⟨LaurentPolynomial.C (algebraMap A (Localization.AtPrime 𝔪) f) * T j,
        C_mul_T_mem_ReesAlg (Ideal.mem_map_of_mem _ hf)⟩ :
          ReesAlg (Φ.loc (Localization.AtPrime 𝔪))) ∈
        (reesChart c' hF' D.J.nonneg hd D.hwe).RF (pad (D.n + 1) D.J.e) (1 / d) :=
      homog_mem_reesRF c' hF' D.J.nonneg hd D.hwe hj (Ideal.mem_map_of_mem _ hf)
    have h2 := Ideal.mem_map_of_mem (algebraMap (ReesAlg (Φ.loc (Localization.AtPrime 𝔪)))
      (VLoc hpos)) h1
    have hloc := Chart.localization_RF (S := VLoc hpos) (vertex hpos).primeCompl
      (reesChart c' hF' D.J.nonneg hd D.hwe) (pad (D.n + 1) D.J.e) (1 / d)
    rw [← hloc] at h2
    have h3 := Ideal.mem_map_of_mem eq h2
    rw [MC.mapRingEquiv_RF (S' := Localization.AtPrime P₀) (J := JV)]
    have hy : algebraMap R (Localization.AtPrime P₀) ⟨LaurentPolynomial.C f * T j,
        C_mul_T_mem_ReesAlg hf⟩ = eq (algebraMap (ReesAlg (Φ.loc (Localization.AtPrime 𝔪)))
          (VLoc hpos) ⟨LaurentPolynomial.C (algebraMap A (Localization.AtPrime 𝔪) f) * T j,
            C_mul_T_mem_ReesAlg (Ideal.mem_map_of_mem _ hf)⟩) := by
      rw [← heq, ← hVR]
      congr 2
      apply Subtype.ext
      rw [reesMap_coe]
      exact lmap_C_mul_T _ _ _
    rw [hy]
    exact h3

end BezoutCounterexample.Principalization
