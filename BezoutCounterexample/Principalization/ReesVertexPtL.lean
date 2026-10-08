import BezoutCounterexample.Principalization.ReesVertex
import BezoutCounterexample.Principalization.ComponentFilPtL
import BezoutCounterexample.Principalization.CompFilGenPtL

/-!
# Vertex data at an explicit point from `LocDataPt` (leaf)

`VertexData.nonempty_pt` (ReesVertex) still uses `LocusComp.mem` (classical locus), `cRF_eq`
(`MC.exists_max_FT`) and `IsInv.exists_run` (with `residueField_isIntegral`). Here everything is
read off local data at the point (`LocDataPt.nonempty`):

* the centre `J` is the witness of `D.inv`, its weights are `D.ek`;
* `k := min D.k D.n` (`D.supp`), so no run is needed;
* `hF` by R3 (`compFil_loc_F_ptL`, over a `ChartCoverPtL`; an input `hR3` of `ofLocDataPt`) and
  `cRF_eq_of_rf` with `D.rf` (no maximal centre).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l)
  {dim : ℕ}
  (hchartn : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) dim))
  {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

/-- `VertexData` at an explicit point from local data at that point. -/
def VertexData.ofLocDataPt [Fact (Constructive.HasPres A)] (q : Pt A) (h𝔭q : 𝔭 ≤ q.ker)
    (D : LocDataPt I v₀ q.ker) (J : MC (Localization.AtPrime q.ker) D.n)
    (hJ : J.Adm (Iloc I q.ker)) (hJe : J.e = D.ek) (w : Fin D.n → ℕ)
    (hwe : ∀ i, (w i : ℚ) = d * J.e i)
    (hR3 : ∀ m : ℤ, ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime q.ker)).F m =
      cRF I q.ker ((m : ℚ) / d)) :
    VertexData hI hmax h𝔭 (d := d) (v₀ := v₀) q.ker where
  n := D.n
  J := J
  w := w
  k := min D.k D.n
  hwe := hwe
  hadm := hJ
  hinv := by
    obtain ⟨-, hmin⟩ := D.inv
    exact ⟨⟨J, hJ, rfl⟩, by rw [hJe]; exact hmin⟩
  hev := by rw [hJe]; exact D.hv
  hsupp i := by rw [hJe, D.supp, lt_min_iff]; exact ⟨fun h => ⟨h, i.2⟩, fun h => h.1⟩
  hkn := min_le_right _ _
  hF m := by
    rw [hR3 m]
    have hinv : IsInv (Iloc I q.ker) D.n D.ek := D.inv
    rw [cRF_eq_of_rf hinv fun J' hJ' hJ'e =>
      (D.rf q D.hg J' hJ' hJ'e _).trans (D.rf q D.hg J hJ hJe _).symm]
    rfl

include hl hchartn hw in
/-- **`VertexData` at an explicit point**, without `LocusComp.mem`, `cRF_eq` or a run
(twin of `VertexData.nonempty_pt`). -/
lemma VertexData.nonempty_ptL [Fact (Constructive.HasPres A)] (q : Pt A) (h𝔭q : 𝔭 ≤ q.ker) :
    Nonempty (VertexData hI hmax h𝔭 (d := d) (v₀ := v₀) q.ker) := by
  have hchart := LocusComp.hchart_of_dim hI l hl hmax h𝔭 hchartn
  obtain ⟨hIq, hv⟩ := h𝔭.mem_ptL hI l hl hchart hmax q h𝔭q
  obtain ⟨f₀, hf₀, n₀, ⟨c₀⟩⟩ := hchart q
  obtain ⟨D⟩ := LocDataPt.nonempty hI l hl q hIq hv hf₀ c₀
  obtain ⟨⟨J, hJ, hJe⟩, -⟩ := D.inv
  have hw' : ∀ i : Fin D.n, ∃ w : ℕ, (w : ℚ) = d * J.e i := fun i => by
    obtain ⟨w, hw⟩ := hw i
    have hv0 : v₀ i = D.ek i := by
      have := congrFun D.hv (i : ℕ); rw [ext0_apply] at this; exact this.symm
    exact ⟨w, by rw [hw, hv0, hJe]⟩
  obtain ⟨w, hwe⟩ := Constructive.finite_choice_dep hw'
  exact ⟨VertexData.ofLocDataPt hI hmax h𝔭 q h𝔭q D J hJ hJe w hwe
    (compFil_loc_F_ptL hI l hl hmax h𝔭 hchartn d q h𝔭q)⟩

end BezoutCounterexample.Principalization
