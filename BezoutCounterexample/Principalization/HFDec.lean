import BezoutCounterexample.Principalization.ChartCover
import BezoutCounterexample.Principalization.ReesPres

/-!
# Deciding membership in the filtration from a chart cover

`compF_dec_of_cover`: for a presented `A` and a chart cover of the component (`ChartCover`,
`Principalization/ChartCover.lean`), membership in `F_t(𝔭)` is decidable: by
`mem_compF_iff_list` it is membership of `x/1` in explicit finitely generated ideals of the
`A[1/gₖ]`, which are presented (`HasPres.away`), hence decided by Gröbner bases.

`hF_of_cover`, `torsor_dec_cover`: all decisions of the torsor `U` (gcds, zero test, divisibility)
from those of `A` and its presentation. Since D3.3d the filtration is the one at points, whose steps
have explicit generators (R2), so no chart cover is needed; `compF_dec_of_cover` is kept for the
classical filtration.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} {𝔭 : Ideal A}

include hI in
/-- **Membership in `F_t` is decidable** given a presentation and a chart cover. -/
theorem compF_dec_of_cover (hZ : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 → I ≤ 𝔪 ∧ InvAt I 𝔪 v₀)
    (hA : HasPres A) (C : ChartCover I v₀ 𝔭) (t : ℚ) (x : A) :
    x ∈ compF I 𝔭 t ∨ x ∉ compF I 𝔭 t := by
  haveI : Fact (HasPres A) := ⟨hA⟩
  obtain ⟨L, hL⟩ := mem_compF_iff_list hI hZ C t
  rw [hL]
  rcases fin_forall_or_exists (A := fun k => algebraMap A (Localization.Away (C.D k).g) x ∈ lspan (L k))
      (B := fun k => algebraMap A (Localization.Away (C.D k).g) x ∉ lspan (L k))
      (fun k => (hA.away (C.D k).g (Localization.Away (C.D k).g)).mem_dec (L k) _) with h | ⟨k, hk⟩
  · exact Or.inl h
  · exact Or.inr fun h => hk (h k)

variable (hmax : IsMaxInvPt I v₀)
  (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hmax h𝔭 in
/-- **Membership in the filtration `F_j` of the Rees algebra is decidable**: the steps have
explicit generators (R2, `LocusComp.exists_lspan_compFPt`), so (G) decides (D3.3d; no chart cover
argument). -/
theorem hF_of_cover (hA : HasPres A) :
    ∀ (j : ℤ) (g : A), g ∈ (compFil hI hmax h𝔭 d).F j ∨ g ∉ (compFil hI hmax h𝔭 d).F j := by
  haveI : Fact (HasPres A) := ⟨hA⟩
  intro j g
  obtain ⟨l, hl⟩ := h𝔭.exists_lspan_compFPtP hI hmax ((j : ℚ) / d)
  rw [compFil_F, hl]
  exact hA.mem_dec l g

include hmax h𝔭 hd hw in
/-- **The torsor with all decisions computed** from `A` and a chart cover of the component. -/
theorem torsor_dec_cover [Fact (Constructive.HasPres A)] [Constructive.Enum A] [Fact (∃ k, ChartDim A k)] (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) (hdA : DvdDec A)
    (hA : HasPres A) (hk2 : v₀ 1 ≠ 0) {π : A}
    (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1) (hπ0 : π ≠ 0) :
    HasGcd (Torsor hI hmax h𝔭 d hπ) ∧ (∀ x : Torsor hI hmax h𝔭 d hπ, x = 0 ∨ x ≠ 0) ∧
      DvdDec (Torsor hI hmax h𝔭 d hπ) :=
  haveI : Fact (HasPres A) := ⟨hA⟩
  torsor_dec_F hI hmax h𝔭 hd hw hπ hG hz hdA hk2 hπ0 (hF_of_cover hI hmax h𝔭 hA)

end BezoutCounterexample.Principalization
