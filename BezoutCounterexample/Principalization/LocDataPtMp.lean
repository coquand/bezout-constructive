import BezoutCounterexample.Principalization.MaxInvPt0
import BezoutCounterexample.Principalization.LocDataPtProd

/-!
# The maximal locus at points, with `IsMaxInvPt` (leaf, for the top-chain switch)

`mem_locusPt_of_le_ptL` and `LocusComp.mem_ptL` (LocDataPtProd) with `hmaxPt : IsMaxInvPt I v₀`
in place of the maximal-ideal `hmax`, argument order unchanged. The proofs use `hmax` only at the
explicit point `p`, so they are the same.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l)
  (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
  {v₀ : ℕ → ℚ} (hmaxPt : IsMaxInvPt I v₀)
include hI hl hchart hmaxPt

/-- `mem_locusPt_of_le_ptL` with `IsMaxInvPt`. -/
theorem mem_locusPt_of_le_ptL_mp {N : ℕ}
    (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0)
    (hb₀ : ∀ i, N ≤ i → v₀ i = 0) (p : Pt A) (hle : locusPt I v₀ ≤ p.ker) :
    I ≤ p.ker ∧ InvAt I p.ker v₀ := by
  have hIp : I ≤ p.ker := (le_locusPt I v₀).trans hle
  refine ⟨hIp, ?_⟩
  obtain ⟨v, hv, g, hg, hgv⟩ := exists_invAt_semicont_ptL hI l hl hchart p hIp
  rcases eq_or_ne_bounded (hbd _ _ hv) hb₀ with heq | hne
  · exact heq ▸ hv
  · exfalso
    have hlt : toLex v₀ < toLex v := lt_of_le_of_ne (hmaxPt p hIp v hv)
      (fun h => hne (toLex.injective h).symm)
    refine hg (hle fun q _ hvq => ?_)
    rcases q.mem_ker_dec g with h | h
    · exact h
    · exact absurd (hgv q h v₀ hvq) (not_le.2 hlt)

/-- `LocusComp.mem_ptL` with `IsMaxInvPt`. -/
theorem LocusComp.mem_ptL_mp {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (p : Pt A) (h : 𝔭 ≤ p.ker) :
    I ≤ p.ker ∧ InvAt I p.ker v₀ := by
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  exact mem_locusPt_of_le_ptL_mp hI l hl hchart hmaxPt hbd hb₀ p (h𝔭.le.trans h)

end BezoutCounterexample.Principalization
