import BezoutCounterexample.Divisorial
import BezoutCounterexample.Principalization.TorsorDerPt

/-!
# The component filtration at points: antitone, and `π ∈ 𝓕₁` (leaf, part (a))

* `compFPt_antitone_ptL`: twin of `compFPt_antitone` (ComponentFilPt), which identifies `cRF` with
  the classical `cRF_eq`. Here `cRF` at an explicit point is the weighted ideal of a decided run
  (`IsInv.exists_run_pos`, `cRF_eq_run_pos`). `LocusComp.compFPt_antitone_ptL'`: for a component,
  with `IsMaxInvPt` (twin of `LocusComp.compFPt_antitone'`, used by `torsor_not_le_of_s_not_mem`).
* `PrincipalizationData.π_mem_fil_ptL`: twin of `π_mem_fil` (Torsor). That proof goes through
  `ReesData.fil_F` (the global centre via `maxCenter_eq_cRF`, i.e. `inv`, `invAt_inv`,
  `MarkedCenter.exists_mc`); this is how `maxCenter_eq_cRF` enters `main_theorem_tower`. Here
  `π ∈ 𝔭 ≤ compFPt I 𝔭 (1/d)` by `LocusComp.pow_le_compFPt_ptL` with `N = 1`.

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- **The filtration at points is antitone** (twin of `compFPt_antitone`, without `cRF_eq`). -/
lemma compFPt_antitone_ptL {I 𝔭 : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l)
    {s t : ℚ} (hst : s ≤ t) (hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ ∃ v, InvAt I p.ker v) :
    compFPt I 𝔭 t ≤ compFPt I 𝔭 s := by
  intro f hf
  rw [mem_compFPt] at hf ⊢
  intro p h𝔭p
  obtain ⟨hIp, v, n, e, he, -⟩ := hZ p h𝔭p
  obtain ⟨J, -, -⟩ := he.1
  obtain ⟨k, ck, hrun, -, -, -⟩ :=
    he.exists_run_pos p.dec_local _ (hlR p.ker I l hl) (Iloc_ne_bot hI p.ker) (Iloc_le hIp)
      J.c J.centred
  have := hf p h𝔭p
  rw [cRF_eq_run_pos p.dec_local hrun he] at this ⊢
  exact ck.RF_antitone e hst this

/-- `compFPt_antitone_ptL` for a component, with `IsMaxInvPt` (twin of
`LocusComp.compFPt_antitone'`). -/
theorem LocusComp.compFPt_antitone_ptL' {I : Ideal A} (hI : I ≠ ⊥) (l : List A)
    (hl : I = lspan l)
    (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
    {v₀ : ℕ → ℚ} (hmaxPt : IsMaxInvPt I v₀) {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {s t : ℚ}
    (hst : s ≤ t) : compFPt I 𝔭 t ≤ compFPt I 𝔭 s :=
  compFPt_antitone_ptL hI l hl hst fun p h =>
    ⟨(h𝔭.mem_ptL_mp hI l hl hchart hmaxPt p h).1, v₀, (h𝔭.mem_ptL_mp hI l hl hchart hmaxPt p h).2⟩

end BezoutCounterexample.Principalization

namespace BezoutCounterexample.PrincipalizationData

open Principalization Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  (S : PrincipalizationData A)

/-- **`π ∈ 𝓕₁`, at points** (twin of `π_mem_fil`, without `fil_F`/`maxCenter_eq_cRF`):
`π ∈ 𝔭 ≤ compFPt I 𝔭 (1/d)`. -/
theorem π_mem_fil_ptL [Fact (HasPres A)] (l : List A) (hl : S.I = lspan l)
    (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n)) :
    S.π ∈ S.fil.F 1 := by
  have h := S.h𝔭c.pow_le_compFPt_ptL S.ne_bot l hl hchart S.hmax S.d_pos S.hw 1
    (by rw [pow_one]; exact S.π_mem)
  rw [compFil_F]
  simpa using h

end BezoutCounterexample.PrincipalizationData
