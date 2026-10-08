import BezoutCounterexample.Principalization.TorsorDer
import BezoutCounterexample.Principalization.LocDataPtMp
import BezoutCounterexample.Principalization.DerivRFPos
import BezoutCounterexample.Principalization.RunPos
import BezoutCounterexample.Principalization.ComponentFilPtL

/-!
# Derivations and the component filtration at explicit points (leaf, part (a))

`deriv_mem_compFPt` (TorsorDer) has no `hmax` in its statement but uses four classical inputs: the
component lemma `LocusComp.mem` (maximal locus via `exists_invAt`), the run `IsInv.exists_run`,
`deriv_mem_RF` (classical transfer) and `cRF_eq` (`MC.exists_max_FT`). At an explicit point the
residue field is decided, so each has a twin:

* `LocusComp.mem_ptL_mp` (with `hmaxPt : IsMaxInvPt I v₀`), `IsInv.exists_run_pos`,
  `deriv_mem_RF_pos`, and `cRF_eq_of_rf` with the decided transfer bound (`cRF_eq_run_pos`).

Results: `cRF_eq_run_pos`, `deriv_mem_compFPt_ptL`. Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- **`cRF` is the weighted ideal of a run ending admissibly**, with a decided residue field
(twin of `cRF_eq` on runs: the transfer bound replaces `MC.exists_max_FT`). -/
lemma cRF_eq_run_pos {I 𝔪 : Ideal A} [𝔪.IsMaximal]
    (hdec : ∀ x : Localization.AtPrime 𝔪, x ∈ maximalIdeal _ ∨ IsUnit x) {n : ℕ}
    {c : Chart (Localization.AtPrime 𝔪) n} {k : ℕ} {ck : Chart (Localization.AtPrime 𝔪) n}
    {e : Fin n → ℚ} (hrun : IsRun (Iloc I 𝔪) 0 c 0 k ck e) (he : IsInv (Iloc I 𝔪) n e)
    (t : ℚ) : cRF I 𝔪 t = ck.RF e t := by
  obtain ⟨C3, hC3, hbound⟩ := hrun.transfer_bound_pos hdec (hnn := le_refl n) (Compat.id c)
  have hC3x : ∀ j, C3.x j = ck.x j := fun j => by
    have := hC3.x j; simpa [Fin.castLE_refl] using this
  refine cRF_eq_of_rf he fun J' hJ' hJe => ?_
  have h := (hbound J' (by rwa [Ideal.map_id])).2 (by rw [pad_refl]; exact hJe) t
  rw [h, pad_refl]
  exact Chart.RF_congr (fun j _ => hC3x j) t

variable {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l)
  (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
  {v₀ : ℕ → ℚ} (hmaxPt : IsMaxInvPt I v₀) {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭)

include hI hl hchart hmaxPt h𝔭 in
/-- **Derivations stabilizing `I` stabilize the component filtration at points** (twin of
`deriv_mem_compFPt`, with `IsMaxInvPt`). -/
theorem deriv_mem_compFPt_ptL (δ : Derivation ℚ A A) (hδ : ∀ f ∈ I, δ f ∈ I) (t : ℚ) {f : A}
    (hf : f ∈ compFPt I 𝔭 t) : δ f ∈ compFPt I 𝔭 t := by
  rw [mem_compFPt] at hf ⊢
  intro p h𝔭p
  obtain ⟨hIp, n, e, he, -⟩ := h𝔭.mem_ptL_mp hI l hl hchart hmaxPt p h𝔭p
  obtain ⟨J, -, -⟩ := he.1
  obtain ⟨k, ck, hrun, hadm, hck, hsupp⟩ :=
    he.exists_run_pos p.dec_local _ (hlR p.ker I l hl) (Iloc_ne_bot hI p.ker) (Iloc_le hIp)
      J.c J.centred
  set δ𝔪 : Derivation ℚ (Localization.AtPrime p.ker) (Localization.AtPrime p.ker) :=
    extLoc (S := Localization.AtPrime p.ker) p.ker.primeCompl δ
  have hδ𝔪 : ∀ g ∈ Iloc I p.ker, δ𝔪 g ∈ Iloc I p.ker := fun g hg =>
    deriv_mem_map (algebraMap A _) δ𝔪 δ (fun r => extLoc_algebraMap _ δ r) hδ hg
  have hx : ∀ i, e i ≠ 0 → δ𝔪 (ck.x i) ∈ ck.RF e (e i) := fun i hi =>
    deriv_mem_RF_pos p.dec_local hrun hadm hck he.nonneg he.anti hsupp δ𝔪 hδ𝔪 i
      ((hsupp i).1 hi)
  have hcRF : cRF I p.ker t = ck.RF e t := cRF_eq_run_pos p.dec_local hrun he t
  have h1 := hf p h𝔭p
  rw [hcRF] at h1 ⊢
  rw [← extLoc_algebraMap p.ker.primeCompl δ f]
  exact deriv_mem_RF_of_x ck δ𝔪 hx t h1

end BezoutCounterexample.Principalization
