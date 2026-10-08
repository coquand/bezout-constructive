import BezoutCounterexample.LengthControl
import BezoutCounterexample.Principalization.DerivRFPos
import BezoutCounterexample.Principalization.GoodVPt

/-!
# The length bound `(⋆_N)` at explicit points (leaf, part (a))

`numNonzero_inv_add_le_chart` (LengthControl) bounds the classical `inv I 𝔪` (`invAt_inv`) and
gets its Method-1 run from the classical `IsInv.exists_run`; the bound itself goes through
`length_le_of_derivations` (`deriv_mem_RF`, classical transfer). At an explicit point `q` the
residue field is decided (`Pt.dec_local`), so:

* `numNonzero_add_le_chart_pt`: for every invariant `v` of `I` at `q`, `numNonzero v + m ≤ kd`
  (run from `IsInv.exists_run_pos`, bound from `length_le_of_derivations_pos`);
* `StarC.numNonzero_le_pt`: under `(⋆_N)`, every invariant at an explicit point of `V(𝔟)` has at
  most `N` nonzero entries (twin of `StarC.numNonzero_inv_le`).

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization Constructive

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B]

/-- **Lemma 3.7(2) with chart sizes, at an explicit point.** -/
theorem numNonzero_add_le_chart_pt {I : Ideal B} (hI : I ≠ ⊥) (l : List B) (hl : I = lspan l)
    (q : Pt B) [Fact (PolyIndNoeth (Localization.AtPrime q.ker))] (hIq : I ≤ q.ker)
    {v : ℕ → ℚ} (hv : InvAt I q.ker v) {kd : ℕ} (hkd : ChartDim B kd) {m : ℕ}
    (δ : Fin m → Derivation ℚ B B) (hδ : ∀ j, ∀ f ∈ I, δ j f ∈ I) (z : Fin m → B)
    (hz : (Matrix.of fun j q' => δ j (z q')).det ∉ q.ker) :
    numNonzero v + m ≤ kd := by
  obtain ⟨n, e, he, hext⟩ := hv
  obtain ⟨J, -, -⟩ := he.1
  obtain ⟨k, ck, hrun, hadm, hck, hsupp⟩ :=
    he.exists_run_pos q.dec_local _ (hlR q.ker I l hl) (Iloc_ne_bot hI q.ker) (Iloc_le hIq)
      J.c J.centred
  have hunit : IsUnit (Matrix.of fun j l => derivLoc (δ j) q.ker
      (algebraMap B (Localization.AtPrime q.ker) (z l))).det := by
    rw [det_extLoc]
    exact IsLocalization.map_units (Localization.AtPrime q.ker) (⟨_, hz⟩ : q.ker.primeCompl)
  have hkm := length_le_of_derivations_pos q.dec_local hrun hadm hck he.nonneg he.anti hsupp
    (fun j => derivLoc (δ j) q.ker)
    (fun j g hg => deriv_mem_map (algebraMap B _) (derivLoc (δ j) q.ker) (δ j)
      (fun r => extLoc_algebraMap _ (δ j) r) (hδ j) hg) _ hunit
  have hk : numNonzero v = k := by
    rw [← hext]
    unfold numNonzero
    have : {i | ext0 e i ≠ 0} = ↑(Finset.range k) := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.coe_range, Set.mem_Iio]
      by_cases hin : i < n
      · rw [show ext0 e i = e ⟨i, hin⟩ by simp [ext0, hin]]
        exact hsupp ⟨i, hin⟩
      · rw [show ext0 e i = 0 by simp [ext0, hin]]
        simp only [ne_eq, not_true_eq_false, false_iff, not_lt]
        omega
    rw [this, Set.ncard_coe_finset, Finset.card_range]
  rw [hk, ← hkd.card_eq J.c]
  exact hkm

/-- **Under `(⋆_N)`, every invariant at an explicit point of `V(𝔟)` has at most `N` nonzero
entries** (point form of `StarC.numNonzero_inv_le`). -/
theorem StarC.numNonzero_le_pt {N m : ℕ} {𝔟 : Ideal B} (h : StarC N 𝔟 m) (h𝔟 : 𝔟 ≠ ⊥)
    (l : List B) (hl : 𝔟 = lspan l) (q : Pt B) [Fact (PolyIndNoeth (Localization.AtPrime q.ker))]
    (h𝔟q : 𝔟 ≤ q.ker) {v : ℕ → ℚ} (hv : InvAt 𝔟 q.ker v) : numNonzero v ≤ N := by
  obtain ⟨δ, z, hδ, hdet⟩ := h.derivations q h𝔟q
  obtain ⟨k, hk, hkN⟩ := h.dim_le
  have := numNonzero_add_le_chart_pt h𝔟 l hl q h𝔟q hv hk δ hδ z hdet
  omega

end BezoutCounterexample
