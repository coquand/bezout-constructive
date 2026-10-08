import BezoutCounterexample.Principalization.StepRunPos
import BezoutCounterexample.Principalization.TransferPos

/-!
# Method 1 runs with a decided residue field (D3.5, leaf)

`MC.exists_run` (Transfer) decides `J.Adm I` by `by_cases` and steps with the classical
`SA.step_run`; `IsInv.of_run` (Invariant) compares with the classical transfer bound. With a
decided residue field (`hdec`; at a point `q`: `Pt.dec_local` on `A_{q.ker}`) and generators of `I`:

* `MC.exists_run_pos`: the run, deciding admissibility by `MC.adm_or_witness` and stepping with
  `SA.step_run_pos` (D3.4); starts from `sa_zero_pos`;
* `IsInv.of_run_pos`: a run ending admissibly computes the invariant (`IsRun.transfer_bound_pos`);
* `IsInv.exists_run_pos`: every centred chart starts a run computing the invariant.

Callers (Vertex, ReesVertex, Invariant, `numNonzero_inv_add_le`) switch to these in the D3.5
integration diff. Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing Constructive

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] {n : ℕ}

namespace MC

variable {I : Ideal R}

/-- **Method 1 produces a run ending in an admissible marked centre**, positively. -/
theorem exists_run_pos [Fact (PolyIndNoeth R)] (hdec : ∀ x : R, x ∈ maximalIdeal R ∨ IsUnit x)
    (l : List R) (hl : I = lspan l) (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal R) (c : Chart R n)
    (hc : c.IsCentred) :
    ∃ (k : ℕ) (ck : Chart R n) (ek : Fin n → ℚ), IsRun I 0 c 0 k ck ek ∧ I ≤ ck.RF ek 1 ∧
      ck.IsCentred ∧ (∀ i, 0 ≤ ek i) ∧ Antitone ek ∧ (∀ i, ek i ≠ 0 ↔ (i : ℕ) < k) := by
  have key : ∀ d j, n - j = d → ∀ J : MC R n, SA I j J →
      ∃ (k : ℕ) (ck : Chart R n) (ek : Fin n → ℚ), IsRun I j J.c J.e k ck ek ∧ I ≤ ck.RF ek 1 ∧
        ck.IsCentred ∧ (∀ i, 0 ≤ ek i) ∧ Antitone ek ∧ (∀ i, ek i ≠ 0 ↔ (i : ℕ) < k) := by
    intro d
    induction d with
    | zero =>
      intro j hj J hJ
      rcases adm_or_witness hdec l hl J with ha | ⟨f₀, hf₀, β₀, hβ₀, hlt₀⟩
      · exact ⟨j, J.c, J.e, .refl _ _ _, ha, J.centred, J.nonneg, J.anti, hJ.supp⟩
      · obtain ⟨hjn, -⟩ := hJ.step_run_pos hdec l hl hf₀ hβ₀ hlt₀
        exact absurd hj (Nat.sub_ne_zero_of_lt hjn)
    | succ d ih =>
      intro j hj J hJ
      rcases adm_or_witness hdec l hl J with ha | ⟨f₀, hf₀, β₀, hβ₀, hlt₀⟩
      · exact ⟨j, J.c, J.e, .refl _ _ _, ha, J.centred, J.nonneg, J.anti, hJ.supp⟩
      · obtain ⟨hjn, f, hf, β, l', hl', hβl, hlam, hN, hunit, hb, u, hu, hc', hnn, ha', hSA'⟩ :=
          hJ.step_run_pos hdec l hl hf₀ hβ₀ hlt₀
        obtain ⟨k, ck, ek, hrun, hadm, hck, hek⟩ := ih (j + 1) (by rw [Nat.sub_succ, hj]; rfl) _ hSA'
        exact ⟨k, ck, ek, .step hjn f hf β l' hl' hβl hlam hN hunit hb u hu hrun, hadm, hck, hek⟩
  exact key (n - 0) 0 rfl ⟨c, 0, hc, fun _ => le_rfl, fun _ _ _ => le_rfl⟩
    (sa_zero_pos hdec l hl hI hIm c hc)

end MC

/-- **A run ending admissibly computes the invariant** (`IsInv.of_run` with the decided transfer
bound). -/
lemma IsInv.of_run_pos (hdec : ∀ x : R, x ∈ maximalIdeal R ∨ IsUnit x) {I : Ideal R}
    {c : Chart R n} {k : ℕ} {ck : Chart R n} {ek : Fin n → ℚ}
    (hrun : IsRun I 0 c 0 k ck ek) (hadm : I ≤ ck.RF ek 1) (hck : ck.IsCentred)
    (hnn : ∀ i, 0 ≤ ek i) (hanti : Antitone ek) : IsInv I n ek := by
  refine ⟨⟨⟨ck, ek, hck, hnn, hanti⟩, hadm, rfl⟩, fun J' hJ' => ?_⟩
  obtain ⟨_, _, hb⟩ := hrun.transfer_bound_pos hdec (Compat.id c)
  have := (hb J' (by rw [Ideal.map_id]; exact hJ')).1
  rwa [pad_refl] at this

/-- **Every centred chart starts a run computing the invariant**, positively. -/
lemma IsInv.exists_run_pos [Fact (PolyIndNoeth R)] (hdec : ∀ x : R, x ∈ maximalIdeal R ∨ IsUnit x)
    {I : Ideal R} (l : List R) (hl : I = lspan l) (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal R)
    {e : Fin n → ℚ} (he : IsInv I n e) (c : Chart R n) (hc : c.IsCentred) :
    ∃ (k : ℕ) (ck : Chart R n), IsRun I 0 c 0 k ck e ∧ I ≤ ck.RF e 1 ∧ ck.IsCentred ∧
      (∀ i, e i ≠ 0 ↔ (i : ℕ) < k) := by
  obtain ⟨k, ck, ek, hrun, hadm, hck, hnn, hanti, hsupp⟩ :=
    MC.exists_run_pos hdec l hl hI hIm c hc
  obtain rfl := (IsInv.of_run_pos hdec hrun hadm hck hnn hanti).unique he
  exact ⟨k, ck, hrun, hadm, hck, hsupp⟩

end BezoutCounterexample.Principalization
