import BezoutCounterexample.Principalization.RunPos
import BezoutCounterexample.Principalization.SpreadPos
import BezoutCounterexample.Principalization.InvariantPt

/-!
# Invariants at explicit points are good (D3.6, leaf; route 1 of docs/remaining-classical.md)

`InvAt.goodV` (Induction) gets the Method-1 run from the classical `IsInv.exists_run`
(`MC.exists_run`, `TI.step`, `step_*_Q`, `exists_min_Xi`). At an explicit point the residue field is
decided (`Pt.dec_local`), so the run comes from `IsInv.exists_run_pos` (RunPos), and `IsRun.goodV`
(with the constructive `nextW_good` of batch D) finishes:

* `IsInv.goodV_pos`, `InvAt.goodV_pt`;
* `InvAt.mem_Γ_pt`, `InvAt.exists_zero_eq_pt`: the point forms of `InvAt.mem_Γ`,
  `InvAt.exists_zero_eq` (InvariantPt).

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing BezoutCounterexample.Constructive

/-- **Method-1 weights of an invariant are good**, with a decided residue field. -/
lemma IsInv.goodV_pos {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S]
    [Fact (PolyIndNoeth S)] (hdec : ∀ x : S, x ∈ maximalIdeal S ∨ IsUnit x)
    {n : ℕ} {I : Ideal S} (l : List S) (hl : I = lspan l) (hI : I ≠ ⊥)
    (hIm : I ≤ maximalIdeal S) {e : Fin n → ℚ} (he : IsInv I n e) (c : Chart S n)
    (hc : c.IsCentred) : GoodV (ext0 e) := by
  obtain ⟨k, ck, hrun, -, -, -⟩ := he.exists_run_pos hdec l hl hI hIm c hc
  exact hrun.goodV (fun _ => le_rfl) (fun _ _ => rfl) (fun i hi => absurd hi (Nat.not_lt_zero _))

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A]

/-- **An invariant at an explicit point is good.** -/
lemma InvAt.goodV_pt {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l) (q : Pt A)
    [Fact (PolyIndNoeth (Localization.AtPrime q.ker))] (hIq : I ≤ q.ker) {v : ℕ → ℚ}
    (hv : InvAt I q.ker v) : GoodV v := by
  obtain ⟨n, e, he, rfl⟩ := hv
  obtain ⟨J, -, -⟩ := he.1
  exact he.goodV_pos q.dec_local _ (hlR q.ker I l hl) (Iloc_ne_bot hI q.ker) (Iloc_le hIq)
    J.c J.centred

/-- **An invariant at an explicit point lies in `Γ`** (point form of `InvAt.mem_Γ`). -/
theorem InvAt.mem_Γ_pt {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l) (q : Pt A)
    [Fact (PolyIndNoeth (Localization.AtPrime q.ker))] (hIq : I ≤ q.ker) {v : ℕ → ℚ}
    (hv : InvAt I q.ker v) : v ∈ Γ := by
  refine ⟨InvAt.goodV_pt hI l hl q hIq hv, fun i hi => ?_⟩
  obtain ⟨n, e, he, hev⟩ := hv
  rw [← hev] at hi ⊢
  simp only [ext0] at hi ⊢
  rcases Nat.lt_or_ge (i + 1) n with h1 | h1
  · rw [dite_eq_left h1]
    rw [dite_eq_left (show i < n by omega)] at hi
    have h2 : e ⟨i + 1, h1⟩ ≤ e ⟨i, by omega⟩ := he.anti (Fin.le_def.2 (Nat.le_succ i))
    exact le_antisymm (h2.trans hi.le) (he.nonneg _)
  · rw [dite_eq_right (by omega)]

/-- **The first weight of an invariant at an explicit point is `1/a`.** -/
theorem InvAt.exists_zero_eq_pt {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l)
    (q : Pt A) [Fact (PolyIndNoeth (Localization.AtPrime q.ker))] (hIq : I ≤ q.ker)
    {v : ℕ → ℚ} (hv : InvAt I q.ker v) : ∃ a : ℕ, 0 < a ∧ v 0 = 1 / a := by
  rcases InvAt.goodV_pt hI l hl q hIq hv 0 with h0 | ⟨a, ha, h⟩
  · exact absurd h0 (InvAt.zero_ne hI hv)
  · exact ⟨a, ha, by rw [h]; simp [denPN]⟩

end BezoutCounterexample.Principalization
