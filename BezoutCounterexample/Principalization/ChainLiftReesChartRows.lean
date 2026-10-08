import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesRowsCongr
import BezoutCounterexample.Principalization.ChainLiftPartitionPt

/-!
# The data of one chart of the cover (Task B, Rees layer S6, §13 step 1)

For one chart `D : LocDataPt` of the cover, in the common layout `Fin (m + (kc + l))`
(`D.n = kc + l`, `D.k = kc`), `WRows` bundles
* the partition data of `chart_partition_pt`: head numerators `a`, integer heads `ã = Dq · a`, chart
  data `T τ` of the `τ`-coordinates (`(T τ).x = yZ ã τ`) and `gᴹ = Σ β_τ c_τ + Σ ω_q a_q`;
* the weights `wf = d · ek`;
* the rows of `rees_rows_weighted_pt` for the coordinate family `headF ã`: `γ ↦ cγ gᴺ`, `β ↦ cβ gˢ`,
  `P̃`, `Q`, and `g̃ ↦ cg g`.

`exists_wRows` produces it from the cover facts `hglob`, `hloc`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

set_option linter.unusedSectionVars false

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] {𝔭 : Ideal A}
  {m kc l r : ℕ} (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (gZ : Fin r → MvPolynomial (Fin (m + (kc + l))) ℤ) (δ : Fin r → ℕ)

/-- **The data of one chart**: partition and weighted rows. -/
structure WRows (D : LocDataPt I v₀ 𝔪) (hkn : kc ≤ D.n) (d : ℕ) where
  s : ℕ
  a : Fin D.n → A
  ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s = algebraMap A D.B (a i)
  ã : Fin kc → MvPolynomial (Fin (m + (kc + l))) ℤ
  Dq : Fin kc → ℕ
  hDq : ∀ i, 0 < Dq i
  hã : ∀ i, toAZ G e (ã i) = (Dq i : A) * a (ιk hkn i)
  Tc : RowIdx (m + (kc + l)) ((kc + l) - kc) → ChartData G
  hTx : ∀ τ, (Tc τ).x = yZ (Nat.le_add_right kc l) ã τ
  M : ℕ
  βτ : RowIdx (m + (kc + l)) ((kc + l) - kc) → A
  ω : Fin kc → A
  hpart : D.g ^ M = ∑ τ, βτ τ * toAZ G e (Tc τ).c + ∑ q, ω q * a (ιk hkn q)
  wf : Fin D.n → ℕ
  hwf : ∀ i, (wf i : ℚ) = d * D.ek i
  γ : MvPolynomial (Fin (m + (kc + l))) ℤ
  β : MvPolynomial (Fin (m + (kc + l))) ℤ
  gt : MvPolynomial (Fin (m + (kc + l))) ℤ
  cγ : ℕ
  cβ : ℕ
  cg : ℕ
  N : ℕ
  S' : ℕ
  hcγ : 0 < cγ
  hcβ : 0 < cβ
  hcg : 0 < cg
  hγA : toAZ G e γ = (cγ : A) * D.g ^ N
  hβA : toAZ G e β = (cβ : A) * D.g ^ S'
  hgtA : toAZ G e gt = (cg : A) * D.g
  P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ
  Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ
  hP : ∀ i, aeval (evG G e (reesYL G e gZ δ)) (P i) =
    LaurentPolynomial.C (toAZ G e (γ * headF ã (Fin.natAdd m (Fin.castAdd l i)))) * T (wf (ιk hkn i))
  hy : ∀ j, LaurentPolynomial.C (toAZ G e β) * reesYL G e gZ δ j =
    aeval (evW G e (headF ã) γ (fun i => wf (ιk hkn i))) (Q j)

/-- **The data of one chart exist.** -/
theorem exists_wRows (D : LocDataPt I v₀ 𝔪) (hDn : D.n = kc + l) (hkn : kc ≤ D.n) (hk : D.k = kc)
    (hn : 0 < kc + l)
    (hglob : ∀ (b : A) (t : ℚ), algebraMap A D.B b ∈ D.RFB t → ∃ N : ℕ, D.g ^ N * b ∈ compFPt I 𝔭 t)
    (hloc : ∀ (t : ℚ) (z : A), z ∈ compFPt I 𝔭 t → algebraMap A D.B z ∈ D.RFB t)
    (Φ : WFil A) {d : ℕ} (hΦ : ∀ j : ℤ, Φ.F j = compFPt I 𝔭 ((j : ℚ) / d)) (hd : 0 < d)
    (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
    (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
    (hgF : ∀ i, toAq G e (toQZ (gZ i)) ∈ Φ.F (δ i))
    (hgen : ∀ (j : ℤ) (f : A), f ∈ Φ.F j →
      LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (insert (T (-1)) (Set.range (reesYL G e gZ δ)))) :
    Nonempty (WRows G e gZ δ D hkn d) := by
  obtain ⟨s, a, ã, Dq, Tc, M, βτ, ω, hã, hTx, ha, hpart⟩ :=
    chart_partition_pt G e D hDn (Nat.le_add_right kc l) hn
  set a' : Fin D.n → A := fun i => a (Fin.cast hDn i) with ha'def
  have hidx : ∀ q, a' (ιk hkn q) = a (headIdx (Nat.le_add_right kc l) q) := fun q =>
    congrArg a (Fin.ext rfl)
  have hã' : ∀ q, toAZ G e (ã q) = (Dq q : A) * a' (ιk hkn q) := fun q => by
    rw [hidx]; exact (hã q).2
  obtain ⟨wf, hwf⟩ := Constructive.finite_choice_dep (ι := Fin D.n)
    (P := fun i (w : ℕ) => (w : ℚ) = d * D.ek i) fun i => by
      obtain ⟨w, hw'⟩ := hw i
      exact ⟨w, by rw [hw', ← ext0_apply D.ek i, D.hv]⟩
  obtain ⟨γ, β, cγ, cβ, N, S', P, Q, hcγ, hcβ, hγA, hβA, hP, hy⟩ :=
    rees_rows_weighted_pt G e D hkn hk hglob hloc Φ hΦ hd hneg gZ δ hgF hgen s a' ha Dq
      (fun i => (hã i).1) (headF ã) (fun i => by rw [headF_head]; exact hã' i) wf hwf
  obtain ⟨cg, gt, hcg, hgt⟩ := exists_toAq_int G e D.g
  have hDq : ∀ i, 0 < Dq i := fun i => (hã i).1
  exact ⟨⟨s, a', ha, ã, Dq, hDq, hã', Tc, hTx, M, βτ, ω, by rw [hpart]; simp only [hidx]; rfl,
    wf, hwf, γ, β, gt, cγ, cβ, cg, N, S', hcγ, hcβ, hcg, hγA, hβA, hgt, P, Q, hP, hy⟩⟩

end BezoutCounterexample.Principalization
