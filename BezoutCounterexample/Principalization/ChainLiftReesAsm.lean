import Mathlib
import BezoutCounterexample.Principalization.ChainLiftCoverPt
import BezoutCounterexample.Principalization.ChainLiftCertCover

/-!
# Gluing the opens of the Rees algebra (Task B, Rees layer S6, assembly)

`OpenOK GR ε cond`: some `e` in the certificate layout has a power cover by square pieces of
`GR' = GR.map (rename ε)` and is nonzero at every point `P` of `QR GR ε` satisfying `cond P`.

* `smoothCert_of_opens`: finitely many such opens whose conditions cover all points give a
  `SmoothCert` of `GR'` (`exists_cover_of_pts` + `exists_smoothCert_of_pow_mem`);
* `weighted_ok`, `laurent_ok`: the two kinds of opens, from the stage-2 producers and the value
  lemmas of `ChainLiftCoverPt`;
* `exists_fin_surj`: a surjective enumeration of a finset inside a proof (no `toList`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

set_option linter.unusedSectionVars false

/-- **Enumerating a finset surjectively** inside a proof (`Finset.induction_on`). -/
lemma exists_fin_surj {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    ∃ (K : ℕ) (f : Fin K → ι), ∀ i ∈ s, ∃ k, f k = i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Fin.elim0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨K, f, hf⟩ := ih
    refine ⟨K + 1, Fin.cons a f, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨0, rfl⟩
    · obtain ⟨k, rfl⟩ := hf i hi
      exact ⟨k.succ, rfl⟩

variable {A : Type} [CommRing A] [Algebra ℚ A] {m kc l r : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (gZ : Fin r → MvPolynomial (Fin (m + (kc + l))) ℤ) (δ : Fin r → ℕ)
  (GR : List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ))
  (hGR : ∀ h, aeval (reesVec G e gZ δ) h = 0 ↔ h ∈ lspan (GR.map toQZ))
  (ε : Fin ((m + (kc + l)) + (1 + r)) ≃ Fin ((m + r) + ((1 + kc) + l)))

/-- **A certified open**: a power cover and nonvanishing under `cond`. -/
def OpenOK (cond : Pt (QR GR ε) → Prop) : Prop :=
  ∃ e : MvPolynomial (Fin ((m + r) + ((1 + kc) + l))) ℤ,
    (∃ (a K : ℕ) (P : Fin K → SquarePiece (m + r) ((1 + kc) + l) (GR.map (rename ε)))
      (u : Fin K → MvPolynomial (Fin ((m + r) + ((1 + kc) + l))) ℤ) (N : ℕ), 0 < N ∧
      (N : MvPolynomial _ ℤ) * e ^ a - ∑ k, u k * (P k).h ∈ lspan (GR.map (rename ε))) ∧
    ∀ P, cond P → valR GR ε P e ≠ 0

/-- **Gluing certified opens.** -/
theorem smoothCert_of_opens {ι : Type*} (cond : ι → Pt (QR GR ε) → Prop)
    (hok : ∀ i, OpenOK GR ε (cond i)) (henum : ∃ (J : ℕ) (f : Fin J → ι), ∀ i, ∃ k, f k = i)
    (hcov : ∀ P, ∃ i, cond i P) :
    Nonempty (SmoothCert (m + r) ((1 + kc) + l) (GR.map (rename ε))) := by
  obtain ⟨J, f, hf⟩ := henum
  obtain ⟨E, hE⟩ := Constructive.finite_choice_dep (ι := Fin J)
    (P := fun k (x : MvPolynomial (Fin ((m + r) + ((1 + kc) + l))) ℤ) =>
      (∃ (a K : ℕ) (P : Fin K → SquarePiece (m + r) ((1 + kc) + l) (GR.map (rename ε)))
        (u : Fin K → MvPolynomial (Fin ((m + r) + ((1 + kc) + l))) ℤ) (N : ℕ), 0 < N ∧
        (N : MvPolynomial _ ℤ) * x ^ a - ∑ k, u k * (P k).h ∈ lspan (GR.map (rename ε))) ∧
      ∀ P, cond (f k) P → valR GR ε P x ≠ 0)
    fun k => hok (f k)
  obtain ⟨C, hC, hmem⟩ := exists_cover_of_pts (GR.map (rename ε)) E fun P => by
    obtain ⟨i, hi⟩ := hcov P
    obtain ⟨k, rfl⟩ := hf i
    refine ⟨k, fun hk => (hE k).2 P hi ?_⟩
    exact P.mem_ker.1 hk
  exact exists_smoothCert_of_pow_mem E C hC hmem fun k => (hE k).1

include hGR in
lemma hGR0_of (g : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) (hg : g ∈ GR) :
    aeval (evG G e (reesYL G e gZ δ)) g = 0 := by
  have h1 : aeval (evG G e (reesYL G e gZ δ)) g = aeval (R := ℚ) (reesVec G e gZ δ) (toQZ g) := by
    rw [← evG_reesYL G e gZ δ]; exact (aeval_int_cast _ _).symm
  rw [h1, hGR]
  exact Ideal.subset_span (List.mem_map_of_mem hg)

/-- **A Laurent open is certified**, under `S.h εL ≠ 0` at the restriction. -/
theorem laurent_ok (S : SquarePiece m (kc + l) G) {d : ℕ} (hδ : ∀ j, δ j ≤ d)
    (εL : MvPolynomial (Fin (m + (kc + l))) ℤ) (Pt' : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hrows : ∀ x ∈ rowsL gZ δ S.F d εL Pt', x ∈ lspan GR) :
    OpenOK GR ε fun P => qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε P) (S.h * εL) ≠ 0 := by
  obtain ⟨n, ⟨T, -, hTc⟩, hinj⟩ := laur_open_of_rows G e gZ δ S hδ εL Pt' GR
    (hGR0_of G e gZ δ GR hGR) hrows ε
  refine ⟨T.c * _, T.exists_pow_cover (by omega) _ hinj, fun P hne => ?_⟩
  rw [hTc, map_mul]
  exact val_laurent_ne G e gZ δ GR hGR ε P S d εL Pt' _ n
    (hrows _ (by simp [rowsL])) hne

section Weighted

variable [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ}
  {𝔪 : Ideal A} [𝔪.IsMaximal]

/-- **A weighted open is certified**, under `S.h β γ g̃ ≠ 0` and vanishing heads at the restriction. -/
theorem weighted_ok (D : LocDataPt I v₀ 𝔪) (hkn : kc ≤ D.n) (hk : D.k = kc)
    {d : ℕ} (hd : 0 < d) (s : ℕ) (a : Fin D.n → A)
    (ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s = algebraMap A D.B (a i))
    (Dq : Fin kc → ℕ) (hDq : ∀ i, 0 < Dq i) (S : SquarePiece m (kc + l) G)
    (hhead : ∀ i, toAZ G e (S.F (Fin.natAdd m (Fin.castAdd l i))) = (Dq i : A) * a (ιk hkn i))
    (wf : Fin D.n → ℕ) (hwf : ∀ i, (wf i : ℚ) = d * D.ek i)
    (inst₁ : ∀ q : Pt A, Fact (PolyIndNoeth (Localization.AtPrime q.ker)))
    (inst₂ : ∀ q : Pt A, Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker))
    (inst₃ : ∀ q : Pt A,
      Algebra.FormallySmooth ℚ (IsLocalRing.ResidueField (Localization.AtPrime q.ker)))
    (γ β gt : MvPolynomial (Fin (m + (kc + l))) ℤ) (cγ cg N : ℕ)
    (hγA : toAZ G e γ = (cγ : A) * D.g ^ N) (hgtA : toAZ G e gt = (cg : A) * D.g)
    (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)
    (hP : ∀ i, aeval (evG G e (reesYL G e gZ δ)) (P i) =
      LaurentPolynomial.C (toAZ G e (γ * S.F (Fin.natAdd m (Fin.castAdd l i)))) * T (wf (ιk hkn i)))
    (hy : ∀ j, LaurentPolynomial.C (toAZ G e β) * reesYL G e gZ δ j =
      aeval (evW G e S.F γ (fun i => wf (ιk hkn i))) (Q j))
    (hrows : ∀ x ∈ rowsW S.F γ (fun i => wf (ιk hkn i)) P β Q, x ∈ lspan GR) :
    OpenOK GR ε fun Pp => qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε Pp)
        (S.h * (β * (γ * gt))) ≠ 0 ∧
      ∀ i, qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε Pp)
        (S.F (Fin.natAdd m (Fin.castAdd l i))) = 0 := by
  obtain ⟨n, ⟨T, -, hTc⟩, hinj⟩ := rees_open_weighted_of_rows G e D hkn hk hd
    (reesYL G e gZ δ) s a ha Dq hDq S hhead wf hwf inst₁ inst₂ inst₃ γ β gt cγ cg N hγA hgtA
    P Q hP hy GR (hGR0_of G e gZ δ GR hGR) hrows ε
  refine ⟨T.c * _, T.exists_pow_cover (by omega) _ hinj, fun Pp ⟨hne, hheads⟩ => ?_⟩
  rw [hTc, map_mul]
  exact val_weighted_ne G e gZ δ GR hGR ε Pp S γ β gt _ Q P n hne hheads

end Weighted

end BezoutCounterexample.Principalization
