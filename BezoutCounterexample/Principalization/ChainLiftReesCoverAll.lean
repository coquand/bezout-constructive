import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesChartRows
import BezoutCounterexample.Principalization.ChainLiftReesGRAll
import BezoutCounterexample.Principalization.ChainLiftReesPtCase
import BezoutCounterexample.Principalization.ChartCoverPtL

/-!
# The certificate of the Rees algebra (Task B, Rees layer S6, §13 step 3)

From `A`'s certificate (`hG`, pieces `P_j`), a chart cover `C : ChartCoverPtL` with all charts in one
layout (`(C.D k).n = kc + l`, `(C.D k).k = kc`), the cover facts `hglob`, `hloc`, integer Rees
generators and a power `iᵇ ∈ F₁` of the element `i ∈ 𝔭` of the cover:

1. the data `W k : WRows` of every chart (`exists_wRows`), the Laurent row of `iᵇ` (`exists_laurT`), and
   one global presentation `GR` containing all rows (`exists_GR_all`);
2. the opens, indexed by `Fin K_A ⊕ (charts × heads × pieces) ⊕ (charts × τ × pieces × minors)`:
   `L𝔭(j)` (Laurent, `ε ↦ c iᵇ`), `Lh(k, q, j)` (Laurent, `ε = γₖ ãₖ_q`), `W(k, τ, j, σ)` (weighted,
   `A`-piece = minor piece `σ` of `exists_minor_cover (Tₖ τ) (h_j^{e+f})`, heads `ãₖ`);
3. the point argument (`hcov`) by zero tests at the restriction `q` of the point: `h_j(q) ≠ 0`; then
   `i(q) ≠ 0` gives `L𝔭(j)`; else some `gₖ(q) ≠ 0`; then some `ãₖ_q(q) ≠ 0` gives `Lh(k, q, j)`; else
   the partition gives `τ` and the minor cover `σ`: `W(k, τ, j, σ)`;
4. `smoothCert_of_opens`.

`exists_smoothCert_rees`: `GR` with its kernel property and a `SmoothCert` of `GR` renamed along `ε`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

set_option linter.unusedSectionVars false

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ} {𝔭 : Ideal A}

/-- A certificate of a nontrivial ring has a piece, hence `0 < n`. -/
lemma SmoothCert.pos_of_ne {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}
    (e : SmoothCert.QB G ≃+* A) (hG : SmoothCert m n G) : 0 < n := by
  rcases Nat.eq_zero_or_pos hG.K with h0 | hpos
  · exfalso
    haveI : IsEmpty (Fin hG.K) := by rw [h0]; infer_instance
    have h1 := SmoothCert.ψ_eq_zero hG.cover
    rw [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, map_natCast] at h1
    have h2 := congrArg e h1
    rw [map_natCast, map_zero, ← map_natCast (algebraMap ℚ A), map_eq_zero, Nat.cast_eq_zero] at h2
    exact hG.hC.ne' h2
  · exact (hG.P ⟨0, hpos⟩).hn

/-- **The certificate of the Rees algebra** in the layout `(m + r) + ((1 + kc) + l)`. -/
theorem exists_smoothCert_rees {m kc l r : ℕ} (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ))
    (e : SmoothCert.QB G ≃+* A) (hG : SmoothCert m (kc + l) G)
    (C : ChartCoverPtL I v₀ 𝔭) (hCn : ∀ k, (C.D k).n = kc + l) (hCk : ∀ k, (C.D k).k = kc)
    (hglob : ∀ k (b : A) (t : ℚ), algebraMap A (C.D k).B b ∈ (C.D k).RFB t →
      ∃ N : ℕ, (C.D k).g ^ N * b ∈ compFPt I 𝔭 t)
    (hloc : ∀ k (t : ℚ) (z : A), z ∈ compFPt I 𝔭 t → algebraMap A (C.D k).B z ∈ (C.D k).RFB t)
    (Φ : WFil A) {d : ℕ} (hΦ : ∀ j : ℤ, Φ.F j = compFPt I 𝔭 ((j : ℚ) / d)) (hd : 0 < d)
    (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
    (gZ : Fin r → MvPolynomial (Fin (m + (kc + l))) ℤ) (δ : Fin r → ℕ) (hδ : ∀ j, δ j ≤ d)
    (hgF : ∀ i, toAq G e (toQZ (gZ i)) ∈ Φ.F (δ i))
    (hgen : ∀ (j : ℤ) (f : A), f ∈ Φ.F j →
      LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (insert (T (-1)) (Set.range (reesYL G e gZ δ))))
    (hib : ∃ b : ℕ, C.i ^ b ∈ Φ.F 1)
    (inst₁ : ∀ q : Pt A, Fact (PolyIndNoeth (Localization.AtPrime q.ker)))
    (inst₂ : ∀ q : Pt A, Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker))
    (inst₃ : ∀ q : Pt A,
      Algebra.FormallySmooth ℚ (IsLocalRing.ResidueField (Localization.AtPrime q.ker)))
    (ε : Fin ((m + (kc + l)) + (1 + r)) ≃ Fin ((m + r) + ((1 + kc) + l))) :
    ∃ GR : List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ),
      (∀ h, aeval (reesVec G e gZ δ) h = 0 ↔ h ∈ lspan (GR.map toQZ)) ∧
      Nonempty (SmoothCert (m + r) ((1 + kc) + l) (GR.map (rename ε))) := by
  have hn : 0 < kc + l := SmoothCert.pos_of_ne e hG
  have hkn : ∀ k, kc ≤ (C.D k).n := fun k => by rw [hCn k]; exact Nat.le_add_right kc l
  -- 1. the data of the charts, the Laurent row of `iᵇ`, and `GR`
  obtain ⟨W⟩ := Constructive.finite_nonempty_pi (X := fun k => WRows G e gZ δ (C.D k) (hkn k) d)
    fun k => exists_wRows G e gZ δ (C.D k) (hCn k) (hkn k) (hCk k) hn (hglob k) (hloc k) Φ hΦ hd
      hw hneg hgF hgen
  obtain ⟨b, hb⟩ := hib
  obtain ⟨ε₀, c₀, Pt₀, hc₀, hε₀, hPt₀⟩ := exists_laurT G e gZ δ Φ hneg hgF hgen hb
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hw0 : ∀ k i, 0 < (W k).wf (ιk (hkn k) i) := fun k i => by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h1 := (W k).hwf (ιk (hkn k) i)
    rw [h0, Nat.cast_zero, eq_comm, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact hdq h1
    · exact ((C.D k).supp (ιk (hkn k) i)).2 (by rw [hCk k]; exact i.2) h1
  obtain ⟨GR, hGR, hGGR, hL₀, hWr, hLh⟩ := exists_GR_all G e gZ δ hδ ε₀ Pt₀ hPt₀
    (fun k => (W k).ã) (fun k => (W k).γ) (fun k => (W k).β)
    (fun k i => (W k).wf (ιk (hkn k) i)) hw0 (fun k => (W k).P) (fun k => (W k).Q)
    (fun k => (W k).hP) (fun k => (W k).hy)
  refine ⟨GR, hGR, ?_⟩
  -- 2. the minor pieces of the weighted opens
  obtain ⟨Pm, hPm⟩ := Constructive.finite_choice_dep
    (ι := Fin C.n × RowIdx (m + (kc + l)) ((kc + l) - kc) × Fin hG.K)
    (α := fun _ => ChartData.MinorIdx (m := m) (n := kc + l) G → SquarePiece m (kc + l) G)
    (P := fun x Pm => (∀ s i, (Pm s).F (Fin.natAdd m (Fin.castAdd l i)) =
        ((W x.1).Tc x.2.1).x (Fin.castAdd l i)) ∧
      ∃ (N a c : ℕ) (u : ChartData.MinorIdx (m := m) (n := kc + l) G → MvPolynomial (Fin (m + (kc + l))) ℤ),
        0 < N ∧ (N : MvPolynomial (Fin (m + (kc + l))) ℤ) * (((W x.1).Tc x.2.1).c ^ a *
          ((hG.P x.2.2).h ^ ((hG.P x.2.2).e + (hG.P x.2.2).f)) ^ c) -
          ∑ s, u s * (Pm s).h ∈ lspan G)
    fun x => by
      obtain ⟨K', Pm, u, hF, -, hid⟩ := ChartData.exists_minor_cover ((W x.1).Tc x.2.1) hn _
        (hG.P x.2.2).conormalInj
      exact ⟨Pm, fun s i => by simp only [hF s, Fin.addCases_right],
        _, _, _, u, pow_pos (Nat.factorial_pos m) K', hid⟩
  have hheads : ∀ k τ j s i, (Pm (k, τ, j) s).F (Fin.natAdd m (Fin.castAdd l i)) =
      headF (W k).ã (Fin.natAdd m (Fin.castAdd l i)) := fun k τ j s i => by
    rw [(hPm (k, τ, j)).1 s i, (W k).hTx τ, headF_head]
    simp [yZ]
  -- the opens
  let ι := Fin hG.K ⊕ (Fin C.n × Fin kc × Fin hG.K) ⊕
    (Fin C.n × RowIdx (m + (kc + l)) ((kc + l) - kc) × Fin hG.K × ChartData.MinorIdx (m := m) (n := kc + l) G)
  let cond : ι → Pt (QR GR ε) → Prop := Sum.elim
    (fun j P => qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε P) ((hG.P j).h * ε₀) ≠ 0)
    (Sum.elim
      (fun x P => qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε P)
        ((hG.P x.2.2).h * ((W x.1).γ * (W x.1).ã x.2.1)) ≠ 0)
      (fun x P => qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε P)
          ((Pm (x.1, x.2.1, x.2.2.1) x.2.2.2).h * ((W x.1).β * ((W x.1).γ * (W x.1).gt))) ≠ 0 ∧
        ∀ i, qHom (A := A) G e (ptR (A := A) G e gZ δ GR hGR ε P)
          ((Pm (x.1, x.2.1, x.2.2.1) x.2.2.2).F (Fin.natAdd m (Fin.castAdd l i))) = 0))
  have hok : ∀ o, OpenOK GR ε (cond o) := by
    rintro (j | ⟨k, q, j⟩ | ⟨k, τ, j, s⟩)
    · exact laurent_ok G e gZ δ GR hGR ε (hG.P j) hδ ε₀ Pt₀
        (rowsL_mem_of_eq G gZ δ hGGR (hG.P j).eqmem d ε₀ Pt₀ hL₀)
    · exact laurent_ok G e gZ δ GR hGR ε (hG.P j) hδ _ _
        (rowsL_mem_of_eq G gZ δ hGGR (hG.P j).eqmem d _ _ (hLh k q))
    · have hh := hheads k τ j s
      exact weighted_ok G e gZ δ GR hGR ε (C.D k) (hkn k) (hCk k) hd (W k).s (W k).a (W k).ha
        (W k).Dq (W k).hDq (Pm (k, τ, j) s) (fun i => by rw [hh, headF_head]; exact (W k).hã i)
        (W k).wf (W k).hwf inst₁ inst₂ inst₃ (W k).γ (W k).β (W k).gt (W k).cγ (W k).cg (W k).N
        (W k).hγA (W k).hgtA (W k).P (W k).Q (fun i => by rw [hh]; exact (W k).hP i)
        (fun j' => by rw [evW_congr G e hh]; exact (W k).hy j')
        (rowsW_mem_of_heads G hGGR (Pm (k, τ, j) s).eqmem hh _ _ _ _ _ (hWr k))
  have henum : ∃ (J : ℕ) (f : Fin J → ι), ∀ o, ∃ k, f k = o := by
    obtain ⟨J, f, hf⟩ := exists_fin_surj (Finset.univ : Finset ι)
    exact ⟨J, f, fun o => hf o (Finset.mem_univ o)⟩
  -- 3. the point argument
  have hcov : ∀ P, ∃ o, cond o P := by
    intro P
    set q := ptR (A := A) G e gZ δ GR hGR ε P with hqdef
    have := algebraRat.charZero q.L
    have hqH : ∀ x, qHom (A := A) G e q x = q.z (toAZ G e x) := fun x => rfl
    obtain ⟨j, hj⟩ := SmoothCert.exists_piece_ne G e hG q
    rcases q.dec (q.z C.i) with hi0 | hi
    · obtain ⟨k, hgk⟩ := exists_ne_of_one q C.i C.f (fun k => (C.D k).g) C.one hi0
      have hgk' : q.z (C.D k).g ≠ 0 := hgk
      have hγ : qHom G e q (W k).γ ≠ 0 := by
        rw [hqH, (W k).hγA]
        exact natCast_mul_ne q (W k).hcγ (by rw [map_pow]; exact pow_ne_zero _ hgk')
      rcases fin_forall_or_exists (A := fun i => qHom G e q ((W k).ã i) = 0)
          (B := fun i => qHom G e q ((W k).ã i) ≠ 0) (fun i => q.dec _) with hall | ⟨i, hi'⟩
      · have ha0 : ∀ i, q.z ((W k).a (ιk (hkn k) i)) = 0 := fun i => by
          have h := hall i
          rw [hqH, (W k).hã, map_mul, map_natCast] at h
          exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 ((W k).hDq i).ne')
        obtain ⟨τ, hτ⟩ := exists_ne_of_part q (C.D k).g (W k).M (W k).βτ
          (fun τ => toAZ G e ((W k).Tc τ).c) (W k).ω (fun i => (W k).a (ιk (hkn k) i))
          (W k).hpart hgk' ha0
        obtain ⟨N, a, c, u, hN, hid⟩ := (hPm (k, τ, j)).2
        obtain ⟨s, hs⟩ := exists_ne_of_cover G e q hN _ u (fun s => (Pm (k, τ, j) s).h) hid (by
          rw [map_mul, map_pow, map_pow, map_pow]
          exact mul_ne_zero (pow_ne_zero _ hτ) (pow_ne_zero _ (pow_ne_zero _ hj)))
        refine ⟨Sum.inr (Sum.inr (k, τ, j, s)), ?_, fun i => ?_⟩
        · show qHom G e q _ ≠ 0
          rw [map_mul, map_mul, map_mul]
          refine mul_ne_zero hs (mul_ne_zero ?_ (mul_ne_zero hγ ?_))
          · rw [hqH, (W k).hβA]
            exact natCast_mul_ne q (W k).hcβ (by rw [map_pow]; exact pow_ne_zero _ hgk')
          · rw [hqH, (W k).hgtA]
            exact natCast_mul_ne q (W k).hcg hgk'
        · show qHom G e q _ = 0
          rw [hheads k τ j s i, headF_head]
          exact hall i
      · refine ⟨Sum.inr (Sum.inl (k, i, j)), ?_⟩
        show qHom G e q _ ≠ 0
        rw [map_mul, map_mul]
        exact mul_ne_zero hj (mul_ne_zero hγ hi')
    · refine ⟨Sum.inl j, ?_⟩
      show qHom G e q _ ≠ 0
      rw [map_mul]
      refine mul_ne_zero hj ?_
      rw [hqH, hε₀]
      exact natCast_mul_ne q hc₀ (by rw [map_pow]; exact pow_ne_zero _ hi)
  -- 4. gluing
  exact smoothCert_of_opens GR ε cond hok henum hcov

end BezoutCounterexample.Principalization
