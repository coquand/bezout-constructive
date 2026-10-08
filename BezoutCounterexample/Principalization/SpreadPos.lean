import BezoutCounterexample.Principalization.Spread
import BezoutCounterexample.Principalization.StepRunPos

/-!
# Spreading of Method-1 runs, positively (D3.4 (b), leaf)

`spread_run` (Spread) branches on admissibility by `by_cases` (twice), takes the step from the
classical `MC.SA.step_run`, and spreads the admissibility containment through
`Loc.spread_ideal_le` (`classical` for the finset of generators of `I.FG`). Here, at a maximal
ideal `𝔪` with a decided residue field of `A_𝔪` (`hdec`; at a point: `Pt.dec_local`),
`[Fact (PolyIndNoeth A_𝔪)]` and explicit generators `I = (l)`:

* `Loc.spread_ideal_le_list`: `spread_ideal_le` by induction on the list of generators;
* `spread_adm_pos`: `spread_adm` over it;
* `spread_run_pos`: `spread_run`, with the branches decided by `MC.adm_or_witness` and the steps
  by `MC.SA.step_run_pos`. Same conclusion.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalization IsLocalRing Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A]

namespace Loc

variable {M N : Submonoid A}

omit [IsDomain A] [Algebra ℚ A] in
/-- **Spreading containment of an extended ideal**, for an ideal given by a list of generators. -/
lemma spread_ideal_le_list (h : M ≤ N) (hN : N ≤ nonZeroDivisors A) (s : List A)
    (J : Ideal (Localization M))
    (hIJ : (lspan s).map (algebraMap A (Localization N)) ≤ J.map (map h)) :
    ∃ M', ∃ hE : Ext M N M',
      (lspan s).map (algebraMap A (Localization M')) ≤ J.map (map hE.le₁) := by
  have key : ∀ t : List A, (∀ a ∈ t, a ∈ s) → ∃ M', ∃ hE : Ext M N M', ∀ a ∈ t,
      algebraMap A (Localization M') a ∈ J.map (map hE.le₁) := by
    intro t
    induction t with
    | nil => exact fun _ => ⟨M, Ext.refl h, fun a ha => absurd ha List.not_mem_nil⟩
    | cons a t ih =>
      intro hts
      obtain ⟨M₁, hE₁, hmem₁⟩ := ih (fun x hx => hts x (List.mem_cons_of_mem _ hx))
      have ha : map hE₁.le₂ (algebraMap A (Localization M₁) a) ∈
          (J.map (map hE₁.le₁)).map (map hE₁.le₂) := by
        rw [Ideal.map_map, map_comp, map_algebraMap]
        exact hIJ (Ideal.mem_map_of_mem _ (Ideal.subset_span (hts a List.mem_cons_self)))
      obtain ⟨u, hu, hmem⟩ := spread_mem_map hE₁.le₂ hN _ _ ha
      have hE₂ := Ext.sup_powers hE₁.le₂ hu
      refine ⟨_, hE₁.trans hE₂, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [Ideal.map_map, map_comp, map_algebraMap] at hmem
        exact hmem
      · have := map_mem_map_trans hE₁.le₁ hE₂.le₁ J (hmem₁ x hx)
        rwa [map_algebraMap] at this
  obtain ⟨M', hE, hmem⟩ := key s fun _ h => h
  refine ⟨M', hE, ?_⟩
  rw [lspan, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  exact hmem a ha

end Loc

variable (𝔪 : Ideal A) [𝔪.IsMaximal] [Fact (PolyIndNoeth (Localization.AtPrime 𝔪))] {n : ℕ}
  (hdec : ∀ x : Localization.AtPrime 𝔪, x ∈ maximalIdeal (Localization.AtPrime 𝔪) ∨ IsUnit x)
  (I : Ideal A) (l : List A) (hl : I = lspan l)

omit [IsDomain A] [Fact (PolyIndNoeth (Localization.AtPrime 𝔪))] in
include hl in
/-- The generators of `I`, at `A_𝔪`. -/
lemma hlR : I.map (algebraMap A (Localization.AtPrime 𝔪)) =
    lspan (l.map (algebraMap A (Localization.AtPrime 𝔪))) := by
  rw [hl, lspan, lspan, Ideal.map_span]
  congr 1
  ext y
  simp

omit [Fact (PolyIndNoeth (Localization.AtPrime 𝔪))] in
include hl in
lemma spread_adm_pos {M : Submonoid A} (hM : M ≤ 𝔪.primeCompl) (c : Chart (Localization M) n)
    (e : Fin n → ℚ)
    (hadm : I.map (algebraMap A (Localization.AtPrime 𝔪)) ≤ (Loc.transport hM c).RF e 1) :
    ∃ M', ∃ hE : Loc.Ext M 𝔪.primeCompl M',
      I.map (algebraMap A (Localization M')) ≤ (Loc.transport hE.le₁ c).RF e 1 := by
  rw [← Loc.map_RF] at hadm
  subst hl
  obtain ⟨M', hE, hle⟩ := Loc.spread_ideal_le_list hM (Ideal.primeCompl_le_nonZeroDivisors 𝔪) l
    _ hadm
  exact ⟨M', hE, by rwa [← Loc.map_RF]⟩

include hdec hl in
/-- **Spreading of Method-1 runs, positively** (`spread_run` with the admissibility branches decided
by `MC.adm_or_witness` and the steps by `MC.SA.step_run_pos`). -/
theorem spread_run_pos :
    ∀ (d j : ℕ), n - j = d → ∀ (M : Submonoid A) (hM : M ≤ 𝔪.primeCompl)
      (c : Chart (Localization M) n) (e : Fin n → ℚ) (hc : (Loc.transport hM c).IsCentred)
      (hnn : ∀ i, 0 ≤ e i) (ha : Antitone e),
      MC.SA (I.map (algebraMap A (Localization.AtPrime 𝔪))) j
        ⟨Loc.transport hM c, e, hc, hnn, ha⟩ →
      ∃ M', ∃ hE : Loc.Ext M 𝔪.primeCompl M', ∃ (k : ℕ) (ck : Chart (Localization M') n)
        (ek : Fin n → ℚ),
        IsRun (I.map (algebraMap A (Localization M'))) j (Loc.transport hE.le₁ c) e k ck ek ∧
        I.map (algebraMap A (Localization M')) ≤ ck.RF ek 1 ∧
        (∀ i, ek i ≠ 0 ↔ (i : ℕ) < k) ∧ (∀ i, 0 ≤ ek i) ∧ Antitone ek ∧
        (Loc.transport hE.le₂ ck).IsCentred := by
  have hN : 𝔪.primeCompl ≤ nonZeroDivisors A := Ideal.primeCompl_le_nonZeroDivisors 𝔪
  intro d
  induction d with
  | zero =>
    intro j hj M hM c e hc hnn ha hSA
    rcases MC.adm_or_witness hdec _ (hlR 𝔪 I l hl)
        (⟨Loc.transport hM c, e, hc, hnn, ha⟩ : MC (Localization.AtPrime 𝔪) n)
      with hadm | ⟨f₀, hf₀, β₀, hβ₀, hlt₀⟩
    · obtain ⟨M', hE, hle⟩ := spread_adm_pos 𝔪 I l hl hM c e hadm
      exact ⟨M', hE, j, _, e, .refl _ _ _, hle, hSA.supp, hnn, ha,
        by rw [Loc.transport_trans]; exact hc⟩
    · obtain ⟨hjn, -⟩ := hSA.step_data_pos hdec _ (hlR 𝔪 I l hl) hf₀ hβ₀ hlt₀
      exact absurd hj (Nat.sub_ne_zero_of_lt hjn)
  | succ d ih =>
    intro j hj M hM c e hc hnn ha hSA
    set Jc := Loc.transport hM c with hJc
    rcases MC.adm_or_witness hdec _ (hlR 𝔪 I l hl)
        (⟨Jc, e, hc, hnn, ha⟩ : MC (Localization.AtPrime 𝔪) n)
      with hadm | ⟨f₀, hf₀, β₀, hβ₀, hlt₀⟩
    · obtain ⟨M', hE, hle⟩ := spread_adm_pos 𝔪 I l hl hM c e hadm
      exact ⟨M', hE, j, _, e, .refl _ _ _, hle, hSA.supp, hnn, ha,
        by rw [Loc.transport_trans]; exact hc⟩
    obtain ⟨hjn, f, hf, β, l, hl, hβl, hlam, hNt, hunit, hb, u, hu, hc', hnn', ha', hSA'⟩ :=
      hSA.step_run_pos hdec _ (hlR 𝔪 I l hl) hf₀ hβ₀ hlt₀
    -- spread `f`
    obtain ⟨M₁, hE₁, f₁, hf₁, hf₁m⟩ := Loc.spread_mem_ideal hM I hf
    set c₁ := Loc.transport hE₁.le₁ c
    have hJc₁ : Jc = Loc.transport hE₁.le₂ c₁ := by rw [Loc.transport_trans]
    -- spread the witness unit
    have hw : IsUnit (Loc.map hE₁.le₂ (c₁.D β f₁)) := by
      rw [← Loc.transport_D, ← hJc₁, hf₁m]; exact hunit
    obtain ⟨M₂, hE₂, hw₂⟩ := Loc.spread_isUnit hE₁.le₂ hN hw
    -- spread `u`
    obtain ⟨M₃, hE₃, u₃, hu₃m⟩ := Loc.spread_unit hE₂.le₂ hN u
    have h13 : M₁ ≤ M₃ := hE₂.le₁.trans hE₃.le₁
    set c₃ := Loc.transport h13 c₁ with hc₃
    set f₃ := Loc.map h13 f₁ with hf₃
    have hJc₃ : Jc = Loc.transport hE₃.le₂ c₃ := by rw [hc₃, Loc.transport_trans, hJc₁]
    have hf₃m : Loc.map hE₃.le₂ f₃ = f := by rw [hf₃, Loc.map_apply_comp, hf₁m]
    set γ := β - Finsupp.single l 1
    have hmapx : Loc.map hE₃.le₂ (c₃.Dv γ f₃) = Jc.Dv γ f := by
      rw [← Loc.transport_Dv, ← hJc₃, hf₃m]
    have hu₃ : c₃.d l (c₃.Dv γ f₃) = u₃ := by
      apply Loc.map_injective hE₃.le₂ hN
      rw [← Loc.transport_d, ← hJc₃, hmapx, hu, hu₃m]
    have hw₃ : IsUnit (c₃.D β f₃) := by
      have : c₃.D β f₃ = Loc.map hE₃.le₁ (Loc.map hE₂.le₁ (c₁.D β f₁)) := by
        rw [hc₃, hf₃, Loc.transport_D, Loc.map_apply_comp]
      rw [this]; exact hw₂.map _
    set C₃ := nextChart c₃ ⟨j, hjn⟩ l (c₃.Dv γ f₃) u₃ hu₃ with hC₃
    have hC₃N : Loc.transport hE₃.le₂ C₃ = nextChart Jc ⟨j, hjn⟩ l (Jc.Dv γ f) u hu := by
      rw [hC₃, Loc.transport_nextChart]
      refine Chart.eq_of_x (funext fun i => ?_)
      simp only [Principalization.nextChart, Chart.reindex_x]
      by_cases hi : Equiv.swap ⟨j, hjn⟩ l i = l
      · rw [hi, Chart.replace_x_self, Chart.replace_x_self, hmapx]
      · rw [Chart.replace_x_ne _ _ _ _ _ hi, Chart.replace_x_ne _ _ _ _ _ hi, hJc₃]
    have hcC : (Loc.transport hE₃.le₂ C₃).IsCentred := by rw [hC₃N]; exact hc'
    have hSA'' : MC.SA (I.map (algebraMap A (Localization.AtPrime 𝔪))) (j + 1)
        ⟨Loc.transport hE₃.le₂ C₃, nextE e j (nextW e j β), hcC, hnn', ha'⟩ := by
      have heq : (⟨Loc.transport hE₃.le₂ C₃, nextE e j (nextW e j β), hcC, hnn', ha'⟩ :
          MC (Localization.AtPrime 𝔪) n) = ⟨nextChart Jc ⟨j, hjn⟩ l (Jc.Dv γ f) u hu,
            nextE e j (nextW e j β), hc', hnn', ha'⟩ := MC.ext' hC₃N rfl
      rw [heq]; exact hSA'
    obtain ⟨M', hE', k, ck, ek, hrun, hadm', hsupp', hnn'', ha'', hcent⟩ :=
      ih (j + 1) (by rw [Nat.sub_succ, hj]; rfl) M₃ hE₃.le₂ C₃ _ hcC hnn' ha' hSA''
    have hE : Loc.Ext M 𝔪.primeCompl M' := hE₁.trans (hE₂.trans (hE₃.trans hE'))
    refine ⟨M', hE, k, ck, ek, ?_, hadm', hsupp', hnn'', ha'', hcent⟩
    -- the step over `M'⁻¹A`
    set c' := Loc.transport hE.le₁ c with hc'def
    have hc'3 : c' = Loc.transport hE'.le₁ c₃ := by
      rw [hc'def, hc₃, Loc.transport_trans, Loc.transport_trans]
    obtain ⟨f', hf'def⟩ : ∃ f', f' = Loc.map hE'.le₁ f₃ := ⟨_, rfl⟩
    have hf' : f' ∈ I.map (algebraMap A (Localization M')) := by
      have := Ideal.mem_map_of_mem (Loc.map hE'.le₁) (Ideal.mem_map_of_mem (Loc.map h13) hf₁)
      rw [Loc.map_map_algebraMap, Loc.map_map_algebraMap] at this
      rw [hf'def]; exact this
    have hmapx' : Loc.map hE'.le₁ (c₃.Dv γ f₃) = c'.Dv γ f' := by
      rw [hc'3, hf'def, Loc.transport_Dv hE'.le₁]
    have hu' : c'.d l (c'.Dv γ f') = ↑(Units.map (Loc.map hE'.le₁).toMonoidHom u₃) := by
      rw [← hmapx', hc'3, Loc.transport_d hE'.le₁, hu₃]; rfl
    have hw' : IsUnit (c'.D β f') := by
      rw [hc'3, hf'def, Loc.transport_D hE'.le₁]; exact hw₃.map _
    have hnext : nextChart c' ⟨j, hjn⟩ l (c'.Dv γ f') (Units.map (Loc.map hE'.le₁).toMonoidHom u₃)
        hu' = Loc.transport hE'.le₁ C₃ := by
      rw [hC₃, Loc.transport_nextChart]
      refine Chart.eq_of_x (funext fun i => ?_)
      simp only [Principalization.nextChart, Chart.reindex_x]
      by_cases hi : Equiv.swap ⟨j, hjn⟩ l i = l
      · rw [hi, Chart.replace_x_self, Chart.replace_x_self, hmapx']
      · rw [Chart.replace_x_ne _ _ _ _ _ hi, Chart.replace_x_ne _ _ _ _ _ hi, hc'3]
    refine IsRun.step hjn f' hf' β l hl hβl hlam hNt hw' hb _ hu' ?_
    rw [hnext]
    exact hrun

end BezoutCounterexample.Principalization
