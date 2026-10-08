import BezoutCounterexample.Principalization.MaxInvPos
import BezoutCounterexample.Principalization.Points
import BezoutCounterexample.Principalization.MaxInvPtDef

/-!
# The maximal invariant is attained at an explicit point (D3.5, leaf)

`IsMaxInv I v₀` (MaxInvPos) is attained at some maximal ideal; `exists_maxInv_pos` takes it from
the certificates of the positive cover, which are built at explicit points (`ExplicitNS`). Keeping
the point gives the attainment at an explicit point, which the point forms of the length bound
(`StarC.eq_zero_pt`, StarPt) and of the support bound need:

* `CertGenPt`, `one_mem_certPt_pos`, `certPt_min_pos`: `CertGen`, `one_mem_cert_pos`,
  `cert_min_pos` with the witness an explicit point;
* `exists_isMaxInv_pt`: `∃ v₀, IsMaxInvPt I v₀ ∧ ∃ q : Pt A, I ≤ q.ker ∧ InvAt I q.ker v₀`;
* `IsMaxInv.exists_pt`: every maximal invariant is attained at an explicit point (uniqueness).

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- A certified element whose certificate is attained at an explicit point. -/
def CertGenPt (I : Ideal A) (g : A) : Prop :=
  ∃ v : ℕ → ℚ, (∃ q : Pt A, I ≤ q.ker ∧ g ∉ q.ker ∧ InvAt I q.ker v) ∧
    ∀ q' : Pt A, g ∉ q'.ker → ∀ v', InvAt I q'.ker v' → toLex v ≤ toLex v'

/-- **The cover by point certificates, positively.** -/
theorem one_mem_certPt_pos {I : Ideal A} (hI : I ≠ ⊥) (gens : List A) (hgens : I = lspan gens)
    (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
    (hNS : ExplicitNS A)
    (hdec : ∀ l : List A, (1 : A) ∈ I ⊔ lspan l ∨ (1 : A) ∉ I ⊔ lspan l)
    (hN : IndNoeth (A ⧸ I)) :
    ∃ l : List A, (∀ g ∈ l, CertGenPt I g) ∧ (1 : A) ∈ I ⊔ lspan l :=
  exists_cover I hN (CertGenPt I) hdec fun l _ hl1 => by
    obtain ⟨L, _, _, _, z, hzd, hz⟩ := hNS (gens ++ l) fun h => hl1 (lspan_append_le hgens h)
    let q : Pt A := ⟨L, z, hzd⟩
    have hle : I ⊔ lspan l ≤ q.ker := sup_le_ker hgens z hz
    have hIq : I ≤ q.ker := le_sup_left.trans hle
    -- D3.8 (A): invariant and semicontinuity at the point (`exists_invAt_semicont_ptL`)
    obtain ⟨v, hv, g, hg, hbound⟩ := exists_invAt_semicont_ptL hI gens hgens hchart q hIq
    exact ⟨g, ⟨v, ⟨q, hIq, hg, hv⟩, hbound⟩, fun h => hg (hle h)⟩

/-- **The minimum over point certificates.** -/
theorem certPt_min_pos {I : Ideal A} {N : ℕ}
    (hb : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0) :
    ∀ (n : ℕ) (g : Fin (n + 1) → A), (∀ k, CertGenPt I (g k)) →
    ∃ v₀ : ℕ → ℚ, (∃ q : Pt A, I ≤ q.ker ∧ InvAt I q.ker v₀) ∧
      ∀ q : Pt A, ¬ (∀ k, g k ∈ q.ker) → ∀ v, InvAt I q.ker v →
        ¬ toLex v < toLex v₀ := by
  intro n
  induction n with
  | zero =>
    intro g hg
    obtain ⟨v₂, ⟨q₂, hI₂, -, hv₂⟩, B₂⟩ := hg 0
    refine ⟨v₂, ⟨q₂, hI₂, hv₂⟩, fun q hn v hv hlt => ?_⟩
    refine (fun h0 : g 0 ∉ q.ker => lt_irrefl _ (hlt.trans_le (B₂ q h0 v hv))) fun h0 => hn ?_
    intro k
    rwa [Fin.fin_one_eq_zero k]
  | succ n ih =>
    intro g hg
    obtain ⟨v₂, ⟨q₂, hI₂, -, hv₂⟩, B₂⟩ := hg 0
    obtain ⟨v₁, ⟨q₁, hI₁, hv₁⟩, bnd₁⟩ := ih (fun k => g k.succ) (fun k => hg k.succ)
    have hcomb : ∀ (q : Pt A), ¬ (∀ k, g k ∈ q.ker) → ¬¬ (g 0 ∈ q.ker) →
        ¬¬ (∀ k : Fin (n + 1), g k.succ ∈ q.ker) → False := fun q hn h0 hr =>
      h0 fun h0 => hr fun hr => hn fun k => Fin.cases h0 hr k
    rcases lex_total_bounded (hb q₁.ker v₁ hv₁) (hb q₂.ker v₂ hv₂) with h12 | h21
    · refine ⟨v₁, ⟨q₁, hI₁, hv₁⟩, fun q hn v hv hlt => hcomb q hn ?_ ?_⟩
      · exact fun h0 => lt_irrefl _ ((hlt.trans_le h12).trans_le (B₂ q h0 v hv))
      · exact fun hr => bnd₁ q hr v hv hlt
    · refine ⟨v₂, ⟨q₂, hI₂, hv₂⟩, fun q hn v hv hlt => hcomb q hn ?_ ?_⟩
      · exact fun h0 => lt_irrefl _ (hlt.trans_le (B₂ q h0 v hv))
      · exact fun hr => bnd₁ q hr v hv (hlt.trans_le h21)

/-- **The maximal invariant exists and is attained at an explicit point.** -/
theorem exists_isMaxInv_pt (hp : HasPres A) {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤)
    {N : ℕ} (hN : ChartDim A N) (gens : List A) (hgens : I = lspan gens) :
    ∃ v₀, IsMaxInvPt I v₀ ∧ ∃ q : Pt A, I ≤ q.ker ∧ InvAt I q.ker v₀ := by
  -- D3.8 (A): the charts from the certificate; bounds at explicit points
  have hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ,
      Nonempty (Chart (Localization.Away f) n) := fun p => by
    obtain ⟨f, hf, hc⟩ := hN.exists_chart_away p
    exact ⟨f, hf, N, hc⟩
  have hdec : ∀ l : List A, (1 : A) ∈ I ⊔ lspan l ∨ (1 : A) ∉ I ⊔ lspan l := fun l => by
    rw [hgens, ← lspan_append_eq]; exact (HasPres.mem_dec hp) _ 1
  obtain ⟨l, hl, hcov⟩ := one_mem_certPt_pos hI gens hgens hchart (explicitNS_of_hasPres hp) hdec
    (indNoeth_quotient_of_hasPres hp I)
  obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 hcov
  rcases l with _ | ⟨g₀, l⟩
  · exfalso
    have hy0 : y = 0 := by
      have : lspan ([] : List A) = ⊥ := by simp [lspan]
      rw [this] at hy; exact (Submodule.mem_bot A).1 hy
    rw [hy0, add_zero] at hiy
    exact hItop ((Ideal.eq_top_iff_one I).2 (hiy ▸ hi))
  · let g : Fin (l.length + 1) → A := fun k => (g₀ :: l).get k
    have hg : ∀ k, CertGenPt I (g k) := fun k => hl _ (List.get_mem _ _)
    obtain ⟨v₀, ⟨q₀, hI₀, hv₀⟩, bnd⟩ := certPt_min_pos (fun 𝔪 _ v hv => invAt_bounded hN hv)
      l.length g hg
    have hmax : ∀ q : Pt A, I ≤ q.ker → ∀ v, InvAt I q.ker v →
        ¬ toLex v < toLex v₀ := fun q hI𝔪 v hv => bnd q (fun hall => by
      have hl𝔪 : lspan (g₀ :: l) ≤ q.ker := by
        rw [lspan, Ideal.span_le]
        intro x hx
        obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hx
        exact hall k
      exact (Pt.ker_isMaximal q).ne_top
        ((Ideal.eq_top_iff_one _).2 (hiy ▸ Ideal.add_mem _ (hI𝔪 hi) (hl𝔪 hy)))) v hv
    refine ⟨v₀, fun q hI𝔪 v hv => ?_, q₀, hI₀, hv₀⟩
    rcases lex_total_bounded (invAt_bounded hN hv₀) (invAt_bounded hN hv) with h | h
    · exact h
    · rcases h.lt_or_eq with hlt | heq
      · exact absurd hlt (hmax q hI𝔪 v hv)
      · exact heq.ge

/-- **Every maximal invariant is attained at an explicit point.** -/
theorem IsMaxInv.exists_pt (hp : HasPres A) {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤)
    {N : ℕ} (hN : ChartDim A N) (gens : List A) (hgens : I = lspan gens) {v : ℕ → ℚ}
    (he : IsMaxInv I v) : ∃ q : Pt A, I ≤ q.ker ∧ InvAt I q.ker v := by
  -- classical (off the path): compare at the maximal ideal attaining `v` (`IsMaxInvPt.toMax`)
  obtain ⟨v₀, h₀, q₀, hI₀, hv₀⟩ := exists_isMaxInv_pt hp hI hItop hN gens hgens
  obtain ⟨⟨𝔪, h𝔪, hI𝔪, hv⟩, hb⟩ := he
  have : v = v₀ := toLex.injective (le_antisymm (hb q₀.ker hI₀ v₀ hv₀) (IsMaxInvPt.toMax h₀ 𝔪 hI𝔪 v hv))
  exact ⟨q₀, hI₀, this ▸ hv₀⟩

end BezoutCounterexample.Principalization
