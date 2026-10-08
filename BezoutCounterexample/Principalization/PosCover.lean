import BezoutCounterexample.Principalization.Components
import BezoutCounterexample.Constructive.PosCover
import BezoutCounterexample.Constructive.LexDec
import BezoutCounterexample.MarkedCenter
import BezoutCounterexample.Principalization.ChartDim

/-!
# Positive covers from the Nullstellensatz with explicit points (leaf; `bezout-positive.tex` §1)

`Cover.lean` obtains its covers only under `¬¬` (`NNMax`, `not_not_one_mem_cert(C)`), and
`Components.lean` uses the Jacobson property in `¬¬`-form (`JacS`). Here both are replaced by the
explicit form of the Nullstellensatz together with bar induction (`Constructive.exists_cover`).

* `ExplicitNS A`: for a finite list `l` with `1 ∉ (l)` there is a `ℚ`-algebra map `z : A → L` into
  a finite field extension `L/ℚ` with decidable equality, vanishing on `l`. Its kernel is maximal
  (`ker_isMaximal`: a finite-dimensional `ℚ`-domain is a field). The classical source is
  `explicitNS_of_classical` (`A ⧸ 𝔪` for a Zorn maximal ideal, which is finite over `ℚ` by
  Zariski); the constructive source is the effective Nullstellensatz.
* `one_mem_cert_pos`: the cover `1 ∈ I ⊔ Cert I` holds positively, given `ExplicitNS A`, a
  presentation `I = (gens)`, a decision (G) of `1 ∈ I + (l)`, and `IndNoeth (A ⧸ I)`.
  It replaces `not_not_one_mem_cert` (and `NNMax`).
* `one_mem_certC_pos`: the same for the cover of `V(𝔭)` by local data, replacing
  `not_not_one_mem_certC`.
* `jacS_explicit`: `JacS` for an explicitly generated prime `p = (pgens)`, from `ExplicitNS A[X]`
  (a point of `V(p) ∩ D(f)` is a point of `V(p, 1 - f X)`) and a decision of `f ∈ p`.

The remaining `¬¬` of `exists_maxInv_C` is only the totality of the lexicographic order.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

/-- **The Nullstellensatz with explicit points**: a finite list not generating `(1)` vanishes at
a point with values in a finite extension of `ℚ` with decidable equality. -/
def ExplicitNS (A : Type) [CommRing A] [Algebra ℚ A] : Prop :=
  ∀ l : List A, (1 : A) ∉ lspan l →
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L) (z : A →ₐ[ℚ] L),
      (∀ x : L, x = 0 ∨ x ≠ 0) ∧ ∀ x ∈ l, z x = 0

/-- The kernel of a point is maximal: its image is a finite-dimensional `ℚ`-domain. -/
theorem ker_isMaximal {A : Type} [CommRing A] [Algebra ℚ A] {L : Type} [Field L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] (z : A →ₐ[ℚ] L) : (RingHom.ker z).IsMaximal := by
  let _ : Algebra A L := z.toRingHom.toAlgebra
  have : IsScalarTower ℚ A L := IsScalarTower.of_algebraMap_eq fun r => (z.commutes r).symm
  have : Algebra.IsIntegral ℚ L := Algebra.IsIntegral.of_finite ℚ L
  have : Algebra.IsIntegral A L := Algebra.IsIntegral.tower_top ℚ
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A L)
    (Algebra.isIntegral_def.1 inferInstance) (⊥ : Ideal L)
  have hk : (⊥ : Ideal L).comap (algebraMap A L) = RingHom.ker z := by
    ext x; simp [RingHom.mem_ker]; rfl
  rwa [hk] at h

/-- Classical source of `ExplicitNS` (Zorn and Zariski's lemma). -/
theorem explicitNS_of_classical (A : Type) [CommRing A] [Algebra ℚ A] [Algebra.FiniteType ℚ A] :
    ExplicitNS A := by
  classical
  intro l hl
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (lspan l) fun h => hl (h ▸ trivial)
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : IsJacobsonRing ℚ := inferInstance
  haveI : Module.Finite ℚ (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ 𝔪)
  exact ⟨A ⧸ 𝔪, inferInstance, inferInstance, inferInstance, Ideal.Quotient.mkₐ ℚ 𝔪,
    fun x => em _, fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.subset_span hx))⟩

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- `I ⊔ (l)` lies in the kernel of a point vanishing on `gens ++ l`. -/
lemma sup_le_ker {I : Ideal A} {gens l : List A} (hgens : I = lspan gens) {L : Type} [Field L]
    [Algebra ℚ L] (z : A →ₐ[ℚ] L) (hz : ∀ x ∈ gens ++ l, z x = 0) :
    I ⊔ lspan l ≤ RingHom.ker z := by
  refine sup_le ?_ ?_
  · rw [hgens, lspan, Ideal.span_le]
    intro x hx; exact hz x (List.mem_append_left _ hx)
  · rw [lspan, Ideal.span_le]
    intro x hx; exact hz x (List.mem_append_right _ hx)

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
lemma lspan_append_le {I : Ideal A} {gens l : List A} (hgens : I = lspan gens) :
    lspan (gens ++ l) ≤ I ⊔ lspan l := by
  rw [lspan, Ideal.span_le]
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact Ideal.mem_sup_left (hgens ▸ Ideal.subset_span h)
  · exact Ideal.mem_sup_right (Ideal.subset_span h)

omit [IsNoetherianRing A] in
/-- **The certified cover, positively.** -/
theorem one_mem_cert_pos {I : Ideal A} (hI : I ≠ ⊥) (gens : List A) (hgens : I = lspan gens)
    (hNS : ExplicitNS A)
    (hdec : ∀ l : List A, (1 : A) ∈ I ⊔ lspan l ∨ (1 : A) ∉ I ⊔ lspan l)
    (hN : IndNoeth (A ⧸ I)) : (1 : A) ∈ I ⊔ Cert I := by
  obtain ⟨l, hl, h1⟩ := exists_cover I hN (CertGen I) hdec fun l _ hl1 => by
    obtain ⟨L, _, _, _, z, -, hz⟩ := hNS (gens ++ l) fun h => hl1 (lspan_append_le hgens h)
    have hmax := ker_isMaximal z
    have hle := sup_le_ker hgens z hz
    have hI𝔪 : I ≤ RingHom.ker z := le_sup_left.trans hle
    obtain ⟨v, hv⟩ := exists_invAt hI _ hI𝔪
    obtain ⟨g, hg, hbound⟩ := invAt_semicont hI _ hI𝔪 hv
    exact ⟨g, ⟨v, ⟨_, hmax, hI𝔪, hg, hv⟩, hbound⟩, fun h => hg (hle h)⟩
  refine (sup_le_sup_left ?_ I) h1
  rw [lspan, Ideal.span_le]
  intro g hg; exact Ideal.subset_span (hl g hg)

omit [IsNoetherianRing A] in
/-- **The maximal invariant exists** from the positive cover; the remaining `¬¬` is only the
totality of the lexicographic order (`nn_le_total`). -/
theorem exists_maxInv_E {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤) (gens : List A)
    (hgens : I = lspan gens) (hNS : ExplicitNS A)
    (hdec : ∀ l : List A, (1 : A) ∈ I ⊔ lspan l ∨ (1 : A) ∉ I ⊔ lspan l)
    (hN : IndNoeth (A ⧸ I)) :
    ¬¬ ∃ v₀ : ℕ → ℚ, (∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), I ≤ 𝔪 ∧ InvAt I 𝔪 v₀) ∧
      ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → ¬ toLex v < toLex v₀ :=
  exists_maxInv_C hItop (one_mem_cert_pos hI gens hgens hNS hdec hN)

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- Invariants vanish beyond the size of a chart at any prime: chart sizes are constant on a
domain (`chart_card_eq_of_domain`). -/
lemma invAt_bounded_of_chart {𝔭₀ : Ideal A} [𝔭₀.IsPrime] {N : ℕ}
    (c₀ : Chart (Localization.AtPrime 𝔭₀) N) {I 𝔪 : Ideal A} [𝔪.IsMaximal] {v : ℕ → ℚ}
    (hv : InvAt I 𝔪 v) : ∀ i, N ≤ i → v i = 0 := by
  obtain ⟨n, e, ⟨⟨J, -, -⟩, -⟩, rfl⟩ := hv
  have hn : N = n := chart_card_eq_of_domain 𝔭₀ 𝔪 c₀ J.c
  intro i hi
  simp only [ext0, dif_neg (show ¬ i < n by omega)]

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- Invariants vanish beyond the chart size `N` (`ChartDim.card_eq`). -/
lemma invAt_bounded {N : ℕ} (hN : ChartDim A N) {I 𝔪 : Ideal A} [𝔪.IsMaximal] {v : ℕ → ℚ}
    (hv : InvAt I 𝔪 v) : ∀ i, N ≤ i → v i = 0 := by
  obtain ⟨n, e, ⟨⟨J, -, -⟩, -⟩, rfl⟩ := hv
  have hn : N = n := (hN.card_eq J.c).symm
  intro i hi
  simp only [ext0, dif_neg (show ¬ i < n by omega)]

omit [IsNoetherianRing A] in
/-- The minimum over a nonempty finite family of certified elements, **positively**: the
lexicographic comparisons are decided (`lex_total_bounded`, supports bounded by `dim A`). -/
theorem cert_min_pos {I : Ideal A} {N : ℕ}
    (hb : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0) :
    ∀ (n : ℕ) (g : Fin (n + 1) → A), (∀ k, CertGen I (g k)) →
    ∃ v₀ : ℕ → ℚ, (∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), I ≤ 𝔪 ∧ InvAt I 𝔪 v₀) ∧
      ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], ¬ (∀ k, g k ∈ 𝔪) → ∀ v, InvAt I 𝔪 v →
        ¬ toLex v < toLex v₀ := by
  intro n
  induction n with
  | zero =>
    intro g hg
    obtain ⟨v₂, ⟨𝔪₂, h𝔪₂, hI₂, -, hv₂⟩, B₂⟩ := hg 0
    refine ⟨v₂, ⟨𝔪₂, h𝔪₂, hI₂, hv₂⟩, fun 𝔪 _ hn v hv hlt => ?_⟩
    refine (fun h0 : g 0 ∉ 𝔪 => lt_irrefl _ (hlt.trans_le (B₂ 𝔪 h0 v hv))) fun h0 => hn ?_
    intro k
    rwa [Fin.fin_one_eq_zero k]
  | succ n ih =>
    intro g hg
    obtain ⟨v₂, ⟨𝔪₂, h𝔪₂, hI₂, -, hv₂⟩, B₂⟩ := hg 0
    obtain ⟨v₁, ⟨𝔪₁, h𝔪₁, hI₁, hv₁⟩, bnd₁⟩ := ih (fun k => g k.succ) (fun k => hg k.succ)
    have hcomb : ∀ (𝔪 : Ideal A), ¬ (∀ k, g k ∈ 𝔪) → ¬¬ (g 0 ∈ 𝔪) →
        ¬¬ (∀ k : Fin (n + 1), g k.succ ∈ 𝔪) → False := fun 𝔪 hn h0 hr =>
      h0 fun h0 => hr fun hr => hn fun k => Fin.cases h0 hr k
    rcases lex_total_bounded (hb 𝔪₁ v₁ hv₁) (hb 𝔪₂ v₂ hv₂) with h12 | h21
    · refine ⟨v₁, ⟨𝔪₁, h𝔪₁, hI₁, hv₁⟩, fun 𝔪 _ hn v hv hlt => hcomb 𝔪 hn ?_ ?_⟩
      · exact fun h0 => lt_irrefl _ ((hlt.trans_le h12).trans_le (B₂ 𝔪 h0 v hv))
      · exact fun hr => bnd₁ 𝔪 hr v hv hlt
    · refine ⟨v₂, ⟨𝔪₂, h𝔪₂, hI₂, hv₂⟩, fun 𝔪 _ hn v hv hlt => hcomb 𝔪 hn ?_ ?_⟩
      · exact fun h0 => lt_irrefl _ (hlt.trans_le (B₂ 𝔪 h0 v hv))
      · exact fun hr => bnd₁ 𝔪 hr v hv (hlt.trans_le h21)

/-- **The maximal invariant exists, positively** (no `¬¬`): positive cover plus decided
lexicographic comparisons. -/
theorem exists_maxInv_pos {I : Ideal A} (hI : I ≠ ⊥) (hItop : I ≠ ⊤) {N : ℕ}
    (hN : ChartDim A N) (gens : List A) (hgens : I = lspan gens) (hNS : ExplicitNS A)
    (hdec : ∀ l : List A, (1 : A) ∈ I ⊔ lspan l ∨ (1 : A) ∉ I ⊔ lspan l)
    (hNq : IndNoeth (A ⧸ I)) :
    ∃ v₀ : ℕ → ℚ, (∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal), I ≤ 𝔪 ∧ InvAt I 𝔪 v₀) ∧
      ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → ¬ toLex v < toLex v₀ := by
  have hcov := one_mem_cert_pos hI gens hgens hNS hdec hNq
  obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 hcov
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hy
  cases n with
  | zero =>
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hfg
    rw [← hfg, add_zero] at hiy
    exact absurd ((Ideal.eq_top_iff_one I).2 (hiy ▸ hi)) hItop
  | succ n =>
    obtain ⟨v₀, att, bnd⟩ := cert_min_pos (fun 𝔪 _ v hv => invAt_bounded hN hv) n
      (fun k => (g k).1) (fun k => (g k).2)
    refine ⟨v₀, att, fun 𝔪 h𝔪 hI𝔪 v hv => bnd 𝔪 (fun hall => ?_) v hv⟩
    have h1 : (1 : A) ∈ 𝔪 := by
      rw [← hiy, ← hfg]
      exact Ideal.add_mem _ (hI𝔪 hi)
        (Ideal.sum_mem _ fun k _ => by rw [smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hall k))
    exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).2 h1)

/-- **The cover of `V(𝔭)` by local data, positively.** -/
theorem one_mem_certC_pos {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} {𝔭 : Ideal A}
    (hZ : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 → I ≤ 𝔪 ∧ InvAt I 𝔪 v₀)
    (pgens : List A) (hpgens : 𝔭 = lspan pgens) (hNS : ExplicitNS A)
    (hdec : ∀ l : List A, (1 : A) ∈ 𝔭 ⊔ lspan l ∨ (1 : A) ∉ 𝔭 ⊔ lspan l)
    (hN : IndNoeth (A ⧸ 𝔭)) : (1 : A) ∈ 𝔭 ⊔ Ideal.span {g | CertC I v₀ 𝔭 g} := by
  obtain ⟨l, hl, h1⟩ := exists_cover 𝔭 hN (CertC I v₀ 𝔭) hdec fun l _ hl1 => by
    obtain ⟨L, _, _, _, z, -, hz⟩ := hNS (pgens ++ l) fun h => hl1 (lspan_append_le hpgens h)
    have hmax := ker_isMaximal z
    have hle := sup_le_ker hpgens z hz
    have h𝔭𝔪 : 𝔭 ≤ RingHom.ker z := le_sup_left.trans hle
    have hZ' := hZ _ h𝔭𝔪
    obtain ⟨D⟩ := LocData.nonempty hI _ hZ'.1 hZ'.2
    exact ⟨D.g, ⟨_, hmax, h𝔭𝔪, D, rfl⟩, fun h => D.hg (hle h)⟩
  refine (sup_le_sup_left ?_ 𝔭) h1
  rw [lspan, Ideal.span_le]
  intro g hg; exact Ideal.subset_span (hl g hg)

section Jacobson

variable {A : Type} [CommRing A] [Algebra ℚ A]

omit [Algebra ℚ A] in
open Polynomial in
/-- If `f ∉ p` for a prime `p`, then `p A[X] + (1 - f X) ≠ (1)`: map to `(A ⧸ p)[1/f]`, `X ↦ 1/f`. -/
lemma one_not_mem_rabinowitsch {p : Ideal A} [hp : p.IsPrime] {pgens : List A}
    (hpg : p = lspan pgens) {f : A} (hf : f ∉ p) :
    (1 : A[X]) ∉ lspan (pgens.map C ++ [1 - C f * X]) := by
  intro h1
  set B := A ⧸ p
  set Lc := Localization.Away (Ideal.Quotient.mk p f)
  let u : Lc := IsLocalization.Away.invSelf (Ideal.Quotient.mk p f)
  let φ : A[X] →+* Lc := eval₂RingHom ((algebraMap B Lc).comp (Ideal.Quotient.mk p)) u
  have hker : lspan (pgens.map C ++ [1 - C f * X]) ≤ RingHom.ker φ := by
    rw [lspan, Ideal.span_le]
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      have : Ideal.Quotient.mk p a = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (hpg ▸ Ideal.subset_span ha)
      simp [φ, RingHom.mem_ker, this]
    · rw [List.mem_singleton] at hx
      subst hx
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, map_mul, φ,
        coe_eval₂RingHom, eval₂_C, eval₂_X, RingHom.coe_comp, Function.comp_apply]
      rw [IsLocalization.Away.mul_invSelf, sub_self]
  have h10 : (1 : Lc) = 0 := by
    have := hker h1
    rwa [RingHom.mem_ker, map_one] at this
  have h2 : algebraMap B Lc 1 = algebraMap B Lc 0 := by rw [map_one, map_zero, h10]
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers (Ideal.Quotient.mk p f)) Lc).1 h2
  simp only [mul_one, mul_zero] at hn
  apply hf
  have : f ^ n ∈ p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]; exact hn
  exact hp.mem_of_pow_mem n this

open Polynomial in
/-- **`JacS` for an explicitly generated prime**, from the explicit Nullstellensatz on `A[X]` and
a decision of `f ∈ p`. -/
theorem jacS_explicit (hNSX : ExplicitNS A[X]) (p : Ideal A) [p.IsPrime] (pgens : List A)
    (hpg : p = lspan pgens) (f : A) (hdec : f ∈ p ∨ f ∉ p)
    (hf : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], p ≤ 𝔪 → ¬¬ f ∈ 𝔪) : f ∈ p := by
  rcases hdec with h | h
  · exact h
  exfalso
  obtain ⟨L, _, _, _, z', -, hz'⟩ := hNSX _ (one_not_mem_rabinowitsch hpg h)
  let z : A →ₐ[ℚ] L := z'.comp ((Algebra.ofId A A[X]).restrictScalars ℚ)
  have hzC : ∀ a, z a = z' (C a) := fun a => rfl
  have := ker_isMaximal z
  have hpz : p ≤ RingHom.ker z := by
    rw [hpg, lspan, Ideal.span_le]
    intro a ha
    rw [SetLike.mem_coe, RingHom.mem_ker, hzC]
    exact hz' _ (List.mem_append_left _ (List.mem_map.2 ⟨a, ha, rfl⟩))
  have hfz : f ∉ RingHom.ker z := by
    rw [RingHom.mem_ker, hzC]
    intro h0
    have h1 := hz' (1 - C f * X) (List.mem_append_right _ (List.mem_singleton_self _))
    rw [map_sub, map_one, map_mul, h0, zero_mul, sub_zero] at h1
    exact one_ne_zero h1
  exact hf _ hpz hfz

end Jacobson

end BezoutCounterexample.Principalization
