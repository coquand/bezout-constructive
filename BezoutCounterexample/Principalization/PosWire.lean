import BezoutCounterexample.Principalization.ChartCover
import BezoutCounterexample.Constructive.Nullstellensatz
import BezoutCounterexample.Constructive.PresContract
import BezoutCounterexample.Principalization.MaxInvPtDef

/-!
# Wiring (G1), (G2) into `exists_chartCover_pos` (option 2, M4; leaf, read-only on ChartCover)

Inputs: a presentation of `A` and explicit generators `Pg` of the locus ideal `P = locusIdeal I v₀`.
* (G1) `HasPres.exists_minimal_prime`: an explicit prime `𝔭 = (pgens)` minimal over `P`, with a
  factorial fraction field; it is a component (`mem_minimalPrimes_of_explicit`).
* (G2) `explicitNS_of_hasPres`: `ExplicitNS A` from `HasPres.exists_point`.
* The decision (G) and `IndNoeth (A ⧸ 𝔭)` from the presentation (`mem_dec`, `polyBar`).
* The separating element: the colon `(P : 𝔭)` is explicit (`HasPres.exists_colon`) and
  `1 ∈ 𝔭 + (P : 𝔭)` is decided by `mem_dec`; the negative branch is refuted (classically, here in
  `Principalization`) since `𝔭 + 𝔭' = (1)` for the other components (`minimalPrimes_sup_eq_top`)
  and `P` is radical. Then `sep_of_mem_colon`.
* `exists_chartCover_of_component`: for ANY component `𝔭` (e.g. `S.𝔭` of the torsor data), a
  separated chart cover positively — every minimal prime over `(Pg)` is explicit
  (`HasPres.gens_of_minimalPrime`). This is the drop-in replacement for the classical
  `exists_chartCover` in `torsorSGD`, given `HasPres A` and generators of the locus ideal.
* `exists_chartCover_explicit`: an explicit component `𝔭` with a separated chart cover.
* `exists_locusIdeal_gens`: generators of the locus ideal from `IsNoetherianRing A` — the single
  classical input left in `torsorSGD`.
* (O3) `exists_gens_compF`: explicit generators of `F_t(𝔭)` (hence of `gensF`, via `compFil_F`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

/-- **(G2)**: the Nullstellensatz with explicit points, from a presentation. -/
theorem explicitNS_of_hasPres {A : Type} [CommRing A] [Algebra ℚ A] (hp : HasPres A) :
    ExplicitNS A := by
  intro l hl
  obtain ⟨L, iF, iA, iFD, z, hz, hzl, -⟩ := hp.exists_point l hl
  exact ⟨L, iF, iA, iFD, z.toRatAlgHom, hz, hzl⟩

lemma lspan_append_eq {A : Type*} [CommRing A] (a b : List A) :
    Constructive.lspan (a ++ b) = Constructive.lspan a ⊔ Constructive.lspan b := by
  rw [Constructive.lspan, Constructive.lspan, Constructive.lspan, ← Ideal.span_union]
  congr 1
  ext x
  simp [List.mem_append]

/-- `IndNoeth` of a quotient of a presented ring. -/
theorem indNoeth_quotient_of_hasPres {A : Type} [CommRing A] (hp : HasPres A) (J : Ideal A) :
    IndNoeth (A ⧸ J) := by
  obtain ⟨n, G, ⟨e⟩⟩ := hp
  exact IndNoeth.of_surjective ((Ideal.Quotient.mk J).comp (e.toRingHom.comp
    (Ideal.Quotient.mk _))) ((Ideal.Quotient.mk_surjective).comp
      (e.surjective.comp Ideal.Quotient.mk_surjective)) (polyBar n)

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- An explicit prime minimal over the explicit generators is a minimal prime. -/
lemma mem_minimalPrimes_of_explicit {P 𝔭 : Ideal A} (hP𝔭 : P ≤ 𝔭) (h𝔭 : 𝔭.IsPrime)
    (hmin : ∀ Q : Ideal A, Q.IsPrime → P ≤ Q → Q ≤ 𝔭 → Q = 𝔭) : 𝔭 ∈ P.minimalPrimes :=
  ⟨⟨h𝔭, hP𝔭⟩, fun Q hQ hQ𝔭 => (hmin Q hQ.1 hQ.2 hQ𝔭).symm ▸ le_rfl⟩

include hI hmax in
/-- **The separating element is explicit**: `1 ∈ 𝔭 + (P : 𝔭)`, with `(P : 𝔭)` given by a list. -/
theorem one_mem_sup_colon {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes)
    (C : List A) (hC : ∀ x, x ∈ Constructive.lspan C ↔ ∀ y ∈ 𝔭, x * y ∈ locusIdeal I v₀) :
    (1 : A) ∈ 𝔭 ⊔ Constructive.lspan C := by
  classical
  have hfin : ((locusIdeal I v₀).minimalPrimes \ {𝔭}).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing A _).subset Set.sdiff_subset
  set S := hfin.toFinset
  set Q : Ideal A := ⨅ q ∈ S, q
  have hQ : 𝔭 ⊔ Q = ⊤ := Ideal.sup_iInf_eq_top fun q hq => by
    obtain ⟨hqm, hqne⟩ := (Set.Finite.mem_toFinset hfin).1 hq
    exact minimalPrimes_sup_eq_top hI (IsMaxInvPt.toMax hmax) h𝔭 hqm (Ne.symm hqne)
  have hrad : ∀ x : A, x ∈ (locusIdeal I v₀).radical → x ∈ locusIdeal I v₀ := by
    intro x ⟨k, hk⟩
    rw [mem_locusIdeal] at hk ⊢
    intro 𝔪 h𝔪
    obtain ⟨h𝔪m, hI𝔪, hv𝔪⟩ := h𝔪
    exact h𝔪m.isPrime.mem_of_pow_mem k (hk 𝔪 ⟨h𝔪m, hI𝔪, hv𝔪⟩)
  have hQC : Q ≤ Constructive.lspan C := by
    intro x hx
    refine (hC x).2 fun y hy => hrad _ ?_
    rw [← Ideal.sInf_minimalPrimes]
    refine Submodule.mem_sInf.2 fun q hq => ?_
    by_cases hqp : q = 𝔭
    · exact Ideal.mul_mem_left _ _ (hqp ▸ hy)
    · have hqS : q ∈ S := (Set.Finite.mem_toFinset hfin).2 ⟨hq, hqp⟩
      exact Ideal.mul_mem_right _ _ ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hx q) hqS)
  have : (⊤ : Ideal A) ≤ 𝔭 ⊔ Constructive.lspan C := hQ ▸ sup_le_sup_left hQC 𝔭
  exact this trivial

/-- **The single classical input of `torsorSGD`** (option 2, M4): generators of the locus ideal,
from `IsNoetherianRing A`. Positive replacement planned: `⋂ₖ D_k.p` over a positive cover of
`V(I)` by local data (`docs/d5-plan.md`). -/
theorem exists_locusIdeal_gens (I : Ideal A) (v₀ : ℕ → ℚ) :
    ∃ Pg : List A, locusIdeal I v₀ = Constructive.lspan Pg := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (locusIdeal I v₀ : Submodule A A))
  refine ⟨s.toList, ?_⟩
  rw [Constructive.lspan]
  conv_lhs => rw [← hs]
  congr 1
  ext x
  simp

include hI hmax in
/-- **(M4) A separated chart cover of a given component**, positively: from a presentation of `A`
and explicit generators of the locus ideal (every component is then explicit). -/
theorem exists_chartCover_of_component (hp : HasPres A) (Pg : List A)
    (hPg : locusIdeal I v₀ = Constructive.lspan Pg) {𝔭 : Ideal A}
    (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) : Nonempty (ChartCover I v₀ 𝔭) := by
  obtain ⟨pgens, hpg, -⟩ := hp.gens_of_minimalPrime Pg (hPg ▸ h𝔭)
  have hZ : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 → I ≤ 𝔪 ∧ InvAt I 𝔪 v₀ :=
    fun 𝔪 _ h => mem_maxLocus_of_minimal hI (IsMaxInvPt.toMax hmax) h𝔭 𝔪 h
  -- the separating element
  obtain ⟨C, hC⟩ := hp.exists_colon Pg pgens
  have hC' : ∀ x, x ∈ Constructive.lspan C ↔ ∀ y ∈ 𝔭, x * y ∈ locusIdeal I v₀ := by
    intro x; rw [hC x, hPg, hpg]
  have h1C : (1 : A) ∈ 𝔭 ⊔ Constructive.lspan C := by
    rcases hp.mem_dec (pgens ++ C) 1 with h | h
    · rwa [lspan_append_eq, ← hpg] at h
    · exact one_mem_sup_colon hI hmax h𝔭 C hC'
  obtain ⟨p, hp𝔭, q, hqC, hpq⟩ := Submodule.mem_sup.1 h1C
  have hq : 1 - q ∈ 𝔭 := by rw [← hpq, add_sub_cancel_right]; exact hp𝔭
  have hqsep : ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], q ∉ 𝔪' → I ≤ 𝔪' → InvAt I 𝔪' v₀ → 𝔭 ≤ 𝔪' :=
    fun 𝔪' _ hq' hI' hv' => sep_of_mem_colon (P := locusIdeal I v₀)
      (fun 𝔪'' _ hI'' hv'' => fun f hf => mem_locusIdeal.1 hf 𝔪'' ⟨‹_›, hI'', hv''⟩)
      (fun y hy => (hC' q).1 hqC y hy) 𝔪' hq' hI' hv'
  have hdec : ∀ l : List A, (1 : A) ∈ 𝔭 ⊔ Constructive.lspan l ∨
      (1 : A) ∉ 𝔭 ⊔ Constructive.lspan l := fun l => by
    rw [hpg, ← lspan_append_eq]; exact hp.mem_dec _ 1
  exact exists_chartCover_pos hI hZ q hq hqsep pgens hpg (explicitNS_of_hasPres hp) hdec
    (indNoeth_quotient_of_hasPres hp 𝔭)

include hI hmax in
/-- **(M4) An explicit component with a separated chart cover**: (G1) gives an explicit minimal
prime of the locus ideal, with a factorial fraction field. -/
theorem exists_chartCover_explicit (hp : HasPres A) (Pg : List A)
    (hPg : locusIdeal I v₀ = Constructive.lspan Pg) (h1 : (1 : A) ∉ Constructive.lspan Pg) :
    ∃ pgens : List A, Constructive.lspan pgens ∈ (locusIdeal I v₀).minimalPrimes ∧
      PrimeFF (Constructive.lspan pgens) ∧
      Nonempty (ChartCover I v₀ (Constructive.lspan pgens)) := by
  obtain ⟨pgens, hle, hFF, hmin⟩ := hp.exists_minimal_prime Pg h1
  have h𝔭 : Constructive.lspan pgens ∈ (locusIdeal I v₀).minimalPrimes :=
    mem_minimalPrimes_of_explicit (hPg ▸ hle) hFF.1 (fun Q hQ hPQ hQ𝔭 => hmin Q hQ (hPg ▸ hPQ) hQ𝔭)
  exact ⟨pgens, h𝔭, hFF, exists_chartCover_of_component hI hmax hp Pg hPg h𝔭⟩

include hI hmax in
/-- **(O3) Explicit generators of `F_t(𝔭)`** for any component: chart lists of the positive chart
cover (`mem_compF_iff_list`) and `HasPres.exists_gens_of_charts`. With `compFil_F` (`rfl`) this gives
explicit `gensF`. -/
theorem exists_gens_compF (hp : HasPres A) (Pg : List A)
    (hPg : locusIdeal I v₀ = Constructive.lspan Pg) {𝔭 : Ideal A}
    (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) (t : ℚ) :
    ∃ N : List A, Constructive.lspan N = compF I 𝔭 t := by
  obtain ⟨C⟩ := exists_chartCover_of_component hI hmax hp Pg hPg h𝔭
  have hZ : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 → I ≤ 𝔪 ∧ InvAt I 𝔪 v₀ :=
    fun 𝔪 _ h => mem_maxLocus_of_minimal hI (IsMaxInvPt.toMax hmax) h𝔭 𝔪 h
  haveI : Fact (HasPres A) := ⟨hp⟩
  obtain ⟨L, hL⟩ := mem_compF_iff_list hI hZ C t
  obtain ⟨N, hN⟩ := hp.exists_gens_of_charts (fun k => (C.D k).g) L
  exact ⟨N, by ext x; rw [hN, hL]⟩

end BezoutCounterexample.Principalization
