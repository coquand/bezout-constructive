import BezoutCounterexample.Principalization.GCDStep
import BezoutCounterexample.Constructive.DynDiv

/-!
# Classical bridge for the D5 divisorial step (`docs/d5-plan.md`, step 3)

`Constructive.div_dyn` states the divisorial hypothesis without `LocData`: an `x ∈ 𝔭` and an
`s ∉ 𝔭` with `x ∣ s g` for every generator `g`. This file checks that the hypotheses of
`div_eq_span_G` give it (`exists_locPrinc`), and recovers `div_eq_span_G` for a list of
generators from `div_dyn` (`div_eq_span_G_of_dyn`; the split branch is empty since `𝔭` is prime).

Proof of `exists_locPrinc`: at a maximal `𝔪 ⊇ 𝔭`, `𝔭 A_𝔪 = (x/u)` (`LocData`); `x ∈ 𝔭` since
`𝔭` is contracted from `A_𝔪`; `x/u ∣ g` in `A_𝔪` gives `x ∣ σ_g g` with `σ_g ∉ 𝔪`, and
`s = ∏ σ_g`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes)

include hI hmax h𝔭 in
/-- **The divisorial case gives local principality with a denominator outside `𝔭`.** -/
theorem exists_locPrinc (h0 : v₀ 0 ≠ 0) (hk1 : v₀ 1 = 0) (P : List A) (hP : lspan P = 𝔭) :
    ∃ s x : A, s ∉ 𝔭 ∧ x ∈ 𝔭 ∧ ∀ g ∈ P, x ∣ s * g := by
  classical
  have := h𝔭.1.1
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal 𝔭 (Ideal.IsPrime.ne_top ‹_›)
  have := h𝔪
  obtain ⟨hI𝔪, hv⟩ := mem_maxLocus_of_minimal hI (IsMaxInvPt.toMax hmax) h𝔭 𝔪 hle
  obtain ⟨D⟩ := LocData.nonempty hI 𝔪 hI𝔪 hv
  have hp : 𝔭 = D.p := D.eq_p_of_minimal h𝔭 hle
  set L := Localization.AtPrime 𝔪
  set xL := (Loc.transport (D.ctrl 𝔪 D.hg) D.ck).x ⟨0, D.n_pos h0⟩
  have hloc : 𝔭.map (algebraMap A L) = Ideal.span {xL} := by
    rw [hp, D.map_p, D.P_eq_span h0 hk1]
  obtain ⟨⟨x, u⟩, hxu⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl xL
  simp only at hxu
  have hdisj : Disjoint (𝔪.primeCompl : Set A) (𝔭 : Set A) := by
    rw [Set.disjoint_left]; intro b hb hb'; exact hb (hle hb')
  have hc := IsLocalization.comap_map_of_isPrime_disjoint 𝔪.primeCompl L ‹𝔭.IsPrime› hdisj
  -- `x ∈ 𝔭`
  have hx : x ∈ 𝔭 := by
    have : algebraMap A L x ∈ 𝔭.map (algebraMap A L) := by
      rw [hloc, ← hxu, ← IsLocalization.mk'_spec L x u]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [← Ideal.mem_comap] at this; exact (Ideal.ext_iff.1 hc x).1 this
  -- `x ∣ σ_g g` with `σ_g ∉ 𝔪`
  have hσ : ∀ j : Fin P.length, ∃ σ ∈ 𝔪.primeCompl, x ∣ σ * P.get j := by
    intro j
    have hmem : algebraMap A L (P.get j) ∈ Ideal.span {xL} := by
      rw [← hloc, ← hP]; exact Ideal.mem_map_of_mem _ (Ideal.subset_span (List.get_mem P j))
    have hdiv : algebraMap A L x ∣ algebraMap A L (P.get j) := by
      rw [← IsLocalization.mk'_spec L x u, hxu]
      exact (IsLocalization.map_units L u).mul_right_dvd.2 (Ideal.mem_span_singleton.1 hmem)
    exact exists_dvd_of_dvd_localization 𝔪.primeCompl L hdiv
  choose σ hσS hσ using hσ
  refine ⟨∏ j, σ j, x, fun hs => Submonoid.prod_mem 𝔪.primeCompl (fun j _ => hσS j) (hle hs),
    hx, fun g hg => ?_⟩
  obtain ⟨j, rfl⟩ := List.get_of_mem hg
  obtain ⟨t, ht⟩ : σ j ∣ ∏ j, σ j := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  rw [ht, mul_comm (σ j) t, mul_assoc]
  exact dvd_mul_of_dvd_right (hσ j) t

include hI hmax h𝔭 in
/-- `div_eq_span_G` for a list of generators, recovered from `div_dyn`. -/
theorem div_eq_span_G_of_dyn (hpres : HasPres A) (hG : HasGcd A) (h0 : v₀ 0 ≠ 0)
    (hk1 : v₀ 1 = 0) (P : List A) (hP : lspan P = 𝔭) {δ : A} (hδ : IsGcdFam δ P.get) :
    𝔭 = Ideal.span {δ} := by
  have := h𝔭.1.1
  obtain ⟨s, x, hs, hx, hxs⟩ := exists_locPrinc hI hmax h𝔭 h0 hk1 P hP
  have hrad : IsRadL P := fun y n hy => by
    rw [hP] at hy ⊢; exact ‹𝔭.IsPrime›.mem_of_pow_mem n hy
  subst hP
  rcases div_dyn hpres hG hrad hs hx hxs hδ with h | ⟨L₁, L₂, -, -, -, -, ⟨y₁, m₁, n₁⟩, ⟨y₂, m₂, n₂⟩, hsp⟩
  · exact h
  · -- a prime is not an intersection of two strictly larger ideals
    exfalso
    have hm : y₁ * y₂ ∈ lspan P := (hsp _).2
      ⟨Ideal.mul_mem_right _ _ m₁, Ideal.mul_mem_left _ _ m₂⟩
    rcases ‹(lspan P).IsPrime›.mem_or_mem hm with h | h
    · exact n₁ h
    · exact n₂ h

end BezoutCounterexample.Principalization
