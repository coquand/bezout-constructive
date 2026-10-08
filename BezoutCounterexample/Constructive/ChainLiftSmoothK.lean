import Mathlib
import BezoutCounterexample.Constructive.Attr

/-!
# Smoothness: local–global and spreading out (Task B, trusted primitives)

Two facts about finitely presented `ℚ`-algebras, used to prove the smoothness of the extended Rees
algebra without quantifying over the primes of `R` (`Algebra.smoothLocus`). Both statements are
constructively valid; their Mathlib proofs go through `smoothLocus` and are classical, so they are
`@[cprim]`.

* `smooth_of_span_cover` (**local–global**): `S` is smooth if `S[1/r]` is smooth for every `r` in
  a set `s` with `(s) = 1`. Constructively (Lombardi–Quitté, Ch. XV, local–global principles for
  comaximal localisations): finite presentation glues (Ch. XV), and formal smoothness is the
  splitting of the conormal sequence `J/J² → Ω_P ⊗ S` (`FormallySmooth.iff_split_injection`,
  Stacks 00TH). Retractions `ρ_k` on `D(r_k)` are given by the images of the finitely many `dYᵢ`;
  with `Σ a_k r_k^{N} = 1` the map `ρ = Σ a_k r_k^{N} ρ_k` is a global retraction (the identities
  `ρ_k ι = id` hold on `D(r_k)` for the finitely many generators of `J`, after multiplying by a
  power of `r_k`). Only finitely many `r_k` are used (`1 ∈ (s)` is a finite combination).
* `exists_away_smooth_of_isLocalization` (**spreading out**): if `S_M` is formally smooth for a
  submonoid `M` of the base `A`, then `S[1/a]` is smooth for some `a ∈ M`. Constructive reading:
  fix a finite presentation `S = P/I`, `P = ℚ[Y₁…Y_N]`, `I = (f₁…f_r)`. Formal smoothness of `S_M`,
  applied to the square-zero lifting problem `P_M/I_M² → P_M/I_M` with the identity of `S_M`, gives
  an **explicit** section, i.e. an explicit retraction of the conormal sequence
  `I_M/I_M² → Ω_P ⊗ S_M`: finitely many elements `ρ(dYᵢ) ∈ I_M/I_M²` with the finitely many
  identities `ρ(df_j) = f_j`. These involve finitely many denominators `m₁ … m_t ∈ M` (and the
  identities hold after multiplying by finitely many further elements of `M`); `a` is their
  product. No search over `M` is involved: `a` is read off the given section. Over `S[1/a]` the same
  data is a retraction, so `S[1/a]` is formally smooth, and finitely presented as a localization
  (Stacks 00TF/00TB/00TH, Lombardi–Quitté Ch. VI).
-/

namespace BezoutCounterexample.Constructive

/-- **Local–global for smoothness** over a set generating the unit ideal (trusted primitive:
constructively valid statement, classical Mathlib proof). -/
@[cprim]
theorem smooth_of_span_cover {S : Type} [CommRing S] [Algebra ℚ S] (s : Set S)
    (hs : Ideal.span s = ⊤) (h : ∀ r ∈ s, Algebra.Smooth ℚ (Localization.Away r)) :
    Algebra.Smooth ℚ S := by
  rw [← RingHom.smooth_algebraMap]
  refine RingHom.Smooth.ofLocalizationSpanTarget (algebraMap ℚ S) s hs fun r => ?_
  rw [← IsScalarTower.algebraMap_eq]
  exact RingHom.smooth_algebraMap.mpr (h r r.2)

/-- **Spreading out smoothness** from a localization of the base (trusted primitive:
constructively valid statement, classical Mathlib proof). -/
@[cprim]
theorem exists_away_smooth_of_isLocalization {A S Sₘ : Type*} [CommRing A] [CommRing S]
    [CommRing Sₘ] [Algebra A S] [Algebra ℚ S] [Algebra S Sₘ] [Algebra ℚ Sₘ] [IsScalarTower ℚ S Sₘ]
    [Algebra.FinitePresentation ℚ S] (M : Submonoid A)
    [IsLocalization (M.map (algebraMap A S)) Sₘ] [Algebra.FormallySmooth ℚ Sₘ] :
    ∃ a ∈ M, Algebra.Smooth ℚ (Localization.Away (algebraMap A S a)) := by
  classical
  set M' := M.map (algebraMap A S)
  -- every prime of `S` avoiding `M'` is in the smooth locus
  have hU : ∀ P : PrimeSpectrum S, Disjoint (M' : Set S) P.asIdeal →
      P ∈ Algebra.smoothLocus ℚ S := by
    intro P hP
    show Algebra.FormallySmooth ℚ (Localization.AtPrime P.asIdeal)
    set P' := P.asIdeal.map (algebraMap S Sₘ)
    have hP' : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M' Sₘ _ P.isPrime hP
    have hcomap : P'.comap (algebraMap S Sₘ) = P.asIdeal :=
      IsLocalization.under_map_of_isPrime_disjoint M' Sₘ P.isPrime hP
    have : IsLocalization P.asIdeal.primeCompl (Localization.AtPrime P') := by
      have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M'
        (Localization.AtPrime P') P'
      have he : (P'.under S).primeCompl = P.asIdeal.primeCompl := by
        ext x; show x ∉ P'.comap (algebraMap S Sₘ) ↔ x ∉ P.asIdeal; rw [hcomap]
      exact he ▸ h
    have hT : Algebra.FormallySmooth ℚ (Localization.AtPrime P') := inferInstance
    let e0 := IsLocalization.algEquiv P.asIdeal.primeCompl (Localization.AtPrime P')
      (Localization.AtPrime P.asIdeal)
    let e : Localization.AtPrime P' ≃ₐ[ℚ] Localization.AtPrime P.asIdeal :=
      AlgEquiv.ofRingEquiv (f := e0.toRingEquiv)
        (fun q => RingHom.map_rat_algebraMap e0.toRingEquiv.toRingHom q)
    exact Algebra.FormallySmooth.of_equiv e
  -- the non-smooth locus is closed: `V(T)`
  obtain ⟨T, hT⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).1
    (Algebra.isOpen_smoothLocus (R := ℚ) (A := S)).isClosed_compl
  -- `T` generates the unit ideal in `S_M`, so some `m ∈ M'` lies in `(T)`
  have htop : (Ideal.span T).map (algebraMap S Sₘ) = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    set P := Q.comap (algebraMap S Sₘ)
    have hPdisj : Disjoint (M' : Set S) P :=
      (IsLocalization.isPrime_iff_isPrime_disjoint M' Sₘ Q).1 hQ.isPrime |>.2
    have hsm := hU ⟨P, Ideal.comap_isPrime _ _⟩ hPdisj
    have hz : (⟨P, Ideal.comap_isPrime _ _⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.zeroLocus T := by
      intro t ht
      exact hle (Ideal.mem_map_of_mem _ (Ideal.subset_span ht))
    rw [← hT] at hz
    exact hz hsm
  have h1 : (1 : Sₘ) ∈ (Ideal.span T).map (algebraMap S Sₘ) := htop ▸ Submodule.mem_top
  obtain ⟨⟨x, m⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff M' Sₘ).1 h1
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M' Sₘ).1 (by simpa using hx.symm)
  obtain ⟨a, ha, hae⟩ := (c * m).2
  have hm : algebraMap A S a ∈ Ideal.span T := by
    rw [hae, Submonoid.coe_mul, ← hc]
    exact Ideal.mul_mem_left _ _ x.2
  refine ⟨a, ha, ?_⟩
  rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth]
  intro P hP
  by_contra hns
  have hz : P ∈ PrimeSpectrum.zeroLocus T := by rw [← hT]; exact hns
  exact hP ((PrimeSpectrum.zeroLocus_span T ▸ hz) hm)

end BezoutCounterexample.Constructive
