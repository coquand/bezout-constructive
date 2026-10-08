import BezoutCounterexample.Principalization.PosWire
import BezoutCounterexample.Constructive.CompList
import BezoutCounterexample.Principalization.MaxInvPtDef

/-!
# Components of the maximal locus as an explicit list (Task D, R2: m4, m5)

Given a presentation of `A` and generators `Pg` of the locus ideal `P = locusIdeal I v₀`, the
components of the maximal locus form an explicit list `Cs` (`IsCompList Pg Cs`, from
`HasPres.exists_compList`).

* `compList_eq_or_comax` (m4, replacing `minimalPrimes_sup_eq_top`): two components are equal or
  comaximal. `1 ∈ 𝔭 + 𝔭'` is decided by (G). In the negative branch an explicit point `z` of
  `V(𝔭 + 𝔭')` (NullJac, `explicitNS_of_hasPres`) replaces the maximal ideal from Zorn
  (`Ideal.exists_le_maximal`); `LocData` at `ker z` gives `𝔭 = D.p = 𝔭'`.
* `compList_one_mem_sup_colon` (m5, replacing `one_mem_sup_colon`): `1 ∈ 𝔭 + (P : 𝔭)`, from the
  elementwise radical identity of the Lasker tree and CRT (`IsCompList.one_mem_sup_colon`); no
  `Ideal.finite_minimalPrimes_of_isNoetherianRing`, no `Ideal.sInf_minimalPrimes`, no `classical`.

The `LocData` step itself is still the classical engine (R1/R3, Task C); what is removed here is
the choice of a maximal ideal and the minimal-prime set.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)

include hI hmax in
/-- **m4: components are equal or comaximal**, decided by (G), with an explicit point in the
negative branch. -/
theorem compList_eq_or_comax (hp : HasPres A) {Pg : List A}
    (hPg : locusIdeal I v₀ = lspan Pg) {Cs : List (List A)} (hC : IsCompList Pg Cs)
    {C D : List A} (hCm : C ∈ Cs) (hDm : D ∈ Cs) :
    lspan D = lspan C ∨ (1 : A) ∈ lspan C ⊔ lspan D := by
  rcases hp.mem_dec (C ++ D) 1 with h | h
  · exact Or.inr (by rwa [lspan_append_eq] at h)
  · refine Or.inl ?_
    obtain ⟨L, _, _, _, z, -, hz⟩ := explicitNS_of_hasPres hp (C ++ D) h
    have h𝔪 : (RingHom.ker z).IsMaximal := ker_isMaximal z
    have hle : lspan C ⊔ lspan D ≤ RingHom.ker z := by
      rw [← lspan_append_eq, lspan, Ideal.span_le]
      intro x hx
      exact hz x hx
    have h𝔭 : lspan C ∈ (locusIdeal I v₀).minimalPrimes := hPg ▸ hC.mem_minimalPrimes hCm
    have h𝔭' : lspan D ∈ (locusIdeal I v₀).minimalPrimes := hPg ▸ hC.mem_minimalPrimes hDm
    obtain ⟨hI𝔪, hv⟩ := mem_maxLocus_of_minimal hI (IsMaxInvPt.toMax hmax) h𝔭 _ (le_sup_left.trans hle)
    obtain ⟨E⟩ := LocData.nonempty hI _ hI𝔪 hv
    exact (E.eq_p_of_minimal h𝔭' (le_sup_right.trans hle)).trans
      (E.eq_p_of_minimal h𝔭 (le_sup_left.trans hle)).symm

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- The locus ideal is radical. -/
lemma locusIdeal_rad (x : A) (k : ℕ) (hk : x ^ k ∈ locusIdeal I v₀) : x ∈ locusIdeal I v₀ := by
  rw [mem_locusIdeal] at hk ⊢
  intro 𝔪 h𝔪
  obtain ⟨h𝔪m, hI𝔪, hv𝔪⟩ := h𝔪
  exact h𝔪m.isPrime.mem_of_pow_mem k (hk 𝔪 ⟨h𝔪m, hI𝔪, hv𝔪⟩)

include hI hmax in
/-- **m5: the separating element**, for an entry of the explicit component list. -/
theorem compList_one_mem_sup_colon (hp : HasPres A) {Pg : List A}
    (hPg : locusIdeal I v₀ = lspan Pg) {Cs : List (List A)} (hC : IsCompList Pg Cs)
    {C : List A} (hCm : C ∈ Cs) (K : List A)
    (hK : ∀ x, x ∈ lspan K ↔ ∀ y ∈ lspan C, x * y ∈ locusIdeal I v₀) :
    (1 : A) ∈ lspan C ⊔ lspan K :=
  hC.one_mem_sup_colon (fun _ hDm => compList_eq_or_comax hI hmax hp hPg hC hCm hDm)
    (fun x k hk => hPg ▸ locusIdeal_rad x k (hPg ▸ hk)) K (fun x => hPg ▸ hK x)

end BezoutCounterexample.Principalization
