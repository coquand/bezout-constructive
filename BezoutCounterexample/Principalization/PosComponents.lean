import BezoutCounterexample.Principalization.PosCover

/-!
# Components without `JacS` and `NNMax` (leaf; `bezout-positive.tex` §1.6)

`Components.lean` takes two `¬¬`-hypotheses: `JacS A` (Jacobson in Nullstellensatz form) and
`NNMax A`. Here both are replaced by the explicit Nullstellensatz and decisions:

* `jacS_of_explicit`: `JacS A` from `ExplicitNS A[X]`, generator lists for primes, and decidable
  membership in finitely generated ideals (`HasPres.mem_dec` of `Constructive/Presented`, or
  Gröbner). The classical instantiation of the inputs is `jacS_inputs_classical`.
* `LocData.eq_of_sup_ne_top_E`: components meeting at a point coincide, **positively**, from
  `ExplicitNS A` and generator lists (replacing `not_not_eq_of_sup_ne_top`).
* `compF_map_E`: the filtration of `V(D.p)` localises to the maximal centres, from the positive
  cover `one_mem_certC_pos` (replacing the `hcov` input of `compF_map_S`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

section Jac

variable {A : Type} [CommRing A] [Algebra ℚ A]

/-- **`JacS` from the explicit Nullstellensatz** on `A[X]`. -/
theorem jacS_of_explicit (hNSX : ExplicitNS (Polynomial A))
    (hFG : ∀ p : Ideal A, ∃ l : List A, p = lspan l)
    (hmem : ∀ (l : List A) (f : A), f ∈ lspan l ∨ f ∉ lspan l) : JacS A := by
  intro p _ f hf
  obtain ⟨l, hl⟩ := hFG p
  exact jacS_explicit hNSX p l hl f (hl ▸ hmem l f) hf

omit [Algebra ℚ A] in
/-- Classical source of the inputs of `jacS_of_explicit`. -/
theorem jacS_inputs_classical [IsNoetherianRing A] :
    (∀ p : Ideal A, ∃ l : List A, p = lspan l) ∧
      ∀ (l : List A) (f : A), f ∈ lspan l ∨ f ∉ lspan l := by
  classical
  refine ⟨fun p => ?_, fun l f => em _⟩
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian p : p.FG)
  refine ⟨s.toList, ?_⟩
  rw [← hs, lspan]
  congr 1
  ext x
  simp

end Jac

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

namespace LocData

variable {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪)

omit [Algebra.Smooth ℚ A] [IsDomain A] [Algebra ℚ A] in
lemma lspan_append (l l₁ : List A) : lspan (l ++ l₁) = lspan l ⊔ lspan l₁ := by
  rw [lspan, lspan, lspan, ← Ideal.span_union]
  congr 1
  ext x
  simp [List.mem_append]

/-- **Components meeting at a point coincide**, positively. -/
theorem eq_of_sup_ne_top_E (hI : I ≠ ⊥) (hJ : JacS A) (hNS : ExplicitNS A)
    (hmaxS : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → ¬ toLex v < toLex v₀)
    {𝔪₁ : Ideal A} [𝔪₁.IsMaximal] (D₁ : LocData I v₀ 𝔪₁) (l l₁ : List A)
    (hl : D.p = lspan l) (hl₁ : D₁.p = lspan l₁) (hne : D.p ⊔ D₁.p ≠ ⊤) : D.p = D₁.p := by
  have h1 : (1 : A) ∉ lspan (l ++ l₁) := by
    rw [lspan_append, ← hl, ← hl₁]
    exact fun h => hne ((Ideal.eq_top_iff_one _).2 h)
  obtain ⟨L, _, _, _, z, -, hz⟩ := hNS (l ++ l₁) h1
  have := ker_isMaximal z
  have hle : D.p ⊔ D₁.p ≤ RingHom.ker z := by
    rw [hl, hl₁, ← lspan_append, lspan, Ideal.span_le]
    intro x hx; exact hz x hx
  have hZ := D.mem_of_le_p_S hI hJ hmaxS _ (le_sup_left.trans hle)
  obtain ⟨D'⟩ := LocData.nonempty hI _ hZ.1 hZ.2
  exact (D.eq_p_S hJ D' (le_sup_left.trans hle)).trans
    (D₁.eq_p_S hJ D' (le_sup_right.trans hle)).symm

end LocData

variable [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} (hJ : JacS A)
  (hmaxS : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → ¬ toLex v < toLex v₀)
  {𝔪₁ : Ideal A} [𝔪₁.IsMaximal] (D₁ : LocData I v₀ 𝔪₁)
include hI hJ hmaxS

/-- **The filtration of `V(D.p)` localises to the maximal centres**, from the positive cover. -/
theorem compF_map_E (hNS : ExplicitNS A) (pgens : List A) (hpg : D₁.p = lspan pgens)
    (hdec : ∀ l : List A, (1 : A) ∈ D₁.p ⊔ lspan l ∨ (1 : A) ∉ D₁.p ⊔ lspan l)
    (hN : IndNoeth (A ⧸ D₁.p)) (𝔪₀ : Ideal A) [𝔪₀.IsMaximal] (h𝔭𝔪 : D₁.p ≤ 𝔪₀) (t : ℚ) :
    (compF I D₁.p t).map (algebraMap A (Localization.AtPrime 𝔪₀)) = cRF I 𝔪₀ t :=
  compF_map_S hI hJ hmaxS D₁
    (one_mem_certC_pos hI (D₁.mem_of_le_p_S hI hJ hmaxS) pgens hpg hNS hdec hN) 𝔪₀ h𝔭𝔪 t

end BezoutCounterexample.Principalization
