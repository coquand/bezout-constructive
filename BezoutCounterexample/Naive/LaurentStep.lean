import BezoutCounterexample.Construction

/-!
# Adjoining two fresh units

For a smooth finitely generated factorial `ℚ`-domain `P`, the ring
`L(P) = P[X₀, X₁][1/(X₀ X₁)]` is again one (`laurentSGD`), `X₀, X₁` are units of `L(P)`
algebraically independent over `P`, and the compact set `K ⊆ Spec(P)(ℝ)` lifts to the compact set
`{X₀ = X₁ = 1}` over `K`, homeomorphically, so `K' → K` is a monotone surjection.
Composing with the principalization step gives a modified Construction 5.1 in which every stage
provides fresh units.
-/

noncomputable section

namespace BezoutCounterexample

open MvPolynomial

section Laurent

variable (P : Type) [CommRing P] [IsDomain P]

/-- `P[X₀, X₁]`. -/
abbrev Poly2 : Type := MvPolynomial (Fin 2) P

/-- `L(P) = P[X₀, X₁][1/(X₀ X₁)]`. -/
abbrev L2 : Type := Localization.Away (X 0 * X 1 : Poly2 P)

lemma X01_ne_zero : (X 0 * X 1 : Poly2 P) ≠ 0 := mul_ne_zero (X_ne_zero _) (X_ne_zero _)

instance : IsDomain (L2 P) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (X01_ne_zero P))

lemma L2_injective : Function.Injective (algebraMap (Poly2 P) (L2 P)) :=
  IsLocalization.injective (L2 P) (powers_le_nonZeroDivisors_of_noZeroDivisors (X01_ne_zero P))

/-- The map `P → L(P)`. -/
def toL2 : P →+* L2 P := (algebraMap (Poly2 P) (L2 P)).comp C

lemma toL2_injective : Function.Injective (toL2 P) :=
  (L2_injective P).comp (C_injective _ _)

lemma isUnit_X (i : Fin 2) : IsUnit (algebraMap (Poly2 P) (L2 P) (X i)) := by
  have h : IsUnit (algebraMap (Poly2 P) (L2 P) (X 0 * X 1)) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at h
  fin_cases i
  · exact isUnit_of_mul_isUnit_left h
  · exact isUnit_of_mul_isUnit_right h

/-- `X₀, X₁` are algebraically independent over `P` in `L(P)`, in the form: for every injective
`f : A → P`, the evaluation `A[Y₀, Y₁] → L(P)`, `Yᵢ ↦ Xᵢ` is injective. -/
lemma eval₂_X_injective {A : Type*} [CommRing A] (f : A →+* P) (hf : Function.Injective f) :
    Function.Injective (eval₂Hom ((toL2 P).comp f)
      ![algebraMap (Poly2 P) (L2 P) (X 0), algebraMap (Poly2 P) (L2 P) (X 1)]) := by
  have h : eval₂Hom ((toL2 P).comp f)
      ![algebraMap (Poly2 P) (L2 P) (X 0), algebraMap (Poly2 P) (L2 P) (X 1)] =
      (algebraMap (Poly2 P) (L2 P)).comp (map f) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [toL2]
    · intro i; fin_cases i <;> simp
  rw [h]
  exact (L2_injective P).comp (map_injective f hf)

/-- Evaluation at `X₀ = X₁ = 1`, `L(P) → P`. -/
def evalOne : L2 P →+* P :=
  IsLocalization.Away.lift (X 0 * X 1 : Poly2 P) (g := eval₂Hom (RingHom.id P) fun _ => 1)
    (by simp)

lemma evalOne_toL2 (a : P) : evalOne P (toL2 P a) = a := by
  simp [evalOne, toL2]

end Laurent

section LaurentSFD

variable (A : SmoothGCDDomain)

instance laurent_finitePresentation : Algebra.FinitePresentation ℚ (L2 A) := by
  have : Algebra.FinitePresentation A (Poly2 A) := inferInstance
  have : Algebra.FinitePresentation (Poly2 A) (L2 A) :=
    IsLocalization.Away.finitePresentation (X 0 * X 1 : Poly2 A)
  have : Algebra.FinitePresentation A (L2 A) :=
    Algebra.FinitePresentation.trans A (Poly2 A) (L2 A)
  exact Algebra.FinitePresentation.trans ℚ A (L2 A)

instance laurent_formallySmooth : Algebra.FormallySmooth ℚ (L2 A) := by
  have : Algebra.FormallySmooth (Poly2 A) (L2 A) :=
    Algebra.FormallySmooth.of_isLocalization (Submonoid.powers (X 0 * X 1 : Poly2 A))
  have : Algebra.FormallySmooth A (L2 A) := Algebra.FormallySmooth.comp A (Poly2 A) (L2 A)
  exact Algebra.FormallySmooth.comp ℚ A (L2 A)

instance laurent_smooth : Algebra.Smooth ℚ (L2 A) := ⟨inferInstance, inferInstance⟩

theorem laurent_hasGcd : Constructive.HasGcd (L2 A) :=
  Constructive.hasGcd_of_isLocalization (Submonoid.powers (X 0 * X 1 : Poly2 A)) (L2 A)
    (Constructive.hasGcd_mvPolynomial A.hasGcd A.zeroTest 2).1
    (Constructive.hasGcd_mvPolynomial A.hasGcd A.zeroTest 2).2

theorem laurent_zeroTest : ∀ x : L2 A, x = 0 ∨ x ≠ 0 :=
  Constructive.localization_eq_zero_or (Constructive.hasGcd_mvPolynomial A.hasGcd A.zeroTest 2).2
    (Submonoid.powers (X 0 * X 1 : Poly2 A))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (X01_ne_zero A)) (L2 A)

theorem laurent_dvdDec : Constructive.DvdDec (L2 A) := by
  have hz2 := (Constructive.hasGcd_mvPolynomial A.hasGcd A.zeroTest 2).2
  have hd2 : Constructive.DvdDec (Poly2 A) := Constructive.dvdDec_mvPolynomial A.zeroTest A.dvdDec 2
  have hN : Constructive.IndNoeth (Poly2 A) := Constructive.polyIndNoeth_of_finiteType A 2
  exact Constructive.dvdDec_away_mul (p := X 0) (q := X 1) MvPolynomial.X_prime MvPolynomial.X_prime
    hz2 hd2 (fun a ha => hN.exists_val MvPolynomial.X_prime.not_unit hd2 ha)
    (fun a ha => hN.exists_val MvPolynomial.X_prime.not_unit hd2 ha) (L2 A)

/-- `L(A)` as a smooth finitely generated GCD domain, all decisions computed from `A`. -/
noncomputable def laurentSGD : SmoothGCDDomain :=
  ⟨L2 A, laurent_hasGcd A, laurent_zeroTest A, laurent_dvdDec A,
    (A.pres.mvPolynomial 2).away (X 0 * X 1 : Poly2 A) (L2 A)⟩

/-- `A → L(A)`, typed with the bundled ring. -/
def toL2S : A →+* laurentSGD A := toL2 A

/-- `L(A) → A`, `X₀, X₁ ↦ 1`, typed with the bundled ring. -/
def evalOneS : laurentSGD A →+* A := evalOne A

lemma evalOneS_toL2S (a : A) : evalOneS A (toL2S A a) = a := evalOne_toL2 A a

/-- `A → L(A)` as a `ℚ`-algebra map. -/
def laurentIncl : A →ₐ[ℚ] laurentSGD A := (toL2S A).toRatAlgHom

end LaurentSFD


section RealLift

variable (A : SmoothGCDDomain)

/-- The lift of `K ⊆ Spec(A)(ℝ)` to `{X₀ = X₁ = 1} ⊆ Spec(L(A))(ℝ)`. -/
def laurentK (K : Set (RealPt A)) : Set (RealPt (laurentSGD A)) :=
  RealPt.comap (evalOneS A) '' K

lemma comap_toL2_comap_evalOne (z : RealPt A) :
    RealPt.comap (toL2S A) (RealPt.comap (evalOneS A) z) = z := by
  apply DFunLike.ext
  intro a
  show z (evalOneS A (toL2S A a)) = z a
  rw [evalOneS_toL2S]

lemma laurentK_isCompact {K : Set (RealPt A)} (hK : IsCompact K) : IsCompact (laurentK A K) :=
  hK.image (RealPt.continuous_comap _)

lemma laurentK_monotone (K : Set (RealPt A)) :
    IsMonotoneSurjOn (RealPt.comap (toL2S A)) (laurentK A K) K := by
  have hmaps : Set.MapsTo (RealPt.comap (toL2S A)) (laurentK A K) K := by
    rintro _ ⟨z, hz, rfl⟩
    rw [comap_toL2_comap_evalOne]
    exact hz
  have hval : ∀ (z : RealPt A) (hz : z ∈ K),
      (hmaps.restrict (RealPt.comap (toL2S A)) (laurentK A K) K
        ⟨RealPt.comap (evalOneS A) z, ⟨z, hz, rfl⟩⟩ : RealPt A) = z := fun z _ =>
    comap_toL2_comap_evalOne A z
  refine ⟨hmaps, ⟨(RealPt.continuous_comap _).restrict hmaps, fun w => ?_, fun w => ?_⟩⟩
  · exact ⟨⟨_, ⟨w.1, w.2, rfl⟩⟩, Subtype.ext (hval w.1 w.2)⟩
  · have : hmaps.restrict (RealPt.comap (toL2S A)) (laurentK A K) K ⁻¹' {w} =
        {⟨_, ⟨w.1, w.2, rfl⟩⟩} := by
      ext ⟨z'', hz''⟩
      obtain ⟨z, hz, rfl⟩ := hz''
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        have h' : z = w.1 := by rw [← hval z hz, h]
        subst h'
        rfl
      · intro h
        apply Subtype.ext
        have hzw : RealPt.comap (evalOneS A) z = RealPt.comap (evalOneS A) w.1 :=
          congrArg Subtype.val h
        show RealPt.comap (toL2S A) (RealPt.comap (evalOneS A) z) = w.1
        rw [hzw, comap_toL2_comap_evalOne]
    rw [this]
    exact isConnected_singleton

end RealLift

/-- Compose a principalization result with the Laurent step. -/
def PrincipalizationResult.withLaurent {A : SmoothGCDDomain} {I : Ideal A}
    {K : Set (RealPt A)} (D : PrincipalizationResult A I K) : PrincipalizationResult A I K where
  A' := laurentSGD D.A'
  f := (laurentIncl D.A').comp D.f
  K' := laurentK D.A' D.K'
  injective := (toL2_injective _).comp D.injective
  principal := by
    obtain ⟨g, hg⟩ := D.principal
    refine ⟨⟨laurentIncl D.A' g, ?_⟩⟩
    have hg' : I.map (D.f : A →+* D.A') = Ideal.span {g} := hg
    have : I.map ((laurentIncl D.A').comp D.f) =
        (I.map (D.f : A →+* D.A')).map (laurentIncl D.A' : D.A' →+* laurentSGD D.A') := by
      rw [Ideal.map_map]; rfl
    rw [this, hg', Ideal.map_span, Set.image_singleton]
    rfl
  isCompact := laurentK_isCompact _ D.isCompact
  monotone := by
    have h := IsMonotoneSurjOn.trans (laurentK_isCompact _ D.isCompact) D.monotone
      (laurentK_monotone D.A' D.K')
    convert h using 1
    funext z
    rfl

end BezoutCounterexample
