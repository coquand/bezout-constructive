import BezoutCounterexample.LengthControl

/-!
# A chart at the generic point, by linear algebra (leaf, part (a))

`eq_top_or_exists_chartDim` (LengthControl) gets its chart at `⊥` from `exists_chart_atPrime`,
i.e. from the classical `exists_chart_away` (charts on basic opens of a smooth algebra), and treats
size `0` through `chart_size_eq_ringKrullDim` (Krull dimension; `Chart.IsCentred.span_x_isPrime`).
At the generic point no smoothness is needed: `K = B_{(0)}` is a field, `Ω_{K/ℚ}` is spanned by
the differentials of finitely many algebra generators of `B`, a spanning family contains a basis
(`exists_linearIndependent'`), and the coordinate functionals of that basis composed with `d` are
the dual derivations. Size `0` means `Ω_{K/ℚ} = 0`: `K/ℚ` is formally unramified of essentially
finite type, hence separable algebraic (`Algebra.FormallyUnramified.isSeparable`), so `B` is integral
over `ℚ`, a field.

* `span_D_bot`: the differentials of generators span `Ω_{K/ℚ}`;
* `exists_chart_bot`: a chart at `⊥` (twin of `exists_chart_atPrime ⊥`, no `Algebra.Smooth`);
* `isField_of_chart_bot_zero`: a chart of size `0` at `⊥` makes `B` a field;
* `eq_top_or_exists_chartDim_bot`: twin of `eq_top_or_exists_chartDim`.

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open KaehlerDifferential

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B]

local notation "K" => Localization.AtPrime (⊥ : Ideal B)

/-- **The differentials of algebra generators span `Ω_{K/ℚ}`** at the generic point. -/
theorem span_D_bot (s : Finset B) (hs : Algebra.adjoin ℚ (s : Set B) = ⊤) :
    Submodule.span K (Set.range fun y : s => D ℚ K (algebraMap B K y)) = ⊤ := by
  set M := Submodule.span K (Set.range fun y : s => D ℚ K (algebraMap B K y)) with hM
  have hB : ∀ b : B, D ℚ K (algebraMap B K b) ∈ M := by
    intro b
    have hb : b ∈ Algebra.adjoin ℚ (s : Set B) := hs ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply, Derivation.map_algebraMap]
      exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul, Derivation.leibniz]
      exact add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)
  rw [eq_top_iff, ← span_range_derivation, Submodule.span_le]
  rintro _ ⟨z, rfl⟩
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective (⊥ : Ideal B).primeCompl z
  set z := IsLocalization.mk' K b t
  have hz : z * algebraMap B K t = algebraMap B K b := IsLocalization.mk'_spec K b t
  have h1 : algebraMap B K t • D ℚ K z ∈ M := by
    have h2 := congrArg (D ℚ K) hz
    rw [Derivation.leibniz] at h2
    have h3 : algebraMap B K t • D ℚ K z = D ℚ K (algebraMap B K b) -
        z • D ℚ K (algebraMap B K t) := by rw [← h2]; abel
    rw [h3]
    exact sub_mem (hB b) (Submodule.smul_mem _ _ (hB t))
  obtain ⟨u, hu⟩ := IsLocalization.map_units K t
  have h4 : D ℚ K z = (↑u⁻¹ : K) • (algebraMap B K t • D ℚ K z) := by
    rw [← hu, smul_smul, Units.inv_mul, one_smul]
  rw [SetLike.mem_coe, h4]
  exact Submodule.smul_mem _ _ h1

variable [Algebra.FiniteType ℚ B]

/-- **A chart at the generic point**, from a basis of `Ω_{K/ℚ}` among the differentials of
generators (no smoothness, no `exists_chart_away`). -/
theorem exists_chart_bot : ∃ n, Nonempty (Chart K n) := by
  have : IsFractionRing B K := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal B).primeCompl)
  let : Field K := IsFractionRing.toField B
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℚ B).FG)
  set v : s → Ω[K⁄ℚ] := fun y => D ℚ K (algebraMap B K y) with hv
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K v
  have : Finite κ := Finite.of_injective a ha
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  have hli' : LinearIndependent K ((v ∘ a) ∘ e.symm) := hli.comp _ e.symm.injective
  have hsp' : ⊤ ≤ Submodule.span K (Set.range ((v ∘ a) ∘ e.symm)) := by
    rw [e.symm.surjective.range_comp, hsp, hv, span_D_bot s hs]
  let bas := Module.Basis.mk hli' hsp'
  have hbas : ∀ j, D ℚ K (algebraMap B K (a (e.symm j))) = bas j := fun j => by
    rw [Module.Basis.mk_apply]; rfl
  refine ⟨n, ⟨{ x := fun i => algebraMap B K (a (e.symm i))
                d := fun i => (bas.coord i).compDer (D ℚ K)
                d_x := fun i j => ?_
                span := ?_ }⟩⟩
  · change bas.coord i (D ℚ K (algebraMap B K (a (e.symm j)))) = _
    rw [hbas, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · simp only [hbas]
    exact bas.span_eq

/-- **A chart of size `0` at the generic point makes `B` a field**: `Ω_{K/ℚ} = 0`, so `K/ℚ` is
formally unramified of essentially finite type, hence separable algebraic, and `B ⊆ K` is integral
over `ℚ`. -/
theorem isField_of_chart_bot_zero (c : Chart K 0) : IsField B := by
  have : IsFractionRing B K := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal B).primeCompl)
  let : Field K := IsFractionRing.toField B
  have hsub : Subsingleton Ω[K⁄ℚ] := by
    have h := c.span
    rw [Set.range_eq_empty, Submodule.span_empty] at h
    have := subsingleton_of_bot_eq_top h
    exact (Submodule.subsingleton_iff K).mp this
  have : Algebra.FormallyUnramified ℚ K := ⟨hsub⟩
  have : Algebra.EssFiniteType B K :=
    Algebra.EssFiniteType.of_isLocalization _ (⊥ : Ideal B).primeCompl
  have : Algebra.EssFiniteType ℚ K := Algebra.EssFiniteType.comp ℚ B K
  have := Algebra.FormallyUnramified.isSeparable ℚ K
  have : Algebra.IsIntegral ℚ B := ⟨fun b =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℚ B K) (IsFractionRing.injective B K)).1
      (Algebra.IsIntegral.isIntegral _)⟩
  exact isField_of_isIntegral_of_isField' (R := ℚ) (Field.toIsField ℚ)

/-- **The initial chart size without `exists_chart_atPrime`** (twin of
`eq_top_or_exists_chartDim`): a chart at `⊥` (`exists_chart_bot`) and the K primitive
`exists_smoothCert_of_smooth`; size `0` means `B` is a field (`isField_of_chart_bot_zero`). -/
theorem eq_top_or_exists_chartDim_bot [Algebra.Smooth ℚ B] (hB : Constructive.HasPres B)
    {𝔟 : Ideal B} (h𝔟 : 𝔟 ≠ ⊥) : 𝔟 = ⊤ ∨ ∃ N, ChartDim B N := by
  obtain ⟨n, ⟨c⟩⟩ := exists_chart_bot (B := B)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left
    have hF := isField_of_chart_bot_zero c
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔟
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel hx0
    exact Ideal.eq_top_of_isUnit_mem _ hx (IsUnit.of_mul_eq_one y hy)
  · exact Or.inr ⟨n, exists_smoothCert_of_smooth hB ⊥ hn c⟩


end BezoutCounterexample.Principalization
