import BezoutCounterexample.Torsor
import BezoutCounterexample.Principalization.ChainLiftChartDimUCert
import BezoutCounterexample.Principalization.ChainLiftSmoothCertK
import BezoutCounterexample.Constructive.Enum
import BezoutCounterexample.Principalization.VertOKPt

/-!
# Section 4.3: bounding the length of the invariant (Lemma 4.4)

Termination requires a bound on the number of nonzero entries of the invariants; this is not
automatic, because the dimension of the rings grows.

Fix `N ≥ 0`. For a smooth finitely generated `ℚ`-domain `B`, a nonzero ideal `𝔟 ⊆ B`, and an integer
`m ≥ 0`, the condition `(⋆_N)` on `(B, 𝔟, m)` (`StarC N 𝔟 m`) is:
1. `B` has chart size `k ≤ N + m` (`ChartDim B k`; D3.7b, in place of `dim B ≤ N + m`);
2. for every maximal ideal `𝔪 ⊇ 𝔟` there are `ℚ`-derivations `δ₁, …, δ_m` of `B` and elements
   `z₁, …, z_m ∈ B` with `δⱼ(𝔟) ⊆ 𝔟` for every `j` and `det(δⱼ(z_q)) ∉ 𝔪` (the determinant of the
   empty matrix is `1`).

By Lemma 3.7(2), if `(B, 𝔟, m)` satisfies `(⋆_N)`, then every invariant of `𝔟` has at most `N`
nonzero entries (`StarC.numNonzero_inv_le`). The triple `(A, I, 0)` satisfies `(⋆_N)` when `A` has chart size `N`
(`star_initial`; `eq_top_or_exists_chartDim` supplies `N`).

**Lemma 4.4** (`lem:length-control`): `length_control_divisorial`, `length_control_torsor`.
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization

/-- The condition `(⋆_N)` on `(B, 𝔟, m)`, with chart sizes (D3.7b: `ChartDim` in place of
`ringKrullDim`; the witness `k` is what the stages need, the `≤` keeps the slack). -/
structure StarC (N : ℕ) {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B]
    (𝔟 : Ideal B) (m : ℕ) : Prop where
  dim_le : ∃ k, ChartDim B k ∧ k ≤ N + m
  /-- at the explicit points above `𝔟` (D3.8: the torsor step decides a coordinate off the point,
  `torsor_vertOKPt`) -/
  derivations : ∀ q : Pt B, 𝔟 ≤ q.ker →
    ∃ (δ : Fin m → Derivation ℚ B B) (z : Fin m → B), (∀ j, ∀ f ∈ 𝔟, δ j f ∈ 𝔟) ∧
      (Matrix.of fun j q => δ j (z q)).det ∉ q.ker

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B]

/-- **Lemma 3.7(2) with chart sizes**: as `numNonzero_inv_add_le`, with the chart size `k` of `B`
in place of `ringKrullDim B` (the chart of the run has size `k`, `ChartDim.card_eq`). -/
theorem numNonzero_inv_add_le_chart {I : Ideal B} (hI : I ≠ ⊥) {𝔪 : Ideal B} [𝔪.IsMaximal]
    (hI𝔪 : I ≤ 𝔪) {kd : ℕ} (hkd : ChartDim B kd) {m : ℕ} (δ : Fin m → Derivation ℚ B B)
    (hδ : ∀ j, ∀ f ∈ I, δ j f ∈ I) (z : Fin m → B)
    (hz : (Matrix.of fun j q => δ j (z q)).det ∉ 𝔪) :
    numNonzero (inv I 𝔪) + m ≤ kd := by
  obtain ⟨n, e, he, hext⟩ := invAt_inv hI hI𝔪
  obtain ⟨J, -, -⟩ := he.1
  obtain ⟨k, ck, hrun, hadm, hck, hsupp⟩ :=
    he.exists_run (Iloc_ne_bot hI 𝔪) (Iloc_le hI𝔪) J.c J.centred
  have hunit : IsUnit (Matrix.of fun j l => derivLoc (δ j) 𝔪
      (algebraMap B (Localization.AtPrime 𝔪) (z l))).det := by
    rw [det_extLoc]
    exact IsLocalization.map_units (Localization.AtPrime 𝔪) (⟨_, hz⟩ : 𝔪.primeCompl)
  have hkm := length_le_of_derivations hrun hadm hck he.nonneg he.anti hsupp
    (fun j => derivLoc (δ j) 𝔪)
    (fun j g hg => deriv_mem_map (algebraMap B _) (derivLoc (δ j) 𝔪) (δ j)
      (fun r => extLoc_algebraMap _ (δ j) r) (hδ j) hg) _ hunit
  have hk : numNonzero (inv I 𝔪) = k := by
    rw [← hext]
    unfold numNonzero
    have : {i | ext0 e i ≠ 0} = ↑(Finset.range k) := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.coe_range, Set.mem_Iio]
      by_cases hin : i < n
      · rw [show ext0 e i = e ⟨i, hin⟩ by simp [ext0, hin]]
        exact hsupp ⟨i, hin⟩
      · rw [show ext0 e i = 0 by simp [ext0, hin]]
        simp only [ne_eq, not_true_eq_false, false_iff, not_lt]
        omega
    rw [this, Set.ncard_coe_finset, Finset.card_range]
  rw [hk, ← hkd.card_eq J.c]
  exact hkm

/-- By Lemma 3.7(2), under `(⋆_N)` every invariant of `𝔟` has at most `N` nonzero entries. -/
theorem StarC.numNonzero_inv_le {N m : ℕ} {𝔟 : Ideal B} (h : StarC N 𝔟 m) (h𝔟 : 𝔟 ≠ ⊥)
    (𝔪 : Ideal B) [𝔪.IsMaximal] (h𝔟𝔪 : 𝔟 ≤ 𝔪) : numNonzero (inv 𝔟 𝔪) ≤ N := by
  -- classical (off the path): the point of `𝔪`
  have hk𝔪 := Pt.ker_ofIsMaximal 𝔪
  obtain ⟨δ, z, hδ, hdet⟩ := h.derivations (Pt.ofIsMaximal 𝔪) (by rw [hk𝔪]; exact h𝔟𝔪)
  rw [hk𝔪] at hdet
  obtain ⟨k, hk, hkN⟩ := h.dim_le
  have := numNonzero_inv_add_le_chart h𝔟 h𝔟𝔪 hk δ hδ z hdet
  omega

/-- The triple `(B, 𝔟, 0)` satisfies `(⋆_N)` when `B` has chart size `N`. -/
theorem star_initial {N : ℕ} (hN : ChartDim B N) (𝔟 : Ideal B) : StarC N 𝔟 0 := by
  refine ⟨⟨N, hN, le_rfl⟩, fun q _ => ⟨Fin.elim0, Fin.elim0, fun j => Fin.elim0 j, ?_⟩⟩
  rw [Matrix.det_isEmpty]
  exact (Ideal.ne_top_iff_one _).1 (Pt.ker_isMaximal q).ne_top

/-- The chart size of the initial ring, classically: a chart at `⊥` (`exists_chart_atPrime`) and the
K primitive `exists_smoothCert_of_smooth`. Chart size `0` means `B` is a field, so a nonzero `𝔟`
is `⊤`. -/
theorem eq_top_or_exists_chartDim (hB : Constructive.HasPres B) {𝔟 : Ideal B} (h𝔟 : 𝔟 ≠ ⊥) :
    𝔟 = ⊤ ∨ ∃ N, ChartDim B N := by
  obtain ⟨n, ⟨c⟩⟩ := exists_chart_atPrime (⊥ : Ideal B)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left
    have h0 : ringKrullDim B = 0 := by exact_mod_cast chart_size_eq_ringKrullDim c
    have : Ring.KrullDimLE 0 B := Ring.krullDimLE_iff.2 (by rw [h0]; rfl)
    have hF := Ring.KrullDimLE.isField_of_isDomain (R := B)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔟
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel hx0
    exact Ideal.eq_top_of_isUnit_mem _ hx (IsUnit.of_mul_eq_one y hy)
  · exact Or.inr ⟨n, exists_smoothCert_of_smooth hB ⊥ hn c⟩

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

namespace PrincipalizationData

variable (S : PrincipalizationData A)

/-- **Lemma 4.4** (`lem:length-control`), divisorial step: if `(A, I, m)` satisfies `(⋆_N)`, then
so does `(A, I₁, m)`, `I₁ = (I : π^a)`. -/
theorem length_control_divisorial [Fact (Constructive.HasPres A)] {N m : ℕ} (hS : StarC N S.I m) (hk : S.k = 1) {a : ℕ}
    (ha : S.e 0 = 1 / (a : ℚ)) : StarC N (S.divI₁ a) m :=
  ⟨hS.dim_le, div_vertOKPt S.ne_bot S.hmax S.h𝔭c S.d_pos S.hw (S.divisorial_𝔭_eq hk)
    (S.a_pos hk ha) hS.derivations⟩

/-- **Lemma 4.4** (`lem:length-control`), torsor step: if `(A, I, m)` satisfies `(⋆_N)`, then
`(U, I₁, m + ℓ + 1)` satisfies `(⋆_N)`. `U` has chart size `k + 1 + ℓ` (`chartDim_U_cert`; this
replaces `ringKrullDim_U`). -/
theorem length_control_torsor [Constructive.Enum A] [Fact (Constructive.HasPres A)] {N m : ℕ} (hS : StarC N S.I m)
    (_hk : 2 ≤ S.k) : StarC N S.I₁ (m + S.ℓ + 1) := by
  obtain ⟨k, hk, hkN⟩ := hS.dim_le
  refine ⟨⟨k + 1 + S.ℓ, chartDim_U_cert S hk Constructive.Enum.en Constructive.Enum.hen, by omega⟩, ?_⟩
  -- the lifted, Euler and vertical derivations, at explicit points (`torsor_vertOKPt`)
  exact torsor_vertOKPt S.ne_bot S.hmax S.h𝔭c S.d_pos S.hw S.π_mem_fil hS.derivations

end PrincipalizationData

end BezoutCounterexample
