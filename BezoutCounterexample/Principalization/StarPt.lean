import BezoutCounterexample.LengthControl
import BezoutCounterexample.Principalization.ChainLiftChartDimU
import BezoutCounterexample.Principalization.RunPos
import BezoutCounterexample.Principalization.SpreadPos

/-!
# The condition `(⋆_N)` with chart sizes (D3.5, leaf)

`Star N 𝔟 m` (LengthControl) bounds `ringKrullDim B`, and its length bound
`Star.numNonzero_inv_le` goes through `inv`, `numNonzero` and the classical Method 1 run
(`numNonzero_inv_add_le`). Here (`docs/d3-design.md` §5, D3.5, decided by coll-01):

* `StarC N 𝔟 m` (defined in LengthControl since D3.7b, where it replaced `Star`):
  `dim_le : ∃ k, ChartDim B k ∧ k ≤ N + m`; `derivations` at every maximal ideal, so in particular
  at the kernels of explicit points;
* `invAt_eq_zero_of_derivations_pt`: at an explicit point `q`, an invariant `v` vanishes from
  index `n - m` on, when the chart size is `n` and `m` derivations have a unit determinant at `q`
  (`IsInv.exists_run_pos` with `Pt.dec_local`, then `length_le_of_derivations`);
* `StarC.eq_zero_pt`: under `(⋆_N)`, invariants at points of `V(𝔟)` vanish from index `N` on;
* `star_initial_pt (hN : ChartDim B N) : StarC N 𝔟 0` (`N ≥ 1` in use: `ChartDim B 0` is false);
* `StarC.of_star_divisorial`, `length_control_torsor_pt`: Lemma 4.4 with chart sizes
  (the torsor step through `chartDim_U`, coll-8a).

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization Constructive

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B]

/-- **The length bound at an explicit point**: with chart size `n` and `m` derivations stabilizing
`I` with a unit determinant at `q`, an invariant at `q` vanishes from index `n - m` on. -/
theorem invAt_eq_zero_of_derivations_pt {I : Ideal B} (hI : I ≠ ⊥) (l : List B)
    (hl : I = lspan l) (q : Pt B) [Fact (PolyIndNoeth (Localization.AtPrime q.ker))]
    (hIq : I ≤ q.ker) {v : ℕ → ℚ} (hv : InvAt I q.ker v) {n : ℕ} (hn : ChartDim B n) {m : ℕ}
    (δ : Fin m → Derivation ℚ B B) (hδ : ∀ j, ∀ f ∈ I, δ j f ∈ I) (z : Fin m → B)
    (hz : (Matrix.of fun j q => δ j (z q)).det ∉ q.ker) : ∀ i, n ≤ i + m → v i = 0 := by
  obtain ⟨n', e, he, rfl⟩ := hv
  obtain ⟨J, -, -⟩ := he.1
  have hn' : n' = n := hn.card_eq J.c
  subst hn'
  obtain ⟨k, ck, hrun, hadm, hck, hsupp⟩ :=
    he.exists_run_pos q.dec_local _ (hlR q.ker I l hl) (Iloc_ne_bot hI q.ker) (Iloc_le hIq)
      J.c J.centred
  have hunit : IsUnit (Matrix.of fun j l => derivLoc (δ j) q.ker
      (algebraMap B (Localization.AtPrime q.ker) (z l))).det := by
    rw [det_extLoc]
    exact IsLocalization.map_units (Localization.AtPrime q.ker) (⟨_, hz⟩ : q.ker.primeCompl)
  have hkm := length_le_of_derivations hrun hadm hck he.nonneg he.anti hsupp
    (fun j => derivLoc (δ j) q.ker)
    (fun j g hg => deriv_mem_map (algebraMap B _) (derivLoc (δ j) q.ker) (δ j)
      (fun r => extLoc_algebraMap _ (δ j) r) (hδ j) hg) _ hunit
  intro i hi
  simp only [ext0]
  rcases Nat.lt_or_ge i n' with hin | hin
  · rw [dite_eq_left hin]
    rcases (inferInstance : Decidable (e ⟨i, hin⟩ = 0)) with h | h
    · exact absurd ((hsupp ⟨i, hin⟩).1 h) (show ¬ (i < k) by omega)
    · exact h
  · rw [dite_eq_right (by omega)]

/-- **Under `(⋆_N)`, invariants at points of `V(𝔟)` vanish from index `N` on.** -/
theorem StarC.eq_zero_pt {N m : ℕ} {𝔟 : Ideal B} (h : StarC N 𝔟 m) (h𝔟 : 𝔟 ≠ ⊥) (l : List B)
    (hl : 𝔟 = lspan l) (q : Pt B) [Fact (PolyIndNoeth (Localization.AtPrime q.ker))]
    (h𝔟q : 𝔟 ≤ q.ker) {v : ℕ → ℚ} (hv : InvAt 𝔟 q.ker v) : ∀ i, N ≤ i → v i = 0 := by
  obtain ⟨k, hk, hkN⟩ := h.dim_le
  obtain ⟨δ, z, hδ, hdet⟩ := h.derivations q h𝔟q
  intro i hi
  exact invAt_eq_zero_of_derivations_pt h𝔟 l hl q h𝔟q hv hk δ hδ z hdet i (by omega)

/-- The triple `(B, 𝔟, 0)` satisfies `(⋆_N)` when `B` has chart size `N`. -/
theorem star_initial_pt {N : ℕ} (hN : ChartDim B N) (𝔟 : Ideal B) : StarC N 𝔟 0 := by
  refine ⟨⟨N, hN, le_rfl⟩, fun q _ => ⟨Fin.elim0, Fin.elim0, fun j => Fin.elim0 j, ?_⟩⟩
  rw [Matrix.det_isEmpty]
  exact (Ideal.ne_top_iff_one _).1 (Pt.ker_isMaximal q).ne_top

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

namespace PrincipalizationData

variable (S : PrincipalizationData A)

/-- **Lemma 4.4**, divisorial step, with chart sizes (same ring). -/
theorem length_control_divisorial_pt [Fact (Constructive.HasPres A)] {N m : ℕ}
    (hS : StarC N S.I m) (hk : S.k = 1) {a : ℕ} (ha : S.e 0 = 1 / (a : ℚ)) :
    StarC N (S.divI₁ a) m :=
  ⟨hS.dim_le, div_vertOKPt S.ne_bot S.hmax S.h𝔭c S.d_pos S.hw (S.divisorial_𝔭_eq hk)
    (S.a_pos hk ha) hS.derivations⟩

/-- **Lemma 4.4**, torsor step, with chart sizes: `U` has chart size `k + 1 + ℓ`
(`chartDim_U`). -/
theorem length_control_torsor_pt [Constructive.Enum A] [Fact (Constructive.HasPres A)] (hz : ∀ a : A, a = 0 ∨ a ≠ 0)
    (hU : HasPres S.U) {N m : ℕ} (hS : StarC N S.I m) :
    StarC N S.I₁ (m + S.ℓ + 1) := by
  obtain ⟨k, hk, hkN⟩ := hS.dim_le
  refine ⟨⟨k + 1 + S.ℓ, chartDim_U S hz hU hk, by omega⟩, ?_⟩
  exact torsor_vertOKPt S.ne_bot S.hmax S.h𝔭c S.d_pos S.hw S.π_mem_fil hS.derivations

end PrincipalizationData

end BezoutCounterexample
