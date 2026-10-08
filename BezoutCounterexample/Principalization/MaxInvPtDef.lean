import BezoutCounterexample.Principalization.MaxLocus
import BezoutCounterexample.Principalization.Points

/-!
# The maximal invariant bounded at explicit points (D3.8 (A), leaf)

`IsMaxInvPt I v₀`: `toLex v₀ ≤ toLex v` for every invariant `v` at an explicit point of `V(I)`. Since
D3.8 (A) this is the type of the hypothesis `hmax` of the engine (`compFil hI hmax h𝔭 d`, …), in
place of the bound at every maximal ideal (which needs Zariski's lemma to compare with the points).

* `maxPt_of_max`: the bound at maximal ideals gives the point form (constructive);
* `IsMaxInvPt.unique`: two point-maximal invariants attained at explicit points are equal;
* `Pt.ofIsMaximal`, `Pt.ker_ofIsMaximal`, `InvAt.of_eq` (moved from MaxLocusPtCore) and
  `IsMaxInvPt.toMax` (classical, off the path): back to maximal ideals by
  `Pt.ofIsMaximal`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- **The maximal invariant, bounded at explicit points.** -/
def IsMaxInvPt (I : Ideal A) (v₀ : ℕ → ℚ) : Prop :=
  ∀ q : Pt A, I ≤ q.ker → ∀ v, InvAt I q.ker v → toLex v₀ ≤ toLex v

/-- The bound at maximal ideals gives the point form. -/
theorem maxPt_of_max {I : Ideal A} {v₀ : ℕ → ℚ}
    (h : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v) :
    IsMaxInvPt I v₀ :=
  fun q hIq v hv => h q.ker hIq v hv

/-- **Uniqueness** of a point-maximal invariant attained at an explicit point. -/
theorem IsMaxInvPt.unique {I : Ideal A} {v₀ v₁ : ℕ → ℚ} (h₀ : IsMaxInvPt I v₀)
    (a₀ : ∃ q : Pt A, I ≤ q.ker ∧ InvAt I q.ker v₀) (h₁ : IsMaxInvPt I v₁)
    (a₁ : ∃ q : Pt A, I ≤ q.ker ∧ InvAt I q.ker v₁) : v₀ = v₁ := by
  obtain ⟨q₀, hI₀, hv₀⟩ := a₀
  obtain ⟨q₁, hI₁, hv₁⟩ := a₁
  exact toLex.injective (le_antisymm (h₀ q₁ hI₁ v₁ hv₁) (h₁ q₀ hI₀ v₀ hv₀))

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- The point of a maximal ideal of a finite type `ℚ`-algebra (classical: Zariski's lemma and
excluded middle for the zero test). Comparison only. -/
def Pt.ofIsMaximal [Algebra.FiniteType ℚ A] (𝔪 : Ideal A) [𝔪.IsMaximal] : Pt A :=
  letI := Ideal.Quotient.field 𝔪
  haveI : Module.Finite ℚ (A ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ 𝔪)
  { L := A ⧸ 𝔪
    z := Ideal.Quotient.mkₐ ℚ 𝔪
    dec := fun x => Classical.em (x = 0) }

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma Pt.ker_ofIsMaximal [Algebra.FiniteType ℚ A] (𝔪 : Ideal A) [𝔪.IsMaximal] :
    (Pt.ofIsMaximal 𝔪).ker = 𝔪 := by
  ext x
  show (Ideal.Quotient.mkₐ ℚ 𝔪) x = 0 ↔ x ∈ 𝔪
  exact Ideal.Quotient.eq_zero_iff_mem

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma InvAt.of_eq {I 𝔪 𝔪' : Ideal A} [𝔪.IsPrime] [𝔪'.IsPrime] (h : 𝔪 = 𝔪') {v : ℕ → ℚ}
    (hv : InvAt I 𝔪 v) : InvAt I 𝔪' v := by
  subst h; exact hv

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- **Back to maximal ideals** (classical, off the path: Zariski's lemma through
`Pt.ofIsMaximal`): the bound at explicit points is the bound at every maximal ideal. -/
theorem IsMaxInvPt.toMax [Algebra.FiniteType ℚ A] {I : Ideal A} {v₀ : ℕ → ℚ}
    (h : IsMaxInvPt I v₀) :
    ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v := by
  intro 𝔪 _ hI v hv
  have hk := Pt.ker_ofIsMaximal 𝔪
  exact h (Pt.ofIsMaximal 𝔪) (by rw [hk]; exact hI) v (InvAt.of_eq hk.symm hv)

end BezoutCounterexample.Principalization
