import BezoutCounterexample.Principalization.ChartDim

/-!
# Chart size of the initial ring and uniqueness of chart size (Task A, C5)

* `certA₀`: the one-piece smoothness certificate of `ℚ[Y₀, Y₁]` (`m = 0`, `G = []`,
  `F = (Y₀, Y₁)`, `h = 1`, cover `1 = 1 · 1`);
* `chartDim_A₀ : ChartDim A₀ 2` (`A₀ = ℚ[x, y]`), the dimension field of the initial stage;
* `existsUnique_chartDim`: for a domain with some certificate, the chart size is unique, so it can
  be read as data by `uniqueChoice`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive MvPolynomial

/-- The Jacobian of the coordinate functions is the identity. -/
lemma jacPoly_X {N : ℕ} : jacPoly (fun i : Fin N => (X i : MvPolynomial (Fin N) ℤ)) = 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [jacPoly, Matrix.of_apply, pderiv_X, Pi.single_apply, Matrix.one_apply]

/-- The square piece of `ℚ[Y₀, Y₁]`: no equations, coordinates `Y₀, Y₁`, `h = 1`. -/
def pieceA₀ : SquarePiece 0 2 ([] : List (MvPolynomial (Fin (0 + 2)) ℤ)) where
  F := fun i => X i
  hn := by norm_num
  eqmem := fun i => i.elim0
  h := 1
  e := 0
  f := 0
  U := 1
  detc := by rw [jacPoly_X, Matrix.det_one, pow_zero, mul_one, sub_self]; exact Ideal.zero_mem _
  genc := fun g hg => by simp at hg

/-- **The one-piece certificate of `ℚ[Y₀, Y₁]`.** -/
def certA₀ : SmoothCert 0 2 ([] : List (MvPolynomial (Fin (0 + 2)) ℤ)) where
  K := 1
  P := fun _ => pieceA₀
  C := 1
  hC := one_pos
  u := fun _ => 1
  cover := by
    simp only [Finset.univ_unique, Finset.sum_singleton, pieceA₀, mul_one, Nat.cast_one, sub_self]
    exact Ideal.zero_mem _

/-- `ℚ[Y₀, Y₁] ⧸ (0) ≃ A₀`. -/
def qbEquivA₀ : SmoothCert.QB ([] : List (MvPolynomial (Fin (0 + 2)) ℤ)) ≃+* A₀ :=
  (Ideal.quotEquivOfEq (by simp [lspan])).trans (RingEquiv.quotientBot _)

/-- **`A₀ = ℚ[x, y]` has chart size `2`.** -/
theorem chartDim_A₀ : ChartDim A₀ 2 := ⟨0, [], ⟨qbEquivA₀⟩, ⟨certA₀⟩⟩

/-- **Uniqueness of chart size** (domains): read as data by `uniqueChoice`. -/
theorem existsUnique_chartDim {A : Type} [CommRing A] [Algebra ℚ A] [IsDomain A]
    (h : ∃ N, ChartDim A N) : ∃! N, ChartDim A N := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, hN, fun N' hN' => (ChartDim.unique hN hN').symm⟩

end BezoutCounterexample.Principalization
