import Mathlib
import BezoutCounterexample.Constructive.ChainLiftCertRet

/-!
# Square systems: the local models of the Rees layer (Task B, S3)

A *square system* `F : Fin (m + n) → ℤ[Y_{m+n}]` (the first `m` entries are equations, the last
`n` coordinates) presents the complete intersection `sysEq F = (F₀ … F_{m-1})`. With
`J = ∂F` and `h = det J`, everything is exact (no reduction modulo the ideal):

* `SquarePiece.ofSystem`: a piece of `sysEq F` with `h = det J`, `e = 1`, `f = 0`, `U = 1`;
* `exists_conormalRet_system`: retraction data of `sysEq F` with multiplier `det J`;
* `ChartData.ofSystem`: chart data with coordinates the last `n` entries, `B` and `V` the
  equation and coordinate columns of `adj J`, multiplier `det J` (`adj J · J = J · adj J = det J`).

The Rees models (weighted chart, Laurent) are square systems with block-triangular Jacobians; these
data are transported to the global presentation by `ChainLiftRetTransport` and the chart-data
transport.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial Matrix

variable {m n : ℕ} (F : Fin (m + n) → MvPolynomial (Fin (m + n)) ℤ)

/-- The equations of a square system. -/
noncomputable def sysEq : List (MvPolynomial (Fin (m + n)) ℤ) :=
  List.ofFn fun i : Fin m => F (Fin.castAdd n i)

lemma sysEq_length : (sysEq F).length = m := List.length_ofFn

lemma sysEq_get (r : Fin (sysEq F).length) :
    (sysEq F).get r = F (Fin.castAdd n (Fin.cast (sysEq_length F) r)) := by
  exact List.get_ofFn (fun i : Fin m => F (Fin.castAdd n i)) r

lemma mem_lspan_sysEq (i : Fin m) : F (Fin.castAdd n i) ∈ lspan (sysEq F) :=
  Ideal.subset_span (List.mem_ofFn.2 ⟨i, rfl⟩)

/-- **A square system is a piece of its own equations.** -/
noncomputable def SquarePiece.ofSystem (hn : 0 < n) : SquarePiece m n (sysEq F) where
  F := F
  hn := hn
  eqmem := mem_lspan_sysEq F
  h := (jacPoly F).det
  e := 1
  f := 0
  U := 1
  detc := by simp
  genc := fun g hg => by rw [pow_zero, one_mul]; exact Ideal.subset_span hg

/-- **Retraction data of a square system**, with multiplier `det J`. -/
theorem exists_conormalRet_system (hn : 0 < n) :
    ∃ a, ConormalRet (sysEq F) (jacPoly F).det a := by
  have := (SquarePiece.ofSystem F hn).mem_retIdeal
  simp only [SquarePiece.ofSystem, add_zero, pow_one] at this
  exact this

lemma matCong_of_eq {a b : Type*} {R : Type*} [CommRing R] {I : Ideal R} {A A' : Matrix a b R}
    (h : A = A') : MatCong I A A' := fun i j => by rw [h, sub_self]; exact Ideal.zero_mem _

/-- The equation columns of `adj J`, indexed by the equation list. -/
noncomputable def sysB : Matrix (Fin (m + n)) (Fin (sysEq F).length) (MvPolynomial (Fin (m + n)) ℤ) :=
  Matrix.of fun u r => (jacPoly F).adjugate u (Fin.castAdd n (Fin.cast (sysEq_length F) r))

/-- The coordinate columns of `adj J`. -/
noncomputable def sysV : Matrix (Fin (m + n)) (Fin n) (MvPolynomial (Fin (m + n)) ℤ) :=
  Matrix.of fun u i => (jacPoly F).adjugate u (Fin.natAdd m i)

lemma jacG_sysEq (r : Fin (sysEq F).length) (w : Fin (m + n)) :
    jacG (sysEq F) r w = jacPoly F (Fin.castAdd n (Fin.cast (sysEq_length F) r)) w := by
  simp only [jacG, jacPoly, Matrix.of_apply]; rw [sysEq_get]

lemma jacX_sys (i : Fin n) (w : Fin (m + n)) :
    jacX (fun i => F (Fin.natAdd m i)) i w = jacPoly F (Fin.natAdd m i) w := by
  simp [jacX, jacPoly]

/-- Sums over the equation list, reindexed by `Fin m`. -/
lemma sum_sysEq {M : Type*} [AddCommMonoid M] (f : Fin m → M) :
    ∑ r : Fin (sysEq F).length, f (Fin.cast (sysEq_length F) r) = ∑ i, f i :=
  (finCongr (sysEq_length F)).sum_comp f

/-- **Chart data of a square system**, exact, with multiplier `det J`. -/
noncomputable def ChartData.ofSystem : ChartData (sysEq F) where
  x := fun i => F (Fin.natAdd m i)
  B := sysB F
  V := sysV F
  c := (jacPoly F).det
  hL := matCong_of_eq (by
    refine Matrix.ext fun u w => ?_
    have h := congrFun (congrFun (Matrix.adjugate_mul (jacPoly F)) u) w
    rw [Matrix.mul_apply, Fin.sum_univ_add] at h
    simp only [Matrix.add_apply, Matrix.mul_apply, sysB, sysV, Matrix.of_apply, jacG_sysEq,
      jacX_sys]
    rw [sum_sysEq F (fun i => (jacPoly F).adjugate u (Fin.castAdd n i) *
      jacPoly F (Fin.castAdd n i) w)]
    exact h)
  hD := matCong_of_eq (by
    refine Matrix.ext fun r i => ?_
    have h := congrFun (congrFun (Matrix.mul_adjugate (jacPoly F))
      (Fin.castAdd n (Fin.cast (sysEq_length F) r))) (Fin.natAdd m i)
    rw [Matrix.mul_apply] at h
    simp only [Matrix.mul_apply, sysV, Matrix.of_apply, jacG_sysEq, Matrix.zero_apply]
    rw [h, Matrix.smul_apply, Matrix.one_apply_ne (by
      intro e
      have h1 := congrArg Fin.val e
      have h2 := (Fin.cast (sysEq_length F) r).isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast] at h1 h2
      omega), smul_zero])
  hX := matCong_of_eq (by
    refine Matrix.ext fun i i' => ?_
    have h := congrFun (congrFun (Matrix.mul_adjugate (jacPoly F)) (Fin.natAdd m i))
      (Fin.natAdd m i')
    rw [Matrix.mul_apply] at h
    simp only [Matrix.mul_apply, sysV, Matrix.of_apply, jacX_sys]
    rw [h, Matrix.smul_apply, Matrix.smul_apply]
    by_cases hii : i = i'
    · subst hii; simp
    · rw [Matrix.one_apply_ne hii, Matrix.one_apply_ne (fun e => hii ((Fin.natAdd_inj m).1 e))])

end BezoutCounterexample.Constructive
