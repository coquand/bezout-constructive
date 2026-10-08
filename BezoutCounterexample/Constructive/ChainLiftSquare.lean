import Mathlib
import BezoutCounterexample.Constructive.ChainLiftPolyChart
import BezoutCounterexample.Constructive.NoethBar

/-!
# Certified square pieces (§2.2, Jacobian-minor cover)

A presentation `B = ℚ[Y₁…Y_N]/(G)` with `N = m + n`, the relations cleared of denominators
(`G` a list of integer polynomials). A *square piece* on `D(h)` is certified by two congruences
modulo `(G)`, checked algebraically (ideal membership, decidable by Gröbner, `HasPres.mem_dec`):

* (i) `det (∂ⱼ Fᵢ) · U ≡ hᵉ` mod `(G)` (`detc`), where `F` = `m` relations `F_eq` (members of
  `(G)`) followed by the `n` chart coordinates (polynomials);
* (ii) `h^f · g ∈ (F_eq)` for every `g ∈ G` (`genc`). On `D(Δ)` the zero set of `F_eq` may have
  extra components besides `V(G)`; `h` includes a separating element, so that (ii) holds.

`SquarePiece.toPolyChart`: such a piece is a `PolyChart`. All constants come from
`poly_bdd_lip`, and inverses of `h` at points with `|h| ≥ θ_lo` come from `exists_inv_pos`.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {N : ℕ}

/-- Members of `(G)` vanish at real points of `G`. -/
theorem evalR_eq_zero_of_mem {G : List (MvPolynomial (Fin N) ℤ)} {x : Fin N → ℝ} (hx : PtG G x)
    {P : MvPolynomial (Fin N) ℤ} (hP : P ∈ lspan G) : evalR x P = 0 := by
  have hle : lspan G ≤ RingHom.ker (eval₂Hom (Int.castRingHom ℝ) x) :=
    Ideal.span_le.2 fun g hg => RingHom.mem_ker.2 (hx g hg)
  exact RingHom.mem_ker.1 (hle hP)

/-- Inverses at points bounded away from `0`, with a bound. -/
theorem exists_inv_of_le_abs {a θ : ℝ} (hθ : 0 < θ) (ha : θ ≤ |a|) :
    ∃ t, a * t = 1 ∧ |t| * θ ≤ 1 := by
  obtain ⟨t₀, ht₀, hθt⟩ := exists_inv_pos hθ
  have h1 : 1 ≤ t₀ * |a| := by
    calc (1 : ℝ) = θ * t₀ := hθt.symm
      _ ≤ |a| * t₀ := mul_le_mul_of_nonneg_right ha ht₀.le
      _ = t₀ * |a| := mul_comm _ _
  rcases sign_split ht₀ h1 with hpos | hneg
  · obtain ⟨t, ht, hat⟩ := exists_inv_pos hpos
    refine ⟨t, hat, ?_⟩
    rw [abs_of_pos ht]
    rw [abs_of_pos hpos] at ha
    calc t * θ ≤ t * a := mul_le_mul_of_nonneg_left ha ht.le
      _ = 1 := by rw [mul_comm]; exact hat
  · obtain ⟨t, ht, hat⟩ := exists_inv_pos (neg_pos.2 hneg)
    refine ⟨-t, by linarith, ?_⟩
    rw [abs_neg, abs_of_pos ht]
    rw [abs_of_neg hneg] at ha
    calc t * θ ≤ t * -a := mul_le_mul_of_nonneg_left ha ht.le
      _ = 1 := by rw [mul_comm]; exact hat

/-- The polynomial Jacobian matrix. -/
noncomputable def jacPoly (F : Fin N → MvPolynomial (Fin N) ℤ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) ℤ) :=
  Matrix.of fun i j => pderiv j (F i)

lemma evalR_det_jacPoly (F : Fin N → MvPolynomial (Fin N) ℤ) (x : Fin N → ℝ) :
    evalR x (jacPoly F).det = Matrix.det (Jac F x : Matrix (Fin N) (Fin N) ℝ) := by
  have := RingHom.map_det (eval₂Hom (Int.castRingHom ℝ) x) (jacPoly F)
  rw [show evalR x (jacPoly F).det = eval₂Hom (Int.castRingHom ℝ) x (jacPoly F).det from rfl, this]
  rfl

/-- A certified square piece of the presentation `G`. -/
structure SquarePiece (m n : ℕ) (G : List (MvPolynomial (Fin (m + n)) ℤ)) where
  F : Fin (m + n) → MvPolynomial (Fin (m + n)) ℤ
  hn : 0 < n
  eqmem : ∀ i : Fin m, F (Fin.castAdd n i) ∈ lspan G
  h : MvPolynomial (Fin (m + n)) ℤ
  e : ℕ
  f : ℕ
  U : MvPolynomial (Fin (m + n)) ℤ
  detc : (jacPoly F).det * U - h ^ e ∈ lspan G
  genc : ∀ g ∈ G, h ^ f * g ∈ lspan (List.ofFn fun i : Fin m => F (Fin.castAdd n i))

namespace SquarePiece

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)} (S : SquarePiece m n G)

/-- **A certified square piece is a polynomial chart**, for any thresholds `0 < θ_lo < θ`. -/
noncomputable def toPolyChart (θ θlo : ℝ) (hθlo : 0 < θlo) (hθ : θlo < θ) : PolyChart m n where
  G := G
  F := S.F
  h := S.h
  hn := S.hn
  θ := θ
  θlo := θlo
  hθlo := hθlo
  hθ := hθ
  eqs := fun x hx i => evalR_eq_zero_of_mem hx (S.eqmem i)
  gen := by
    intro x hhx heq g hg
    obtain ⟨t, hht, -⟩ := exists_inv_of_le_abs hθlo hhx
    have hP : PtG (List.ofFn fun i : Fin m => S.F (Fin.castAdd n i)) x := by
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hq
      exact heq i
    have h0 := evalR_eq_zero_of_mem hP (S.genc g hg)
    rw [evalR_mul] at h0
    have hpow : evalR x (S.h ^ S.f) = evalR x S.h ^ S.f := map_pow (eval₂Hom _ x) _ _
    rw [hpow] at h0
    calc evalR x g = ((evalR x S.h * t) ^ S.f) * evalR x g := by rw [hht, one_pow, one_mul]
      _ = t ^ S.f * (evalR x S.h ^ S.f * evalR x g) := by ring
      _ = 0 := by rw [h0, mul_zero]
  det := by
    intro C
    obtain ⟨Ub, -, hUb, -, hbU, -⟩ := poly_bdd_lip |C| (abs_nonneg C) S.U
    obtain ⟨t₀, ht₀, hθt₀⟩ := exists_inv_pos hθlo
    refine ⟨Ub * t₀ ^ S.e, by positivity, fun x hxC hx hhx => ?_⟩
    obtain ⟨t, hht, htθ⟩ := exists_inv_of_le_abs hθlo hhx
    have hc := evalR_eq_zero_of_mem hx S.detc
    have hpow : evalR x (S.h ^ S.e) = evalR x S.h ^ S.e := map_pow (eval₂Hom _ x) _ _
    rw [show evalR x ((jacPoly S.F).det * S.U - S.h ^ S.e) =
        evalR x (jacPoly S.F).det * evalR x S.U - evalR x (S.h ^ S.e) from by
          simp only [evalR, eval₂_sub, eval₂_mul], hpow, evalR_det_jacPoly] at hc
    refine ⟨evalR x S.U * t ^ S.e, ?_, ?_⟩
    · calc Matrix.det (Jac S.F x : Matrix (Fin (m + n)) (Fin (m + n)) ℝ) * (evalR x S.U * t ^ S.e)
          = (evalR x S.h * t) ^ S.e := by rw [mul_pow, ← mul_assoc, sub_eq_zero.1 hc]
        _ = 1 := by rw [hht, one_pow]
    · have ht : |t| ≤ t₀ := by
        calc |t| = |t| * (θlo * t₀) := by rw [hθt₀, mul_one]
          _ = (|t| * θlo) * t₀ := by ring
          _ ≤ 1 * t₀ := mul_le_mul_of_nonneg_right htθ ht₀.le
          _ = t₀ := one_mul _
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hbU x fun k => (hxC k).trans (le_abs_self C))
        (pow_le_pow_left₀ (abs_nonneg _) ht _) (by positivity) ((abs_nonneg _).trans
          (hbU x fun k => (hxC k).trans (le_abs_self C)))

end SquarePiece

end BezoutCounterexample.Constructive
