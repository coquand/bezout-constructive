import Mathlib
import BezoutCounterexample.Principalization.ChainLiftBridgeChart
import BezoutCounterexample.Principalization.ChainLiftBridgePres

/-!
# Integer chart data from a chart (bridge (b), over `ℤ`)

For an integer presentation `G` (`A₀ = ℚ[Y] ⧸ (G)`), a localization `S` of `A₀` with a chart and
integer polynomial coordinates `y`: a `Constructive.ChartData G` with `x = y`, whose multiplier
is `D λ det J` in `S` (`D` a positive integer, `λ ∈ M`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open scoped Matrix

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ))

/-- The rational presentation. -/
abbrev GQ : List (MvPolynomial (Fin (m + n)) ℚ) := G.map toQ

/-- Index transport `Fin G.length ≃ Fin (GQ G).length`. -/
abbrev eQ : Fin G.length ≃ Fin (GQ G).length := finCongr (List.length_map _).symm

lemma GQ_get (j : Fin G.length) : (GQ G).get (eQ G j) = toQ (G.get j) := by
  simp [GQ, eQ]

variable {S : Type*} [CommRing S] [Algebra ℚ S] [Algebra (Quo (GQ G)) S]
  [IsScalarTower ℚ (Quo (GQ G)) S] (Mo : Submonoid (Quo (GQ G))) [IsLocalization Mo S]
  (c : Chart S n)

include Mo in
/-- **Integer chart data from a chart.** -/
theorem chartData_of_chart (hn : 0 < n) (y : Fin n → MvPolynomial (Fin (m + n)) ℤ) :
    ∃ (T : ChartData G) (D : ℕ) (lam : MvPolynomial (Fin (m + n)) ℚ), T.x = y ∧ 0 < D ∧
      Ideal.Quotient.mk _ lam ∈ Mo ∧
      toS (S := S) (GQ G) (toQ T.c) =
        (D : S) * toS (GQ G) lam * (Jm (GQ G) c (fun j => toQ (y j))).det := by
  obtain ⟨B, V, c₀, lam, hlam, hL, hD, hX, hc⟩ :=
    chartQ (GQ G) Mo c hn (fun j => toQ (y j))
  set r := G.length
  -- 1. clear the denominators of `B`, `V`, `c₀`
  obtain ⟨D₁, q, hD₁, hq⟩ := exists_int_mul_fin (σ := Fin (m + n))
    (fun i : (Fin (m + n) × Fin r) ⊕ (Fin (m + n) × Fin n) ⊕ Unit =>
      Sum.elim (fun kj => B kj.1 (eQ G kj.2)) (Sum.elim (fun kl => V kl.1 kl.2) fun _ => c₀) i)
  set BZ : Matrix (Fin (m + n)) (Fin r) (MvPolynomial (Fin (m + n)) ℤ) :=
    Matrix.of fun k j => q (Sum.inl (k, j))
  set VZ : Matrix (Fin (m + n)) (Fin n) (MvPolynomial (Fin (m + n)) ℤ) :=
    Matrix.of fun k l => q (Sum.inr (Sum.inl (k, l)))
  set cZ := q (Sum.inr (Sum.inr ()))
  have hBZ : ∀ k j, toQ (BZ k j) = (D₁ : MvPolynomial (Fin (m + n)) ℚ) * B k (eQ G j) :=
    fun k j => hq (Sum.inl (k, j))
  have hVZ : ∀ k l, toQ (VZ k l) = (D₁ : MvPolynomial (Fin (m + n)) ℚ) * V k l :=
    fun k l => hq (Sum.inr (Sum.inl (k, l)))
  have hcZ : toQ cZ = (D₁ : MvPolynomial (Fin (m + n)) ℚ) * c₀ := hq (Sum.inr (Sum.inr ()))
  have hjG : ∀ j k, toQ (jacG G j k) = jacP (GQ G).get (eQ G j) k := fun j k => by
    simp only [jacG, jacP, Matrix.of_apply, GQ_get, toQ, pderiv_map]
  have hjX : ∀ l k, toQ (jacX y l k) = jacP (fun j => toQ (y j)) l k := fun l k => by
    simp only [jacX, jacP, Matrix.of_apply, toQ, pderiv_map]
  -- 2. the three congruences, as integer polynomials
  set ZL := BZ * jacG G + VZ * jacX y - cZ • (1 : Matrix (Fin (m + n)) (Fin (m + n)) _)
  set ZD := jacG G * VZ
  set ZX := jacX y * VZ - cZ • (1 : Matrix (Fin n) (Fin n) _)
  have hZL : ∀ k k', toQ (ZL k k') ∈ lspan (GQ G) := fun k k' => by
    have h := Ideal.mul_mem_left (lspan (GQ G)) (D₁ : MvPolynomial (Fin (m + n)) ℚ) (hL k k')
    convert h using 1
    simp only [ZL, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
      smul_eq_mul, map_sub, map_add, map_sum, map_mul, hBZ, hVZ, hcZ, hjG, hjX]
    rw [← (eQ G).sum_comp (fun j => B k j * jacP (GQ G).get j k')]
    by_cases hkk : k = k'
    · subst hkk; simp [Finset.mul_sum, mul_sub, mul_add, mul_assoc]; rfl
    · simp [Finset.mul_sum, mul_sub, mul_add, mul_assoc, Matrix.one_apply, hkk]; rfl
  have hZD : ∀ j l, toQ (ZD j l) ∈ lspan (GQ G) := fun j l => by
    have h := Ideal.mul_mem_left (lspan (GQ G)) (D₁ : MvPolynomial (Fin (m + n)) ℚ)
      (hD (eQ G j) l)
    convert h using 1
    simp only [ZD, Matrix.mul_apply, Matrix.zero_apply, sub_zero, map_sum, map_mul, hjG, hVZ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hZX : ∀ l l', toQ (ZX l l') ∈ lspan (GQ G) := fun l l' => by
    have h := Ideal.mul_mem_left (lspan (GQ G)) (D₁ : MvPolynomial (Fin (m + n)) ℚ) (hX l l')
    convert h using 1
    by_cases hll : l = l'
    · subst hll
      simp [ZX, Matrix.mul_apply, map_sum, hjX, hVZ, hcZ, Finset.mul_sum, mul_sub]
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp [ZX, Matrix.mul_apply, map_sum, hjX, hVZ, hcZ, Finset.mul_sum, Matrix.one_apply, hll]
      exact Finset.sum_congr rfl fun k _ => by ring
  -- 3. integer multiples in the integer ideal
  obtain ⟨D₂, hD₂, hmem⟩ := exists_int_mem_fin G
    (fun i : (Fin (m + n) × Fin (m + n)) ⊕ (Fin r × Fin n) ⊕ (Fin n × Fin n) =>
      Sum.elim (fun kk => ZL kk.1 kk.2) (Sum.elim (fun jl => ZD jl.1 jl.2) fun ll => ZX ll.1 ll.2) i)
    (fun i => by
      rcases i with kk | jl | ll
      · exact hZL kk.1 kk.2
      · exact hZD jl.1 jl.2
      · exact hZX ll.1 ll.2)
  refine ⟨{
    x := y
    B := (D₂ : MvPolynomial (Fin (m + n)) ℤ) • BZ
    V := (D₂ : MvPolynomial (Fin (m + n)) ℤ) • VZ
    c := (D₂ : MvPolynomial (Fin (m + n)) ℤ) * cZ
    hL := fun k k' => by
      have := hmem (Sum.inl (k, k'))
      simp only [Sum.elim_inl] at this
      convert this using 1
      simp only [ZL, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_mul,
        smul_eq_mul]
      ring
    hD := fun j l => by
      have := hmem (Sum.inr (Sum.inl (j, l)))
      simp only [Sum.elim_inl, Sum.elim_inr] at this
      convert this using 1
      simp only [ZD, Matrix.mul_smul, Matrix.smul_apply, Matrix.zero_apply, sub_zero, smul_eq_mul]
    hX := fun l l' => by
      have := hmem (Sum.inr (Sum.inr (l, l')))
      simp only [Sum.elim_inr] at this
      convert this using 1
      simp only [ZX, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_smul, smul_eq_mul]
      ring }, D₁ * D₂, lam, rfl, Nat.mul_pos hD₁ hD₂, hlam, ?_⟩
  show toS (GQ G) (toQ ((D₂ : MvPolynomial (Fin (m + n)) ℤ) * cZ)) = _
  rw [map_mul, map_natCast, hcZ, ← toSHom_apply, map_mul, map_mul, map_natCast, map_natCast,
    toSHom_apply, hc]
  push_cast; ring

end BezoutCounterexample.Principalization
