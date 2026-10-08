import Mathlib
import BezoutCounterexample.Principalization.ChainLiftBridgeChartZ
import BezoutCounterexample.Principalization.ChainLiftBridgePart
import BezoutCounterexample.Principalization.ChainLiftBridgeHead
import BezoutCounterexample.Constructive.ChainLiftChoice

/-!
# The chain-lifting bridge: one chart of the cover (bridge (b)+(d))

For a chart `D` (`LocData`) of HM's ring `A ≅ ℚ[Y] ⧸ (G)` (`e`), with `n` chart functions and `kc`
head functions: the integer chart data of the `τ`-coordinates `(Dq · a_head, Y_τ)` and the
`A`-level partition `g^M = Σ_τ β_τ c_τ + Σ_q ω_q a_q` (`chart_partition`), where `c_τ` are the
chart multipliers and `a_q` the head numerators.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive IsLocalization
open scoped Matrix

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal]

/-- The integer coordinates of the `τ`-chart: head polynomials, then the variables `Y_τ`. -/
def yZ {m n kc : ℕ} (hk : kc ≤ n) (ã : Fin kc → MvPolynomial (Fin (m + n)) ℤ)
    (τ : RowIdx (m + n) (n - kc)) (j : Fin n) : MvPolynomial (Fin (m + n)) ℤ :=
  if h : (j : ℕ) < kc then ã ⟨j, h⟩ else X (τ.enum ⟨j - kc, by omega⟩)

/-- **One chart: integer chart data of the `τ`-coordinates and the partition in `A`.** -/
theorem chart_partition {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ))
    (e : Quo (GQ G) ≃+* A) (D : LocData I v₀ 𝔪) (hD : D.n = n) {kc : ℕ} (hk : kc ≤ n)
    (hn : 0 < n) :
    ∃ (s : ℕ) (a : Fin n → A) (ã : Fin kc → MvPolynomial (Fin (m + n)) ℤ) (Dq : Fin kc → ℕ)
      (T : RowIdx (m + n) (n - kc) → ChartData G) (M : ℕ) (β : RowIdx (m + n) (n - kc) → A)
      (ω : Fin kc → A),
      (∀ q, 0 < Dq q ∧ e (Ideal.Quotient.mk _ (toQ (ã q))) = (Dq q : A) * a (headIdx hk q)) ∧
      (∀ τ, (T τ).x = yZ hk ã τ) ∧
      (∀ j : Fin D.n, D.cB.x j * algebraMap A D.B D.g ^ s =
        algebraMap A D.B (a (Fin.cast hD j))) ∧
      D.g ^ M = ∑ τ, β τ * e (Ideal.Quotient.mk _ (toQ (T τ).c)) + ∑ q, ω q * a (headIdx hk q) := by
  subst hD
  -- the chart ring as an algebra over the presented ring
  letI alg : Algebra (Quo (GQ G)) D.B := ((algebraMap A D.B).comp e.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ (Quo (GQ G)) D.B := IsScalarTower.of_algebraMap_eq fun q => by
    have := RingHom.ext_rat (algebraMap ℚ D.B)
      ((algebraMap (Quo (GQ G)) D.B).comp (algebraMap ℚ (Quo (GQ G))))
    exact congrArg (fun f : ℚ →+* D.B => f q) this
  set Mo : Submonoid (Quo (GQ G)) := D.N.map e.symm
  haveI : IsLocalization Mo D.B := isLocalization_of_base_ringEquiv D.N D.B e.symm
  have htoS : ∀ p, toS (S := D.B) (GQ G) p = algebraMap A D.B (e (Ideal.Quotient.mk _ p)) :=
    fun p => rfl
  set c := D.cB
  -- numerators and lifts
  obtain ⟨s, a, ha⟩ := exists_numerators D
  have hsurj : ∀ x : A, ∃ p, e (Ideal.Quotient.mk _ p) = x := fun x => by
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨p, rfl⟩
  obtain ⟨pa, hpa⟩ := Constructive.finite_choice_dep fun j => hsurj (a j)
  obtain ⟨pg, hpg⟩ := hsurj D.g
  obtain ⟨D₀, ã, hD₀, hã⟩ := exists_int_mul_fin (σ := Fin (m + D.n)) fun q : Fin kc => pa (headIdx hk q)
  -- the coordinate families
  have hyQ : ∀ τ, (fun j => toQ (yZ hk ã τ j)) = yTau hk pa (fun _ => (D₀ : ℚ)) τ := by
    intro τ; funext j
    by_cases h : (j : ℕ) < kc
    · simp only [yZ, yTau, h, dite_true, hã, ← map_natCast C]
      congr 2
    · simp [yZ, yTau, h]
  obtain ⟨T, hT⟩ := Constructive.finite_choice_dep fun τ => chartData_of_chart G Mo c hn (yZ hk ã τ)
  obtain ⟨DT, hT⟩ := Constructive.finite_choice_dep hT
  obtain ⟨lam, hT⟩ := Constructive.finite_choice_dep hT
  have hTx := fun τ => (hT τ).1
  have hDT := fun τ => (hT τ).2.1
  have hlam := fun τ => (hT τ).2.2.1
  have hTc := fun τ => (hT τ).2.2.2
  -- the partition in the chart ring
  have hgS : toS (S := D.B) (GQ G) pg = algebraMap A D.B D.g := by rw [htoS, hpg]
  obtain ⟨u, hu⟩ : ∃ u : D.B, u * toS (GQ G) pg ^ s = 1 := by
    rw [hgS]
    obtain ⟨v, hv⟩ := ((IsLocalization.Away.algebraMap_isUnit (S := D.B) D.g).pow s).exists_left_inv
    exact ⟨v, hv⟩
  have hp : ∀ j, c.x j * toS (S := D.B) (GQ G) pg ^ s = toS (GQ G) (pa j) := fun j => by
    rw [hgS, htoS, hpa, ← ha j]
  obtain ⟨r, z, hz, hsum⟩ := partition_chart (GQ G) c hk pg s u hu pa hp fun _ => (D₀ : ℚ)
  -- `det J_τ = c_τ / (D_τ λ_τ)`
  set cA : RowIdx (m + D.n) (D.n - kc) → A := fun τ => e (Ideal.Quotient.mk _ (toQ (T τ).c))
  have hunit : ∀ τ, IsUnit ((DT τ : D.B) * toS (GQ G) (lam τ)) := fun τ => by
    refine IsUnit.mul ?_ ?_
    · have : IsUnit ((DT τ : ℚ)) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (hDT τ).ne')
      simpa using this.map (algebraMap ℚ D.B)
    · exact IsLocalization.map_units (M := Mo) D.B ⟨_, hlam τ⟩
  obtain ⟨ν, hν⟩ := Constructive.finite_choice_dep fun τ => (hunit τ).exists_left_inv
  have hdet : ∀ τ, (Jm (GQ G) c (yTau hk pa (fun _ => (D₀ : ℚ)) τ)).det =
      ν τ * algebraMap A D.B (cA τ) := fun τ => by
    rw [← htoS, hTc τ, hyQ τ, ← mul_assoc, hν τ, one_mul]
  -- the head part `z = Σ w_q x_q`
  rw [Ideal.mem_span_range_iff_exists_fun] at hz
  obtain ⟨w, rfl⟩ := hz
  -- clear the denominators in `D.B = A[1/g]`
  obtain ⟨⟨b, hb⟩, hint⟩ := exist_integer_multiples_of_finite (Submonoid.powers D.g)
    (Sum.elim (fun τ => r τ * ν τ) w : RowIdx (m + D.n) (D.n - kc) ⊕ Fin kc → D.B)
  obtain ⟨j₀, rfl⟩ := hb
  obtain ⟨ρ, hρ⟩ := Constructive.finite_choice_dep fun i => (hint i : ∃ a : A, _ = _)
  have hρτ : ∀ τ, algebraMap A D.B (ρ (Sum.inl τ)) = algebraMap A D.B D.g ^ j₀ * (r τ * ν τ) :=
    fun τ => by rw [hρ, Algebra.smul_def, map_pow]; rfl
  have hρq : ∀ q, algebraMap A D.B (ρ (Sum.inr q)) = algebraMap A D.B D.g ^ j₀ * w q :=
    fun q => by rw [hρ, Algebra.smul_def, map_pow]; rfl
  have hB : algebraMap A D.B (∑ τ, D.g ^ s * ρ (Sum.inl τ) * cA τ) = algebraMap A D.B
      ((D₀ : A) ^ kc * D.g ^ (j₀ + s + s * kc) + ∑ q, ρ (Sum.inr q) * a (headIdx hk q)) := by
    have h1 := congrArg (fun y => algebraMap A D.B D.g ^ (j₀ + s) * y) hsum
    rw [map_sum, map_add, map_sum]
    have eL : ∀ τ, algebraMap A D.B (D.g ^ s * ρ (Sum.inl τ) * cA τ) =
        algebraMap A D.B D.g ^ (j₀ + s) * (r τ * (Jm (GQ G) c (yTau hk pa (fun _ => (D₀ : ℚ)) τ)).det) :=
      fun τ => by rw [hdet, map_mul, map_mul, map_pow, hρτ, pow_add]; ring
    have eR : ∀ q, algebraMap A D.B (ρ (Sum.inr q) * a (headIdx hk q)) =
        algebraMap A D.B D.g ^ (j₀ + s) * (w q * c.x (headIdx hk q)) := fun q => by
      rw [map_mul, hρq, ← ha (headIdx hk q), pow_add]; ring
    simp only [eL, eR, ← Finset.mul_sum]
    rw [h1, mul_add]
    congr 1
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul, map_mul,
      map_pow, map_pow, map_natCast, ← map_natCast (algebraMap ℚ D.B), pow_add, pow_add, hgS]
    simp only [map_natCast]
    ring
  obtain ⟨⟨_, t, rfl⟩, ht⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers D.g) D.B).1 hB
  -- divide by `D₀^kc`
  set κ : A := algebraMap ℚ A ((D₀ : ℚ) ^ kc)⁻¹
  have hκ : κ * (D₀ : A) ^ kc = 1 := by
    rw [← map_natCast (algebraMap ℚ A), ← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _
      (Nat.cast_ne_zero.2 hD₀.ne')), map_one]
  refine ⟨s, a, ã, fun _ => D₀, T, t + (j₀ + s + s * kc),
    fun τ => κ * D.g ^ t * (D.g ^ s * ρ (Sum.inl τ)), fun q => -(κ * D.g ^ t * ρ (Sum.inr q)),
    fun q => ⟨hD₀, ?_⟩, hTx, fun j => by simpa using ha j, ?_⟩
  · rw [show e (Ideal.Quotient.mk _ (toQ (ã q))) = e (Ideal.Quotient.mk _ ((D₀ : MvPolynomial _ ℚ) *
      pa (headIdx hk q))) by rw [hã q], map_mul, map_mul, map_natCast, map_natCast, hpa]
  · have ht' : D.g ^ t * ∑ τ, D.g ^ s * ρ (Sum.inl τ) * cA τ = D.g ^ t * ((D₀ : A) ^ kc *
        D.g ^ (j₀ + s + s * kc) + ∑ q, ρ (Sum.inr q) * a (headIdx hk q)) := ht
    have : D.g ^ (t + (j₀ + s + s * kc)) = κ * (D₀ : A) ^ kc * D.g ^ (t + (j₀ + s + s * kc)) := by
      rw [hκ, one_mul]
    rw [this, pow_add]
    have e2 : κ * (D₀ : A) ^ kc * (D.g ^ t * D.g ^ (j₀ + s + s * kc)) =
        κ * (D.g ^ t * ((D₀ : A) ^ kc * D.g ^ (j₀ + s + s * kc) +
          ∑ q, ρ (Sum.inr q) * a (headIdx hk q))) -
        κ * D.g ^ t * ∑ q, ρ (Sum.inr q) * a (headIdx hk q) := by ring
    rw [e2, ← ht']
    simp only [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun τ _ => by simp only [cA]; ring
    · exact Finset.sum_congr rfl fun q _ => by ring

end BezoutCounterexample.Principalization
