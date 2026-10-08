import Mathlib
import BezoutCounterexample.Principalization.ChainLiftBridgeTorsor
import BezoutCounterexample.Constructive.ChainLiftTower
import BezoutCounterexample.Principalization.MaxLocusPt

/-!
# The tower of HM's steps lifts chains (bridge, step (2))

* `chart_card_le`, `LocData.n_le`: a chart on a localization of `ℚ[Y₁ … Y_N] ⧸ (G)` has at most
  `N` functions (the chain rule gives `U · V⁰ = 1` with `V⁰` of size `N × n`).
* `torsor_stage`: one torsor stage, for a presentation `G` with any number `N` of variables:
  the torsor presentation `G'` (with `N + M` variables) presents HM's torsor
  (`torsor_presentation`), and chain lifting holds along the projection `(Y, …) ↦ Y`. The
  presentation of stage `i + 1` is the `G'` of stage `i`.
* The divisorial stage of HM (`principalization_star`, `k = 1`) leaves the ring unchanged
  (`AlgHom.id`), so it is `ChainLift.id`, and the tower is `TowerLift` (`TowerLift.proj` for a
  torsor stage, nothing to append for a divisorial stage).

Inputs per torsor stage: a `ChartCoverPt` of the component (`LocusComp.exists_chartCoverPt`:
local data at explicit points, from explicit generators of `𝔭` and Nullstellensatz points), `Algebra.Smooth ℚ` of the current ring
(`torsor_smooth` for the next one), `v₀ 1 ≠ 0` and `π ∈ F₁`, `π ≠ 0`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open scoped Matrix

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/-- **Charts are no larger than presentations.** -/
theorem chart_card_le {N n : ℕ} (G₀ : List (MvPolynomial (Fin N) ℚ))
    {S : Type*} [CommRing S] [Nontrivial S] [Algebra ℚ S] [Algebra (Quo G₀) S]
    [IsScalarTower ℚ (Quo G₀) S]
    (hloc : ∀ x : S, ∃ p q : MvPolynomial (Fin N) ℚ, ∃ u : S,
      u * toS G₀ q = 1 ∧ x * toS G₀ q = toS G₀ p) (c : Chart S n) : n ≤ N := by
  obtain ⟨p, hp⟩ := Constructive.fin_choice fun j => hloc (c.x j)
  obtain ⟨q, hq⟩ := Constructive.fin_choice hp
  obtain ⟨u, hux⟩ := Constructive.fin_choice hq
  have hu := fun j => (hux j).1
  have hx := fun j => (hux j).2
  set U : Matrix (Fin n) (Fin N) S := Matrix.of fun j k =>
    u j * (toS G₀ (pderiv k (p j)) - c.x j * toS G₀ (pderiv k (q j)))
  set V : Matrix (Fin N) (Fin n) S := Matrix.of fun k l => c.d l (toS G₀ (X k))
  have hUV : U * V = 1 := by
    ext j l
    have h1 := derivation_toS G₀ (c.d l) (p j)
    have h2 := derivation_toS G₀ (c.d l) (q j)
    have h3 : c.d l (toS G₀ (p j)) = c.x j * c.d l (toS G₀ (q j)) +
        toS G₀ (q j) * c.d l (c.x j) := by
      rw [← hx j, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp only [U, V, Matrix.mul_apply, Matrix.of_apply]
    have : ∑ k, u j * (toS G₀ (pderiv k (p j)) - c.x j * toS G₀ (pderiv k (q j))) *
        c.d l (toS G₀ (X k)) = u j * (c.d l (toS G₀ (p j)) - c.x j * c.d l (toS G₀ (q j))) := by
      rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, h3]
    have : u j * (c.x j * c.d l (toS G₀ (q j)) + toS G₀ (q j) * c.d l (c.x j) -
        c.x j * c.d l (toS G₀ (q j))) = (u j * toS G₀ (q j)) * c.d l (c.x j) := by ring
    rw [this, hu, one_mul, c.d_x, Matrix.one_apply]
    by_cases h : l = j
    · simp [h]
    · simp [h, Ne.symm h]
  refine le_of_fin_injective S V.mulVecLin fun v w hvw => ?_
  have := congrArg U.mulVec hvw
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hUV, Matrix.one_mulVec] at this
  exact this

section Stage

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- **The chart dimension is at most the number of variables of a presentation.** -/
theorem LocData.n_le {N : ℕ} (G₀ : List (MvPolynomial (Fin N) ℚ)) (e : Quo G₀ ≃+* A)
    {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) : D.n ≤ N := by
  set S := Localization.AtPrime 𝔪
  let alg : Algebra (Quo G₀) S := ((algebraMap A S).comp e.toRingHom).toAlgebra
  have : IsScalarTower ℚ (Quo G₀) S := IsScalarTower.of_algebraMap_eq fun q => by
    have := RingHom.ext_rat (algebraMap ℚ S) ((algebraMap (Quo G₀) S).comp (algebraMap ℚ (Quo G₀)))
    exact congrArg (fun f : ℚ →+* S => f q) this
  have htoS : ∀ p, toS (S := S) G₀ p = algebraMap A S (e (Ideal.Quotient.mk _ p)) := fun p => rfl
  have hpre : ∀ a : A, ∃ p, e (Ideal.Quotient.mk (lspan G₀) p) = a := fun a => by
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (e.symm a)
    exact ⟨p, by rw [hp, RingEquiv.apply_symm_apply]⟩
  refine chart_card_le G₀ (fun x => ?_) (Loc.transport (D.ctrl 𝔪 D.hg) D.ck)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj 𝔪.primeCompl x
  obtain ⟨p, hp⟩ := hpre a
  obtain ⟨q, hq⟩ := hpre b
  obtain ⟨w, hw⟩ := IsLocalization.map_units S b
  refine ⟨p, q, ↑w⁻¹, ?_, ?_⟩
  · rw [htoS, hq, ← hw, Units.inv_mul]
  · rw [htoS, htoS, hp, hq]; exact hab

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hd hw in
/-- **One torsor stage of the tower.** For a presentation `A ≅ ℚ[Y₁ … Y_N] ⧸ (G)`, a chart
cover of the component, `v₀ 1 ≠ 0` and `0 ≠ π ∈ F₁`: a presentation `G'` with `N + M` variables
of HM's torsor `U`, and chain lifting from `G` to `G'` along `(Y, …) ↦ Y`. -/
theorem torsor_stage [Constructive.Enum A] [Fact (Constructive.HasPres A)] {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1) (hπ0 : π ≠ 0)
    {N : ℕ} (G : List (MvPolynomial (Fin N) ℤ)) (e : Quo (G.map toQ) ≃+* A)
    (C : ChartCoverPt I v₀ 𝔭) (hv1 : v₀ 1 ≠ 0) :
    ∃ (M : ℕ) (G' : List (MvPolynomial (Fin (N + M)) ℤ))
      (e' : Quo (G'.map toQ) ≃+* Torsor hI hmax h𝔭 d hπ),
      (∀ k, e' (Ideal.Quotient.mk _ (X (Fin.castAdd M k))) =
        algebraMap A (Torsor hI hmax h𝔭 d hπ) (e (Ideal.Quotient.mk _ (X k)))) ∧
      ChainLift (PtG G) (PtG G') (fun x k => x (Fin.castAdd M k)) := by
  obtain ⟨k₀⟩ : Nonempty (Fin C.n) := by
    rcases Nat.eq_zero_or_pos C.n with h0 | h0
    · exfalso
      have h1 := C.one
      have : C.i = 1 := by
        rw [← h1, Finset.sum_eq_zero (fun k _ => absurd k.2 (by omega)), add_zero]
      exact h𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (this ▸ C.hi))
    · exact ⟨⟨0, h0⟩⟩
  have hnN := LocData.n_le (G.map toQ) e (C.D k₀)
  obtain ⟨m, rfl⟩ : ∃ m, N = m + (C.D k₀).n := ⟨N - (C.D k₀).n, by omega⟩
  obtain ⟨gZ, Dg, G', O, hgZ, hPt, hPt', -, hOd, hpres, hOπ, hCL⟩ :=
    chainLift_torsor_step hI hmax h𝔭 d hd hw hπ G e C ⟨k₀, rfl⟩ hv1
      (by haveI : Algebra.FormallySmooth ℚ (Quo (GQ G)) :=
            Algebra.FormallySmooth.of_equiv e.symm.toRatAlgEquiv
          exact exists_conormalInj_nat G)
  refine ⟨_, G', torsorEquiv hI hmax h𝔭 d hπ G e gZ Dg hd hw hπ0 (fun i => (hgZ i).2)
    (fun i => (hgZ i).1) G' (fun h => by rw [← hpres, hOd]),
    torsorEquiv_X hI hmax h𝔭 d hπ G e gZ Dg hd hw hπ0 _ _ G' _, ?_⟩
  rw [hPt, hPt', hOπ] at hCL
  exact hCL

include hd hw in
/-- **Extending a tower by a torsor stage**: a tower ending at the presentation `G` of `A`
extends to the torsor presentation `G'`, which presents `U` and is the `G` of the next stage. -/
theorem tower_torsor_stage [Constructive.Enum A] [Fact (Constructive.HasPres A)] {N₀ : ℕ} {Pt₀ : (Fin N₀ → ℝ) → Prop} {π : A}
    (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1) (hπ0 : π ≠ 0)
    {N : ℕ} {G : List (MvPolynomial (Fin N) ℤ)} {ρ : (Fin N → ℝ) → (Fin N₀ → ℝ)}
    (T : TowerLift Pt₀ (PtG G) ρ) (e : Quo (G.map toQ) ≃+* A)
    (C : ChartCoverPt I v₀ 𝔭) (hv1 : v₀ 1 ≠ 0) :
    ∃ (M : ℕ) (G' : List (MvPolynomial (Fin (N + M)) ℤ))
      (e' : Quo (G'.map toQ) ≃+* Torsor hI hmax h𝔭 d hπ),
      (∀ k, e' (Ideal.Quotient.mk _ (X (Fin.castAdd M k))) =
        algebraMap A (Torsor hI hmax h𝔭 d hπ) (e (Ideal.Quotient.mk _ (X k)))) ∧
      TowerLift Pt₀ (PtG G') (ρ ∘ fun x k => x (Fin.castAdd M k)) := by
  obtain ⟨M, G', e', he', hCL⟩ := torsor_stage hI hmax h𝔭 hd hw hπ hπ0 G e C hv1
  exact ⟨M, G', e', he', T.proj hCL⟩

end Stage

end BezoutCounterexample.Principalization

