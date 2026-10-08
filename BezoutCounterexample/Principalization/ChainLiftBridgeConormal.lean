import Mathlib
import BezoutCounterexample.Constructive.ChainLiftConormal
import BezoutCounterexample.Principalization.ChainLiftBridgePres
import BezoutCounterexample.Principalization.ChainLiftBridgeChart
import BezoutCounterexample.Constructive.ChainLiftChoice
import BezoutCounterexample.Constructive.ChainLiftConormalCert

/-!
# Conormal retraction data from smoothness (bridge (c))

The one classical input of the minor cover. For `A₀ = ℚ[Y] ⧸ (G₀)` formally smooth over `ℚ`, the
conormal sequence `I/I² → A₀ ⊗ Ω_{ℚ[Y]}` is split injective (`Algebra.FormallySmooth.
iff_split_injection`). Lifting the images `l(1 ⊗ dY_k)` of a retraction gives `a_k ∈ I` with
`gⱼ ≡ Σ_k ∂_k gⱼ · a_k` modulo `I²` (`exists_retQ`). Clearing denominators gives
`Constructive.ConormalRet G D a` over `ℤ` (`exists_conormalRet`), hence `ConormalInj G D`
(`exists_conormalInj_nat`). The constructive route: from a smoothness certificate
(`exists_conormalInj_of_cert`, via `SmoothCert.conormalInj`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive TensorProduct

variable {N m n : ℕ}

/-- `dp = Σ_k ∂_k p · dY_k` in `Ω_{ℚ[Y]}`. -/
lemma kD_poly (p : MvPolynomial (Fin N) ℚ) :
    KaehlerDifferential.D ℚ (MvPolynomial (Fin N) ℚ) p =
      ∑ k, pderiv k p • KaehlerDifferential.D ℚ (MvPolynomial (Fin N) ℚ) (X k) := by
  have : KaehlerDifferential.D ℚ (MvPolynomial (Fin N) ℚ) = ∑ k,
      (LinearMap.toSpanSingleton (MvPolynomial (Fin N) ℚ) _
        (KaehlerDifferential.D ℚ (MvPolynomial (Fin N) ℚ) (X k))).compDer
        (pderiv k : Derivation ℚ (MvPolynomial (Fin N) ℚ) (MvPolynomial (Fin N) ℚ)) := by
    refine MvPolynomial.derivation_ext fun i => ?_
    rw [Derivation.sum_apply'']
    change _ = ∑ k, pderiv k (X i : MvPolynomial (Fin N) ℚ) •
      KaehlerDifferential.D ℚ (MvPolynomial (Fin N) ℚ) (X k)
    simp only [pderiv_X, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  conv_lhs => rw [this]
  rw [Derivation.sum_apply'']
  rfl

/-- **Retraction data over `ℚ` from formal smoothness.** -/
theorem exists_retQ (G₀ : List (MvPolynomial (Fin N) ℚ))
    [Algebra.FormallySmooth ℚ (Quo G₀)] :
    ∃ a : Fin N → MvPolynomial (Fin N) ℚ, (∀ k, a k ∈ lspan G₀) ∧
      ∀ j : Fin G₀.length, G₀.get j - ∑ k, pderiv k (G₀.get j) * a k ∈ lspan G₀ ^ 2 := by
  have hf : Function.Surjective (algebraMap (MvPolynomial (Fin N) ℚ) (Quo G₀)) := Ideal.Quotient.mk_surjective
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := ℚ) hf).1 inferInstance
  have hker : RingHom.ker (algebraMap (MvPolynomial (Fin N) ℚ) (Quo G₀)) = lspan G₀ := Ideal.mk_ker
  obtain ⟨ak, hak⟩ := finite_choice_dep fun k : Fin N => Ideal.toCotangent_surjective _
    (l (1 ⊗ₜ KaehlerDifferential.D ℚ (MvPolynomial (Fin N) ℚ) (X k)))
  have hle : RingHom.ker (algebraMap (MvPolynomial (Fin N) ℚ) (Quo G₀)) ≤ lspan G₀ := hker.le
  have hle2 : RingHom.ker (algebraMap (MvPolynomial (Fin N) ℚ) (Quo G₀)) ^ 2 ≤ lspan G₀ ^ 2 := by
    rw [pow_two, pow_two]; exact Ideal.mul_mono hle hle
  refine ⟨fun k => (ak k : MvPolynomial (Fin N) ℚ), fun k => hle (ak k).2, fun j => ?_⟩
  have hGj : G₀.get j ∈ RingHom.ker (algebraMap (MvPolynomial (Fin N) ℚ) (Quo G₀)) := by
    rw [hker]; exact get_mem_lspan G₀ j
  set x : RingHom.ker (algebraMap (MvPolynomial (Fin N) ℚ) (Quo G₀)) := ⟨G₀.get j, hGj⟩
  have h1 := LinearMap.congr_fun hl (Ideal.toCotangent _ x)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
    KaehlerDifferential.kerCotangentToTensor_toCotangent] at h1
  rw [kD_poly, tmul_sum] at h1
  simp only [tmul_smul, map_sum, map_smul, ← hak] at h1
  have h2 : Ideal.toCotangent _ (x - ∑ k, pderiv k (G₀.get j) • ak k) = 0 := by
    rw [map_sub, map_sum, ← h1]
    simp only [map_smul]
    exact sub_self _
  rw [Ideal.toCotangent_eq_zero] at h2
  have h3 : ((x - ∑ k, pderiv k (G₀.get j) • ak k :
      RingHom.ker (algebraMap (MvPolynomial (Fin N) ℚ) (Quo G₀))) : MvPolynomial (Fin N) ℚ) =
      G₀.get j - ∑ k, pderiv k (G₀.get j) * (ak k : MvPolynomial (Fin N) ℚ) := by
    simp [x, smul_eq_mul]
  rw [h3] at h2
  exact hle2 h2

/-- The products of pairs of members of a list. -/
def sqList {R : Type*} [CommRing R] (L : List R) : List R := L.flatMap fun g => L.map (g * ·)

lemma lspan_sqList {R : Type*} [CommRing R] (L : List R) : lspan (sqList L) = lspan L ^ 2 := by
  rw [pow_two]
  show Ideal.span _ = Ideal.span _ * Ideal.span _
  rw [Ideal.span_mul_span']
  congr 1
  ext x
  simp only [sqList, List.mem_flatMap, List.mem_map, Set.mem_setOf_eq, Set.mem_mul]


lemma sqList_map {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') (L : List R) :
    (sqList L).map f = sqList (L.map f) := by
  simp [sqList, List.map_flatMap, List.flatMap_map, Function.comp_def]

/-- **Conormal retraction data over `ℤ`** for an integer presentation of a formally smooth
`ℚ`-algebra. -/
theorem exists_conormalRet (G : List (MvPolynomial (Fin N) ℤ))
    [Algebra.FormallySmooth ℚ (Quo (G.map toQ))] :
    ∃ (D : ℕ) (a : Fin N → MvPolynomial (Fin N) ℤ), 0 < D ∧
      ConormalRet G (D : MvPolynomial (Fin N) ℤ) a := by
  obtain ⟨aQ, haQ, hret⟩ := exists_retQ (G.map toQ)
  obtain ⟨D₁, aZ, hD₁, haZ⟩ := exists_int_mul_fin aQ
  -- `aZ ∈ (G)` up to an integer
  obtain ⟨D₂, hD₂, hD₂a⟩ := exists_int_mem_fin G aZ fun k => by
    rw [haZ k]; exact Ideal.mul_mem_left _ _ (haQ k)
  -- the relations, modulo `(G)²` up to an integer
  set Z : Fin G.length → MvPolynomial (Fin N) ℤ := fun j =>
    ((D₁ * D₂ : ℕ) : MvPolynomial (Fin N) ℤ) * G.get j -
      ∑ k, pderiv k (G.get j) * ((D₂ : MvPolynomial (Fin N) ℤ) * aZ k)
  obtain ⟨D₃, hD₃, hD₃Z⟩ := exists_int_mem_fin (sqList G) Z fun j => by
    rw [sqList_map, lspan_sqList]
    have hj := hret (finCongr (List.length_map _).symm j)
    have hget : (G.map toQ).get (finCongr (List.length_map _).symm j) = toQ (G.get j) := by simp
    rw [hget] at hj
    have := Ideal.mul_mem_left (lspan (G.map toQ) ^ 2)
      ((D₁ * D₂ : ℕ) : MvPolynomial (Fin N) ℚ) hj
    convert this using 1
    simp only [Z, map_sub, map_mul, map_natCast, map_sum, pderiv_map, haZ, mul_sub,
      Finset.mul_sum]
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  refine ⟨D₃ * (D₁ * D₂), fun k => ((D₃ * D₂ : ℕ) : MvPolynomial (Fin N) ℤ) * aZ k,
    Nat.mul_pos hD₃ (Nat.mul_pos hD₁ hD₂), fun k => ?_, fun j => ?_⟩
  · show ((D₃ * D₂ : ℕ) : MvPolynomial (Fin N) ℤ) * aZ k ∈ lspan G
    rw [Nat.cast_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ (hD₂a k)
  · have := hD₃Z j
    rw [lspan_sqList] at this
    convert this using 1
    simp only [Z, Nat.cast_mul, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring

/-- **Conormal injectivity, smoothness route** (the classical input). -/
theorem exists_conormalInj_nat (G : List (MvPolynomial (Fin (m + n)) ℤ))
    [Algebra.FormallySmooth ℚ (Quo (G.map toQ))] :
    ∃ Dc : ℕ, 0 < Dc ∧ ConormalInj G (Dc : MvPolynomial (Fin (m + n)) ℤ) := by
  obtain ⟨Dc, ac, hDc, hret⟩ := exists_conormalRet G
  exact ⟨Dc, hDc, conormalInj_of_ret hret⟩

/-- **Conormal injectivity, certificate route** (constructive): a power of the cover constant. -/
theorem exists_conormalInj_of_cert {G : List (MvPolynomial (Fin (m + n)) ℤ)}
    (hG : SmoothCert m n G) :
    ∃ Dc : ℕ, 0 < Dc ∧ ConormalInj G (Dc : MvPolynomial (Fin (m + n)) ℤ) := by
  obtain ⟨M, hM⟩ := hG.conormalInj
  exact ⟨hG.C ^ M, pow_pos hG.hC M, hM⟩

end BezoutCounterexample.Principalization
