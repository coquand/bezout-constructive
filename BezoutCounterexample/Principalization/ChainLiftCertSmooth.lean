import Mathlib
import BezoutCounterexample.Constructive.ChainLiftCertRet
import BezoutCounterexample.Constructive.ChainLiftOffPres
import BezoutCounterexample.Constructive.MinPrime

/-!
# Smoothness from a certificate (Task B, Rees layer S0)

`smooth_of_conormalRet`: retraction data `ConormalRet G D a` with a positive integer `D` make
`ℚ[Y]/(G)` smooth over `ℚ`. Over `ℚ`, `a'_k = D⁻¹ a_k` lifts a retraction of the conormal sequence
(`y ≡ Σ_k ∂_k y · a'_k` modulo `(G)²` for every `y ∈ (G)`, `retQ_of_ret`), so the sequence splits
(`Algebra.FormallySmooth.iff_split_injection`, a whitelisted K fact); finite presentation is
immediate. With `SmoothCert.exists_conormalRet` this gives `SmoothCert.smooth`: a certificate makes
the presented ring smooth, with no quantification over primes (it replaces the local–global and
spreading-out primitives of `ChainLiftSmoothK` on the Rees path).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive TensorProduct

variable {N : ℕ}

/-- **The retraction over `ℚ`**: `y ≡ Σ_k ∂_k y · D⁻¹ a_k` modulo `(G)²` for every `y ∈ (G)`. -/
lemma retQ_of_ret (G : List (MvPolynomial (Fin N) ℤ)) {D : ℕ} (hD : 0 < D)
    {a : Fin N → MvPolynomial (Fin N) ℤ} (h : ConormalRet G (D : MvPolynomial (Fin N) ℤ) a) :
    ∀ y ∈ lspan (G.map toQZ),
      y - ∑ k, pderiv k y * (C ((D : ℚ)⁻¹) * toQZ (a k)) ∈ lspan (G.map toQZ) ^ 2 := by
  set I := lspan (G.map toQZ)
  have hmap : ∀ x ∈ lspan G, toQZ x ∈ I := fun x hx => by
    rw [show I = (lspan G).map toQZ from lspan_map _ _]; exact Ideal.mem_map_of_mem _ hx
  have hmap2 : ∀ x ∈ lspan G ^ 2, toQZ x ∈ I ^ 2 := fun x hx => by
    rw [show I = (lspan G).map toQZ from lspan_map _ _, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  have ha' : ∀ k, C ((D : ℚ)⁻¹) * toQZ (a k) ∈ I := fun k =>
    Ideal.mul_mem_left _ _ (hmap _ (h.1 k))
  have hsq : ∀ x ∈ I, ∀ z ∈ I, x * z ∈ I ^ 2 := fun x hx z hz => by
    rw [pow_two]; exact Ideal.mul_mem_mul hx hz
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, rfl⟩ := List.get_of_mem hg
    have h2 := hmap2 _ (h.2 j)
    simp only [map_sub, map_mul, map_natCast, map_sum] at h2
    have h3 := Ideal.mul_mem_left (I ^ 2) (C ((D : ℚ)⁻¹)) h2
    convert h3 using 1
    simp only [pderiv_map, mul_sub, Finset.mul_sum]
    congr 1
    · rw [← mul_assoc, ← C_eq_coe_nat, ← C_mul, inv_mul_cancel₀ hDq, C_1, one_mul]
    · exact Finset.sum_congr rfl fun k _ => by rw [toQZ]; ring
  | zero => simp
  | add x z _ _ hx hz =>
    have : x + z - ∑ k, pderiv k (x + z) * (C ((D : ℚ)⁻¹) * toQZ (a k)) =
        (x - ∑ k, pderiv k x * (C ((D : ℚ)⁻¹) * toQZ (a k))) +
          (z - ∑ k, pderiv k z * (C ((D : ℚ)⁻¹) * toQZ (a k))) := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]; ring
    rw [this]; exact Ideal.add_mem _ hx hz
  | smul c x hxI hx =>
    have hd : ∀ k, pderiv k (c * x) * (C ((D : ℚ)⁻¹) * toQZ (a k)) =
        c * (pderiv k x * (C ((D : ℚ)⁻¹) * toQZ (a k))) +
          x * (pderiv k c * (C ((D : ℚ)⁻¹) * toQZ (a k))) := fun k => by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    have : c • x - ∑ k, pderiv k (c • x) * (C ((D : ℚ)⁻¹) * toQZ (a k)) =
        c * (x - ∑ k, pderiv k x * (C ((D : ℚ)⁻¹) * toQZ (a k))) -
          ∑ k, x * (pderiv k c * (C ((D : ℚ)⁻¹) * toQZ (a k))) := by
      rw [smul_eq_mul, Finset.sum_congr rfl (fun k _ => hd k), Finset.sum_add_distrib,
        ← Finset.mul_sum, mul_sub]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hx)
      (Ideal.sum_mem _ fun k _ => hsq _ hxI _ (Ideal.mul_mem_left _ _ (ha' k)))

/-- **Formal smoothness from retraction data** with a positive integer multiplier. -/
theorem formallySmooth_of_conormalRet (G : List (MvPolynomial (Fin N) ℤ)) {D : ℕ} (hD : 0 < D)
    {a : Fin N → MvPolynomial (Fin N) ℤ} (h : ConormalRet G (D : MvPolynomial (Fin N) ℤ) a) :
    Algebra.FormallySmooth ℚ (MvPolynomial (Fin N) ℚ ⧸ lspan (G.map toQZ)) := by
  set P := MvPolynomial (Fin N) ℚ
  set Q := P ⧸ lspan (G.map toQZ)
  have hsmul : ∀ (p : P) (u : Q), p • u = algebraMap P Q p * u := fun p u => Algebra.smul_def p u
  rw [Algebra.FormallySmooth.iff_split_injection (P := P) Ideal.Quotient.mk_surjective]
  set K' := RingHom.ker (algebraMap P Q)
  have hK : K' = lspan (G.map toQZ) := Ideal.mk_ker
  let eK : Q ≃+* P ⧸ K' := Ideal.quotEquivOfEq hK.symm
  have heK : ∀ p : P, eK (algebraMap P Q p) = Ideal.Quotient.mk K' p :=
    fun p => Ideal.quotEquivOfEq_mk hK.symm p
  set a' : Fin N → P := fun k => C ((D : ℚ)⁻¹) * toQZ (a k)
  have ha'K : ∀ k, a' k ∈ K' := fun k => by
    rw [hK, show lspan (G.map toQZ) = (lspan G).map toQZ from lspan_map _ _]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h.1 k))
  let rC : Fin N → K'.Cotangent := fun k => K'.toCotangent ⟨a' k, ha'K k⟩
  let Dk : Fin N → Derivation ℚ P Q := fun k => (Algebra.linearMap P Q).compDer (pderiv k)
  let l₀ : Ω[P⁄ℚ] →ₗ[P] K'.Cotangent :=
    { toFun := fun ω => ∑ k, eK ((Dk k).liftKaehlerDifferential ω) • rC k
      map_add' := fun ω ω' => by
        simp only [map_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun p ω => by
        simp only [map_smul, RingHom.id_apply, Finset.smul_sum, hsmul, map_mul, heK, mul_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul] }
  let lB : Q →ₗ[P] Ω[P⁄ℚ] →ₗ[P] K'.Cotangent :=
    LinearMap.mk₂ P (fun u ω => eK u • l₀ ω)
      (fun u u' ω => by simp only [map_add, add_smul])
      (fun p u ω => by
        rw [hsmul, map_mul, heK, mul_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul])
      (fun u ω ω' => by simp only [map_add, smul_add])
      (fun p u ω => by rw [map_smul, smul_comm])
  refine ⟨TensorProduct.lift lB, ?_⟩
  apply LinearMap.ext
  intro t
  obtain ⟨y, rfl⟩ := K'.toCotangent_surjective t
  rw [LinearMap.comp_apply, KaehlerDifferential.kerCotangentToTensor_toCotangent,
    TensorProduct.lift.tmul, LinearMap.id_apply]
  show eK 1 • l₀ (KaehlerDifferential.D ℚ P y) = _
  rw [map_one, one_smul]
  show ∑ k, eK ((Dk k).liftKaehlerDifferential (KaehlerDifferential.D ℚ P y)) • rC k = _
  simp only [Derivation.liftKaehlerDifferential_comp_D]
  obtain ⟨y, hy⟩ := y
  have hy' : y ∈ lspan (G.map toQZ) := by rw [← hK]; exact hy
  have hsum : ∑ k, pderiv k y * a' k ∈ K' :=
    Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (ha'K k)
  have hret : K'.toCotangent ⟨y, hy⟩ = K'.toCotangent ⟨_, hsum⟩ := by
    rw [Ideal.toCotangent_eq]
    show y - ∑ k, pderiv k y * a' k ∈ K' ^ 2
    rw [hK]; exact retQ_of_ret G hD h y hy'
  rw [hret]
  have : (⟨∑ k, pderiv k y * a' k, hsum⟩ : K') = ∑ k, pderiv k y • (⟨a' k, ha'K k⟩ : K') := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul]
  rw [this, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  show eK (algebraMap P Q (pderiv k y)) • rC k = _
  rw [heK]
  rfl

/-- **Smoothness from retraction data** with a positive integer multiplier. -/
theorem smooth_of_conormalRet (G : List (MvPolynomial (Fin N) ℤ)) {D : ℕ} (hD : 0 < D)
    {a : Fin N → MvPolynomial (Fin N) ℤ} (h : ConormalRet G (D : MvPolynomial (Fin N) ℤ) a) :
    Algebra.Smooth ℚ (MvPolynomial (Fin N) ℚ ⧸ lspan (G.map toQZ)) := by
  haveI := formallySmooth_of_conormalRet G hD h
  haveI : Algebra.FinitePresentation ℚ (MvPolynomial (Fin N) ℚ ⧸ lspan (G.map toQZ)) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (G.map toQZ).finite_toSet)
  exact Algebra.Smooth.mk inferInstance inferInstance

/-- **A certificate makes the presented ring smooth.** -/
theorem _root_.BezoutCounterexample.Constructive.SmoothCert.smooth {m n : ℕ}
    {G : List (MvPolynomial (Fin (m + n)) ℤ)} (hG : SmoothCert m n G) :
    Algebra.Smooth ℚ (SmoothCert.QB G) := by
  obtain ⟨M, a, ha⟩ := hG.exists_conormalRet
  exact smooth_of_conormalRet G (pow_pos hG.hC M) ha

end BezoutCounterexample.Principalization
