import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesL3d
import BezoutCounterexample.Principalization.ChainLiftReesGens
import BezoutCounterexample.Constructive.ChainLiftChoice

/-!
# Integer rows of the weighted-chart model (Task B, Rees layer S6, producer part 2)

The rows of L1/L2 (`exists_heads_poly(_pt)`, `exists_yrow_poly(_pt)`) are rational polynomials and
`A`-valued expansions. Here they are cleared to `ℤ` in the form that `exists_reesChart_of_l3`
consumes (`hP`, `hy`). Denominators are cleared by common multiples, with no `Finset` choice:

* `exists_common_mul`: `kᵢ dᵢ = D` for positive `dᵢ` (`D = ∏ dⱼ`, `kᵢ = D / dᵢ`);
* `prod_pow_ιk`: a product over `Fin n` supported on the first `kc` indices is a product over `Fin kc`;
* `exists_head_rows`: the integer head polynomials `P̃ᵢ`, with `γ = D γ₀`;
* `exists_yrow_int`: one integer `y`-row `Qⱼ`, up to a positive integer.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

/-- **Common multiples** of finitely many positive integers. -/
lemma exists_common_mul {K : ℕ} (d : Fin K → ℕ) (hd : ∀ i, 0 < d i) :
    ∃ (D : ℕ) (k : Fin K → ℕ), 0 < D ∧ ∀ i, k i * d i = D :=
  ⟨∏ j, d j, fun i => (∏ j, d j) / d i, Finset.prod_pos fun j _ => hd j,
    fun i => Nat.div_mul_cancel (Finset.dvd_prod_of_mem d (Finset.mem_univ i))⟩

/-- A product over `Fin n` whose factors are trivial beyond the first `kc` indices. -/
lemma prod_pow_ιk {M : Type*} [CommMonoid M] {kc n : ℕ} (hkn : kc ≤ n) (f : Fin n → M)
    (α : Fin n → ℕ) (hα : ∀ l : Fin n, kc ≤ (l : ℕ) → α l = 0) :
    ∏ l, f l ^ α l = ∏ q : Fin kc, f (ιk hkn q) ^ α (ιk hkn q) := by
  have hm := Finset.prod_map Finset.univ ⟨ιk hkn, ιk_injective hkn⟩ (fun l => f l ^ α l)
  simp only [Function.Embedding.coeFn_mk] at hm
  rw [← hm]
  refine (Finset.prod_subset (Finset.subset_univ _) fun l _ hl => ?_).symm
  have : kc ≤ (l : ℕ) := by
    by_contra h
    exact hl (Finset.mem_map.2 ⟨⟨l, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [hα l this, pow_zero]

set_option linter.unusedSectionVars false

variable {A : Type} [CommRing A] [Algebra ℚ A] {m kc l r : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (γ : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ)

omit [Algebra ℚ A] in
lemma aeval_int_cast {σ : Type*} {R : Type*} [CommRing R] [Algebra ℚ R] (x : σ → R)
    (p : MvPolynomial σ ℤ) : aeval (R := ℚ) x (toQZ p) = aeval x p := by
  rw [toQZ, show (Int.castRingHom ℚ) = algebraMap ℤ ℚ from rfl, aeval_map_algebraMap]

lemma toAZ_natCast (n : ℕ) : toAZ G e (n : MvPolynomial (Fin (m + (kc + l))) ℤ) = (n : A) := by
  simp [toAZ]

lemma toAZ_mul' (p p' : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    toAZ G e (p * p') = toAZ G e p * toAZ G e p' := by
  simp [toAZ]

/-- **Integer head rows**: from rational preimages `Pqᵢ` of `C(g' a'ᵢ) T^{wᵢ}` and an integer
`γ₀ ↦ E g'`, integer `P̃ᵢ ↦ C(D γ₀ x̃ᵢ) T^{wᵢ}` where `x̃ᵢ ↦ Dqᵢ a'ᵢ` are the heads of `F`. -/
theorem exists_head_rows (Ly : Fin r → A[T;T⁻¹]) (g' : A) (a' : Fin kc → A)
    (Pq : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℚ)
    (hPq : ∀ i, aeval (evG G e Ly) (Pq i) = LaurentPolynomial.C (g' * a' i) * T (w i))
    (γ₀ : MvPolynomial (Fin (m + (kc + l))) ℤ) (E : ℕ) (hγ₀ : toAZ G e γ₀ = (E : A) * g')
    (Dq : Fin kc → ℕ) (hF : ∀ i, toAZ G e (F (Fin.natAdd m (Fin.castAdd l i))) = (Dq i : A) * a' i) :
    ∃ (D : ℕ) (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ), 0 < D ∧
      ∀ i, aeval (evG G e Ly) (P i) = LaurentPolynomial.C (toAZ G e
        ((D : MvPolynomial (Fin (m + (kc + l))) ℤ) * γ₀ * F (Fin.natAdd m (Fin.castAdd l i)))) *
          T (w i) := by
  obtain ⟨c, hc⟩ := Constructive.finite_choice_dep (ι := Fin kc)
    (P := fun i (x : ℕ × MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) =>
      0 < x.1 ∧ toQZ x.2 = (x.1 : MvPolynomial _ ℚ) * Pq i)
    fun i => by
      obtain ⟨D, q, hD, hq⟩ := int_clear (Pq i)
      exact ⟨(D, q), hD, hq⟩
  obtain ⟨D, k, hD, hk⟩ := exists_common_mul (fun i => (c i).1) fun i => (hc i).1
  refine ⟨D, fun i => ((k i * E * Dq i : ℕ) : MvPolynomial _ ℤ) * (c i).2, hD, fun i => ?_⟩
  have h1 : aeval (evG G e Ly) (c i).2 = aeval (R := ℚ) (evG G e Ly) (toQZ (c i).2) :=
    (aeval_int_cast _ _).symm
  rw [map_mul, map_natCast]
  erw [h1]
  rw [(hc i).2, map_mul, map_natCast, hPq i,
    toAZ_mul', toAZ_mul', toAZ_natCast, hγ₀, hF i, ← hk i]
  simp only [map_mul, map_natCast, Nat.cast_mul]
  ring

/-- The variables of the `W = (s, u', Y)` layout. -/
def wS : Fin ((1 + kc) + (m + (kc + l))) := Fin.castAdd _ (Fin.castAdd kc 0)
def wU (q : Fin kc) : Fin ((1 + kc) + (m + (kc + l))) := Fin.castAdd _ (Fin.natAdd 1 q)
def wY (v : Fin (m + (kc + l))) : Fin ((1 + kc) + (m + (kc + l))) := Fin.natAdd (1 + kc) v

lemma evW_S : evW G e F γ w (wS (m := m) (l := l)) = T (-1) := by simp [evW, wS]

lemma evW_U (q : Fin kc) : evW G e F γ w (wU (m := m) (l := l) q) =
    LaurentPolynomial.C (toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l q)))) * T (w q) := by
  simp [evW, wU]

lemma aeval_evW_wY (p : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    aeval (evW G e F γ w) (rename wY p) = LaurentPolynomial.C (toAZ G e p) := by
  rw [aeval_rename]
  have : (aeval (evW G e F γ w ∘ wY)).toRingHom =
      (LaurentPolynomial.C : A →+* A[T;T⁻¹]).comp
        (e.toRingHom.comp ((Ideal.Quotient.mk _).comp toQZ)) := by
    refine MvPolynomial.ringHom_ext (fun n => intHom_C _ _ n) (fun v => ?_)
    simp [evW, wY, toQZ]
  exact RingHom.congr_fun this p

/-- **One integer `y`-row**: an expansion `C(b₀) y = Σᵢ C(bᵢ) T^{−exᵢ} ∏_q (C(u_q) T^{w_q})^{αᵢ_q}`, with
the head values `γ x̃_q ↦ E_q u_q`, is `aeval evW Q` of an integer `Q`, up to a positive integer. -/
theorem exists_yrow_int (y b₀ : A[T;T⁻¹]) (u : Fin kc → A) (Eh : Fin kc → ℕ) (hEh : ∀ q, 0 < Eh q)
    (hu : ∀ q, toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l q))) = (Eh q : A) * u q)
    {K : ℕ} (b : Fin K → A) (ex : Fin K → ℕ) (α : Fin K → Fin kc → ℕ)
    (hexp : b₀ * y = ∑ i, LaurentPolynomial.C (b i) * T (-(ex i : ℤ)) *
      ∏ q, (LaurentPolynomial.C (u q) * T (w q : ℤ)) ^ α i q) :
    ∃ (D : ℕ) (Q : MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ), 0 < D ∧
      aeval (evW G e F γ w) Q = (D : A[T;T⁻¹]) * (b₀ * y) := by
  obtain ⟨c, hc⟩ := Constructive.finite_choice_dep (ι := Fin K)
    (P := fun i (x : ℕ × MvPolynomial (Fin (m + (kc + l))) ℤ) =>
      0 < x.1 ∧ toAZ G e x.2 = (x.1 : A) * b i)
    fun i => by
      obtain ⟨D, pZ, hD, h⟩ := exists_toAq_int G e (b i)
      exact ⟨(D, pZ), hD, h⟩
  obtain ⟨D, k, hD, hk⟩ := exists_common_mul (fun i => (c i).1 * ∏ q, Eh q ^ α i q)
    fun i => Nat.mul_pos (hc i).1 (Finset.prod_pos fun q _ => pow_pos (hEh q) _)
  refine ⟨D, ∑ i, ((k i : ℕ) : MvPolynomial _ ℤ) * rename wY (c i).2 * X wS ^ ex i *
    ∏ q, X (wU q) ^ α i q, hD, ?_⟩
  rw [hexp, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_prod, map_natCast, aeval_X, aeval_evW_wY, evW_S, evW_U, hu,
    (hc i).2]
  rw [← hk i, T_pow]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_natCast, Nat.cast_mul, Nat.cast_prod,
    Nat.cast_pow, Finset.prod_pow, ← map_pow, ← map_prod]
  push_cast
  ring_nf

end BezoutCounterexample.Principalization
