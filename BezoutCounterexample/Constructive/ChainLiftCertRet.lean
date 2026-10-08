import Mathlib
import BezoutCounterexample.Constructive.ChainLiftConormal
import BezoutCounterexample.Constructive.ChainLiftConormalCert

/-!
# Conormal retraction data from a smoothness certificate (Task B, Rees layer S0)

`ConormalRet G D a` (`a_k ∈ (G)`, `D gⱼ ≡ Σ_k ∂_k gⱼ · a_k` modulo `(G)²`) was obtained from formal
smoothness (`exists_conormalRet`, classical). From a certificate it is explicit:

* `retIdeal G`: the multipliers `D` admitting retraction data form an ideal containing `(G)`;
* `SquarePiece.mem_retIdeal`: `h^(e+f) ∈ retIdeal G`, with `a_k = U · h^f · retA_k`
  (`retA_spec` and `det J · U ≡ hᵉ`);
* `SmoothCert.exists_pow_mem`: an ideal containing `(G)` and every `h_k^(e_k+f_k)` contains an
  integer power of the cover constant `C` (the power trick of `SmoothCert.conormalInj`);
* `SmoothCert.exists_conormalRet`: `ConormalRet G (C^M) a` for some `M`, `a`.

Over `ℚ` the multiplier `C^M` is a unit, so this is a retraction of the conormal sequence, hence
formal smoothness (`Principalization.ChainLiftCertSmooth`).
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}

/-- The multipliers admitting conormal retraction data form an ideal. -/
def retIdeal (G : List (MvPolynomial (Fin (m + n)) ℤ)) :
    Ideal (MvPolynomial (Fin (m + n)) ℤ) where
  carrier := {D | ∃ a, ConormalRet G D a}
  add_mem' {D D'} := by
    rintro ⟨a, ha, hr⟩ ⟨a', ha', hr'⟩
    refine ⟨a + a', fun k => Ideal.add_mem _ (ha k) (ha' k), fun j => ?_⟩
    have : (D + D') * G.get j - ∑ k, pderiv k (G.get j) * (a + a') k =
        (D * G.get j - ∑ k, pderiv k (G.get j) * a k) +
          (D' * G.get j - ∑ k, pderiv k (G.get j) * a' k) := by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
    rw [this]; exact Ideal.add_mem _ (hr j) (hr' j)
  zero_mem' := ⟨0, fun _ => Ideal.zero_mem _, fun j => by simp⟩
  smul_mem' c D := by
    rintro ⟨a, ha, hr⟩
    refine ⟨fun k => c * a k, fun k => Ideal.mul_mem_left _ _ (ha k), fun j => ?_⟩
    have : c • D * G.get j - ∑ k, pderiv k (G.get j) * (c * a k) =
        c * (D * G.get j - ∑ k, pderiv k (G.get j) * a k) := by
      rw [smul_eq_mul, mul_sub, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]; exact Ideal.mul_mem_left _ _ (hr j)

lemma mem_retIdeal {D : MvPolynomial (Fin (m + n)) ℤ} :
    D ∈ retIdeal G ↔ ∃ a, ConormalRet G D a := Iff.rfl

lemma lspan_le_retIdeal : lspan G ≤ retIdeal G := fun D hD =>
  ⟨0, fun _ => Ideal.zero_mem _, fun j => by
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]
    rw [pow_two]; exact Ideal.mul_mem_mul hD (get_mem_lspan G j)⟩

namespace SquarePiece

variable (P : SquarePiece m n G)

/-- **Retraction data of a piece**, with multiplier `h^(e+f)`. -/
theorem mem_retIdeal : P.h ^ (P.e + P.f) ∈ retIdeal G := by
  refine ⟨fun k => P.U * P.h ^ P.f * P.retA k,
    fun k => Ideal.mul_mem_left _ _ (P.retA_mem k), fun j => ?_⟩
  have hg := get_mem_lspan G j
  have hsq : ∀ x ∈ lspan G, ∀ y ∈ lspan G, x * y ∈ lspan G ^ 2 := fun x hx y hy => by
    rw [pow_two]; exact Ideal.mul_mem_mul hx hy
  have h1 := Ideal.mul_mem_left _ P.U (P.retA_spec hg)
  have h2 : ((jacPoly P.F).det * P.U - P.h ^ P.e) * (P.h ^ P.f * G.get j) ∈ lspan G ^ 2 :=
    hsq _ P.detc _ (Ideal.mul_mem_left _ _ hg)
  have : P.h ^ (P.e + P.f) * G.get j -
      ∑ k, pderiv k (G.get j) * (P.U * P.h ^ P.f * P.retA k) =
      -(P.U * (P.h ^ P.f * ∑ k, pderiv k (G.get j) * P.retA k -
        (jacPoly P.F).det * (P.h ^ P.f * G.get j))) -
        ((jacPoly P.F).det * P.U - P.h ^ P.e) * (P.h ^ P.f * G.get j) := by
    simp only [Finset.mul_sum]
    rw [pow_add]
    have : ∀ k, pderiv k (G.get j) * (P.U * P.h ^ P.f * P.retA k) =
        P.U * (P.h ^ P.f * (pderiv k (G.get j) * P.retA k)) := fun k => by ring
    simp only [this]
    rw [← Finset.mul_sum]
    ring
  rw [this]
  exact Ideal.sub_mem _ ((Ideal.neg_mem_iff _).2 h1) h2

end SquarePiece

namespace SmoothCert

/-- **The power trick**: an ideal containing `(G)` and every `h_k^(e_k+f_k)` contains an integer
power of the cover constant. -/
theorem exists_pow_mem (hG : SmoothCert m n G) (J : Ideal (MvPolynomial (Fin (m + n)) ℤ))
    (hJ : lspan G ≤ J) (hP : ∀ k, (hG.P k).h ^ ((hG.P k).e + (hG.P k).f) ∈ J) :
    ∃ M : ℕ, (((hG.C ^ M : ℕ)) : MvPolynomial (Fin (m + n)) ℤ) ∈ J := by
  set E := ∑ k, ((hG.P k).e + (hG.P k).f)
  have hE : ∀ k, (hG.P k).e + (hG.P k).f ≤ E := fun k =>
    Finset.single_le_sum (s := (Finset.univ : Finset (Fin hG.K)))
      (f := fun k => (hG.P k).e + (hG.P k).f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  refine ⟨(Finset.univ : Finset (Fin hG.K)).card * E + 1, ?_⟩
  have hspan := Ideal.sum_pow_mem_span_pow Finset.univ (fun k => hG.u k * (hG.P k).h) E
  have hle : Ideal.span ((fun k => (hG.u k * (hG.P k).h) ^ (E + 1)) ''
      (Finset.univ : Finset (Fin hG.K))) ≤ J := by
    rw [Ideal.span_le]
    rintro _ ⟨k, -, rfl⟩
    have : (hG.u k * (hG.P k).h) ^ (E + 1) =
        (hG.u k ^ (E + 1) * (hG.P k).h ^ (E + 1 - ((hG.P k).e + (hG.P k).f))) *
          (hG.P k).h ^ ((hG.P k).e + (hG.P k).f) := by
      rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel (by have := hE k; omega)]
    show (hG.u k * (hG.P k).h) ^ (E + 1) ∈ J
    rw [this]
    exact Ideal.mul_mem_left _ _ (hP k)
  have h1 := hle hspan
  have h2 : ((hG.C : MvPolynomial (Fin (m + n)) ℤ)) ^ ((Finset.univ : Finset (Fin hG.K)).card * E + 1) -
      (∑ k, hG.u k * (hG.P k).h) ^ ((Finset.univ : Finset (Fin hG.K)).card * E + 1) ∈ J := by
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow ((hG.C : MvPolynomial (Fin (m + n)) ℤ))
      (∑ k, hG.u k * (hG.P k).h) ((Finset.univ : Finset (Fin hG.K)).card * E + 1)
    rw [hq]
    exact hJ (Ideal.mul_mem_right _ _ hG.cover)
  have := Ideal.add_mem _ h2 h1
  rw [sub_add_cancel] at this
  simpa [Nat.cast_pow] using this

/-- **Conormal retraction data from a certificate**, with an integer multiplier `C^M`. -/
theorem exists_conormalRet (hG : SmoothCert m n G) :
    ∃ (M : ℕ) (a : Fin (m + n) → MvPolynomial (Fin (m + n)) ℤ),
      ConormalRet G (((hG.C ^ M : ℕ)) : MvPolynomial (Fin (m + n)) ℤ) a := by
  obtain ⟨M, a, ha⟩ := hG.exists_pow_mem (retIdeal G) lspan_le_retIdeal
    fun k => (hG.P k).mem_retIdeal
  exact ⟨M, a, ha⟩

end SmoothCert

end BezoutCounterexample.Constructive
