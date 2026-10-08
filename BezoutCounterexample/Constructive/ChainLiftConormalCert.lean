import Mathlib
import BezoutCounterexample.Constructive.ChainLiftMinorPoly
import BezoutCounterexample.Constructive.ChainLiftSmoothCert

/-!
# Conormal injectivity from a smoothness certificate (Task B)

`ConormalInj G d` (`d f ∈ (G)²` whenever `f ∈ (G)` and all `∂_k f ∈ (G)`) was obtained from formal
smoothness by `FormallySmooth.iff_split_injection` (bridge (c), `exists_conormalRet`). From a
certificate it is explicit:

* `SquarePiece.retA`: on a piece, `a_k = Σᵢ adj(J)_{k,i} Fᵢ` (sum over the relation rows), so
  `Σ_k ∂_k Fᵢ · a_k = det J · Fᵢ` by `J · adj J = det J` (`sum_pderiv_retA`); for `g ∈ (G)`,
  `h^f · Σ_k ∂_k g · a_k ≡ det J · h^f · g` modulo `(G)²` (`retA_spec`);
* `SquarePiece.conormalInj`: `ConormalInj G (h^(e+f))`, using `det J · U ≡ hᵉ`;
* `conormalIdeal G`: the multipliers form an ideal containing `(G)`;
* `SmoothCert.conormalInj`: `ConormalInj G (C^M)` for an integer power of the cover constant
  (`Ideal.sum_pow_mem_span_pow` on the cover `C ≡ Σ uₖhₖ`).
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}

/-- The admissible conormal multipliers form an ideal. -/
def conormalIdeal (G : List (MvPolynomial (Fin (m + n)) ℤ)) :
    Ideal (MvPolynomial (Fin (m + n)) ℤ) where
  carrier := {d | ConormalInj G d}
  add_mem' {a b} ha hb f hf hdf := by
    rw [add_mul]; exact Ideal.add_mem _ (ha f hf hdf) (hb f hf hdf)
  zero_mem' f _ _ := by rw [zero_mul]; exact Ideal.zero_mem _
  smul_mem' c d hd f hf hdf := by
    rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ (hd f hf hdf)

lemma mem_conormalIdeal {d : MvPolynomial (Fin (m + n)) ℤ} :
    d ∈ conormalIdeal G ↔ ConormalInj G d := Iff.rfl

lemma lspan_le_conormalIdeal : lspan G ≤ conormalIdeal G := fun d hd f hf _ => by
  rw [pow_two]; exact Ideal.mul_mem_mul hd hf

lemma mem_lspan_ofFn {k : ℕ} {v : Fin k → MvPolynomial (Fin (m + n)) ℤ}
    {x : MvPolynomial (Fin (m + n)) ℤ} (hx : x ∈ lspan (List.ofFn v)) :
    ∃ c : Fin k → MvPolynomial (Fin (m + n)) ℤ, x = ∑ i, c i * v i := by
  have : lspan (List.ofFn v) = Ideal.span (Set.range v) := by
    rw [lspan]; congr 1; ext y; simp [List.mem_ofFn]
  rw [this, Ideal.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, hc.symm⟩

namespace SquarePiece

variable (P : SquarePiece m n G)

/-- The retraction vector `a_k = Σᵢ adj(J)_{k,i} Fᵢ` of a piece. -/
noncomputable def retA (k : Fin (m + n)) : MvPolynomial (Fin (m + n)) ℤ :=
  ∑ i : Fin m, (jacPoly P.F).adjugate k (Fin.castAdd n i) * P.F (Fin.castAdd n i)

lemma retA_mem (k : Fin (m + n)) : P.retA k ∈ lspan G :=
  Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (P.eqmem i)

lemma sum_pderiv_retA (i : Fin m) :
    ∑ k, pderiv k (P.F (Fin.castAdd n i)) * P.retA k =
      (jacPoly P.F).det * P.F (Fin.castAdd n i) := by
  have hentry : ∀ i' : Fin m,
      ∑ k, pderiv k (P.F (Fin.castAdd n i)) * ((jacPoly P.F).adjugate k (Fin.castAdd n i') *
        P.F (Fin.castAdd n i')) =
      (jacPoly P.F * (jacPoly P.F).adjugate) (Fin.castAdd n i) (Fin.castAdd n i') *
        P.F (Fin.castAdd n i') := by
    intro i'
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [jacPoly, Matrix.of_apply]; ring
  simp only [retA, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [hentry, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    (Fin.castAdd_injective m n).eq_iff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma hf_mem_feq {g : MvPolynomial (Fin (m + n)) ℤ} (hg : g ∈ lspan G) :
    P.h ^ P.f * g ∈ lspan (List.ofFn fun i : Fin m => P.F (Fin.castAdd n i)) := by
  induction hg using Submodule.span_induction with
  | mem x hx => exact P.genc x hx
  | zero => rw [mul_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx

/-- **The conormal retraction of a piece**, modulo `(G)²`. -/
lemma retA_spec {g : MvPolynomial (Fin (m + n)) ℤ} (hg : g ∈ lspan G) :
    P.h ^ P.f * ∑ k, pderiv k g * P.retA k - (jacPoly P.F).det * (P.h ^ P.f * g) ∈
      lspan G ^ 2 := by
  have hsq : ∀ x ∈ lspan G, ∀ y ∈ lspan G, x * y ∈ lspan G ^ 2 := fun x hx y hy => by
    rw [pow_two]; exact Ideal.mul_mem_mul hx hy
  obtain ⟨c, hc⟩ := mem_lspan_ofFn (P.hf_mem_feq hg)
  -- (1) the derivative of `h^f g`
  have h1 : ∑ k, pderiv k (P.h ^ P.f * g) * P.retA k -
      P.h ^ P.f * ∑ k, pderiv k g * P.retA k ∈ lspan G ^ 2 := by
    have : ∑ k, pderiv k (P.h ^ P.f * g) * P.retA k - P.h ^ P.f * ∑ k, pderiv k g * P.retA k =
        ∑ k, g * (pderiv k (P.h ^ P.f) * P.retA k) := by
      simp only [Derivation.leibniz, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
    rw [this]
    exact Ideal.sum_mem _ fun k _ => hsq _ hg _ (Ideal.mul_mem_left _ _ (P.retA_mem k))
  -- (2) the same via `h^f g = Σ cᵢ Fᵢ`
  have hder : ∀ k, pderiv k (P.h ^ P.f * g) = ∑ i,
      (c i * pderiv k (P.F (Fin.castAdd n i)) + P.F (Fin.castAdd n i) * pderiv k (c i)) := by
    intro k; rw [hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hsplit : ∑ k, pderiv k (P.h ^ P.f * g) * P.retA k =
      ∑ i, c i * ∑ k, pderiv k (P.F (Fin.castAdd n i)) * P.retA k +
        ∑ i, P.F (Fin.castAdd n i) * ∑ k, pderiv k (c i) * P.retA k := by
    simp only [hder, Finset.sum_mul, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun k i => c i * pderiv k (P.F (Fin.castAdd n i)) * P.retA k),
      Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun k i => P.F (Fin.castAdd n i) * pderiv k (c i) * P.retA k)]
    simp only [Finset.mul_sum, mul_assoc]
  have hdet : ∑ i, c i * ∑ k, pderiv k (P.F (Fin.castAdd n i)) * P.retA k =
      (jacPoly P.F).det * (P.h ^ P.f * g) := by
    simp only [P.sum_pderiv_retA, hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ k, pderiv k (P.h ^ P.f * g) * P.retA k - (jacPoly P.F).det * (P.h ^ P.f * g) ∈
      lspan G ^ 2 := by
    rw [hsplit, hdet, add_sub_cancel_left]
    exact Ideal.sum_mem _ fun i _ => hsq _ (P.eqmem i) _
      (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (P.retA_mem k))
  have := Ideal.sub_mem _ h2 h1
  rwa [sub_sub_sub_cancel_left] at this

/-- **`ConormalInj` on a piece**, with multiplier `h^(e+f)`. -/
theorem conormalInj : ConormalInj G (P.h ^ (P.e + P.f)) := by
  intro x hx hdx
  have hsq : ∀ a ∈ lspan G, ∀ b ∈ lspan G, a * b ∈ lspan G ^ 2 := fun a ha b hb => by
    rw [pow_two]; exact Ideal.mul_mem_mul ha hb
  have h1 : (jacPoly P.F).det * (P.h ^ P.f * x) ∈ lspan G ^ 2 := by
    have hs : P.h ^ P.f * ∑ k, pderiv k x * P.retA k ∈ lspan G ^ 2 :=
      Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun k _ => hsq _ (hdx k) _ (P.retA_mem k))
    have := Ideal.sub_mem _ hs (P.retA_spec hx)
    rwa [sub_sub_cancel] at this
  have h2 : ((jacPoly P.F).det * P.U - P.h ^ P.e) * (P.h ^ P.f * x) ∈ lspan G ^ 2 :=
    hsq _ P.detc _ (Ideal.mul_mem_left _ _ hx)
  have : P.h ^ (P.e + P.f) * x =
      P.U * ((jacPoly P.F).det * (P.h ^ P.f * x)) -
        ((jacPoly P.F).det * P.U - P.h ^ P.e) * (P.h ^ P.f * x) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) h2

end SquarePiece

namespace SmoothCert

/-- **`ConormalInj` from a certificate**, with an integer multiplier `C^M`. -/
theorem conormalInj (hG : SmoothCert m n G) :
    ∃ M : ℕ, ConormalInj G (((hG.C ^ M : ℕ)) : MvPolynomial (Fin (m + n)) ℤ) := by
  classical
  set E := ∑ k, ((hG.P k).e + (hG.P k).f)
  have hE : ∀ k, (hG.P k).e + (hG.P k).f ≤ E := fun k =>
    Finset.single_le_sum (s := (Finset.univ : Finset (Fin hG.K)))
      (f := fun k => (hG.P k).e + (hG.P k).f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  refine ⟨(Finset.univ : Finset (Fin hG.K)).card * E + 1, ?_⟩
  rw [← mem_conormalIdeal]
  have hspan := Ideal.sum_pow_mem_span_pow Finset.univ (fun k => hG.u k * (hG.P k).h) E
  have hle : Ideal.span ((fun k => (hG.u k * (hG.P k).h) ^ (E + 1)) '' (Finset.univ : Finset (Fin hG.K))) ≤
      conormalIdeal G := by
    rw [Ideal.span_le]
    rintro _ ⟨k, -, rfl⟩
    have hk := (hG.P k).conormalInj
    have : (hG.u k * (hG.P k).h) ^ (E + 1) =
        (hG.u k ^ (E + 1) * (hG.P k).h ^ (E + 1 - ((hG.P k).e + (hG.P k).f))) *
          (hG.P k).h ^ ((hG.P k).e + (hG.P k).f) := by
      rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel (by have := hE k; omega)]
    show (hG.u k * (hG.P k).h) ^ (E + 1) ∈ conormalIdeal G
    rw [this]
    exact Ideal.mul_mem_left _ _ hk
  have h1 := hle hspan
  have h2 : ((hG.C : MvPolynomial (Fin (m + n)) ℤ)) ^ ((Finset.univ : Finset (Fin hG.K)).card * E + 1) -
      (∑ k, hG.u k * (hG.P k).h) ^ ((Finset.univ : Finset (Fin hG.K)).card * E + 1) ∈ conormalIdeal G := by
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow ((hG.C : MvPolynomial (Fin (m + n)) ℤ))
      (∑ k, hG.u k * (hG.P k).h) ((Finset.univ : Finset (Fin hG.K)).card * E + 1)
    rw [hq]
    exact lspan_le_conormalIdeal (Ideal.mul_mem_right _ _ hG.cover)
  have := Ideal.add_mem _ h2 h1
  rw [sub_add_cancel] at this
  simpa [Nat.cast_pow] using this

end SmoothCert

end BezoutCounterexample.Constructive
