import Mathlib
import BezoutCounterexample.Constructive.ChainLiftMinor

/-!
# The tail minors cover (bridge (d), linear algebra)

`V⁰` (`N × n`, the chart derivations on the coordinates) has a left inverse `U` (`U V⁰ = 1`).
For the tail columns `t ↦ kc + t`, `E = V⁰_tail U_tail` is idempotent of trace `n - kc`, so by
`Constructive.sum_minors_of_sq` its principal minors sum to `1`; each is a product
`det V⁰_{τ,tail} · det U_{tail,τ}`. Hence the tail minors of `V⁰` generate the unit ideal
(`tail_minor_cover`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open Matrix BezoutCounterexample.Constructive

variable {S : Type*} [CommRing S] {N n : ℕ}

/-- The tail columns `t ↦ kc + t`. -/
def tailIdx {kc : ℕ} (hk : kc ≤ n) (t : Fin (n - kc)) : Fin n := ⟨kc + t, by omega⟩

/-- `(m)`-subsets of the rows, with their increasing enumeration. -/
abbrev RowIdx (N m : ℕ) : Type := ((Finset.univ : Finset (Fin N)).powersetCard m :
  Finset (Finset (Fin N)))

def RowIdx.enum {N m : ℕ} (τ : RowIdx N m) : Fin m → Fin N :=
  τ.1.orderEmbOfFin (Finset.mem_powersetCard.1 τ.2).2

/-- **The tail minors of `V⁰` cover.** -/
theorem tail_minor_cover [Algebra ℚ S] {kc : ℕ} (hk : kc ≤ n) (V0 : Matrix (Fin N) (Fin n) S)
    (U : Matrix (Fin n) (Fin N) S) (hUV : U * V0 = 1) :
    ∃ r : RowIdx N (n - kc) → S,
      ∑ τ, r τ * (V0.submatrix τ.enum (tailIdx hk)).det = 1 := by
  set A := V0.submatrix id (tailIdx hk)
  set B := U.submatrix (tailIdx hk) id
  have hBA : B * A = 1 := by
    ext t t'
    have := congrFun (congrFun hUV (tailIdx hk t)) (tailIdx hk t')
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [A, B, Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    rw [this]
    simp [tailIdx, Fin.ext_iff]
  set E := A * B
  have hE : E * E = (1 : S) • E := by
    rw [one_smul, Matrix.mul_assoc, ← Matrix.mul_assoc B, hBA, Matrix.one_mul]
  have htr : E.trace = ((n - kc : ℕ) : S) * 1 := by
    rw [Matrix.trace_mul_comm, hBA, Matrix.trace_one, Fintype.card_fin, mul_one]
  have hsum := sum_minors_of_sq E 1 (n - kc) hE htr
  rw [one_pow, ← Finset.sum_coe_sort] at hsum
  refine ⟨fun τ => (B.submatrix id τ.enum).det, ?_⟩
  rw [← hsum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  set e := (τ.1.orderIsoOfFin (Finset.mem_powersetCard.1 τ.2).2).toEquiv
  rw [← Matrix.det_submatrix_equiv_self e]
  have : (E.submatrix (Subtype.val : τ.1 → Fin N) Subtype.val).submatrix e e =
      V0.submatrix τ.enum (tailIdx hk) * B.submatrix id τ.enum := by
    ext i j
    simp [E, A, Matrix.mul_apply, RowIdx.enum, e]
  rw [this, Matrix.det_mul, mul_comm]

/-- The head columns `q ↦ q`. -/
def headIdx {kc : ℕ} (hk : kc ≤ n) (q : Fin kc) : Fin n := ⟨q, lt_of_lt_of_le q.2 hk⟩

/-- `Fin kc ⊕ Fin (n - kc) ≃ Fin n`, head then tail. -/
def headTail {kc : ℕ} (hk : kc ≤ n) : Fin kc ⊕ Fin (n - kc) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hk))

lemma headTail_inl {kc : ℕ} (hk : kc ≤ n) (q : Fin kc) : headTail hk (Sum.inl q) = headIdx hk q := by
  ext; simp [headTail, headIdx]

lemma headTail_inr {kc : ℕ} (hk : kc ≤ n) (t : Fin (n - kc)) :
    headTail hk (Sum.inr t) = tailIdx hk t := by
  ext; simp [headTail, tailIdx]

/-- **The Jacobian modulo the head ideal** is block triangular: if the head columns are
`c_q e_q` modulo `(x_head)` and the tail columns are `Vt`, then `det J ≡ Π c_q · det Vt_tail`. -/
theorem det_mod_head {kc : ℕ} (hk : kc ≤ n) (J : Matrix (Fin n) (Fin n) S) (x : Fin kc → S)
    (cd : Fin kc → S) (Vt : Matrix (Fin (n - kc)) (Fin n) S)
    (hhead : ∀ l (q : Fin kc), J l (headIdx hk q) - (if l = headIdx hk q then cd q else 0) ∈
      Ideal.span (Set.range x))
    (htail : ∀ l t, J l (tailIdx hk t) = Vt t l) :
    J.det - (∏ q, cd q) * (Vt.submatrix id (tailIdx hk)).det ∈ Ideal.span (Set.range x) := by
  set π := Ideal.Quotient.mk (Ideal.span (Set.range x))
  rw [← Ideal.Quotient.eq]
  have hJ : (J.map π).submatrix (headTail hk) (headTail hk) =
      Matrix.fromBlocks (Matrix.diagonal fun q => π (cd q))
        (Matrix.of fun q t => π (Vt t (headIdx hk q))) 0
        ((Vt.submatrix id (tailIdx hk)).map π)ᵀ := by
    ext (l | l) (j | j)
    · have := Ideal.Quotient.eq.2 (hhead (headIdx hk l) j)
      simp only [Matrix.submatrix_apply, headTail_inl, Matrix.map_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.diagonal_apply]
      rw [this]
      by_cases h : l = j
      · subst h; simp; rfl
      · have : headIdx hk l ≠ headIdx hk j := fun e => h (by
          simpa [headIdx, Fin.ext_iff] using e)
        simp [this, h]
    · simp only [Matrix.submatrix_apply, headTail_inl, headTail_inr, Matrix.map_apply,
        Matrix.fromBlocks_apply₁₂, Matrix.of_apply, htail]
    · have := Ideal.Quotient.eq.2 (hhead (tailIdx hk l) j)
      simp only [Matrix.submatrix_apply, headTail_inl, headTail_inr, Matrix.map_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [this]
      have : tailIdx hk l ≠ headIdx hk j := fun e => by
        have := congrArg Fin.val e
        simp [tailIdx, headIdx] at this; omega
      simp [this]
    · simp only [Matrix.submatrix_apply, headTail_inr, Matrix.map_apply,
        Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, htail, id]
  have hdet : π J.det = ((J.map π).submatrix (headTail hk) (headTail hk)).det := by
    rw [Matrix.det_submatrix_equiv_self, RingHom.map_det]; rfl
  rw [hdet, hJ, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal, Matrix.det_transpose,
    map_mul, map_prod, RingHom.map_det]
  rfl

end BezoutCounterexample.Principalization
