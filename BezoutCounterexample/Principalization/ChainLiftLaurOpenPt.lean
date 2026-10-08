import Mathlib
import BezoutCounterexample.Principalization.ChainLiftLaurL3
import BezoutCounterexample.Principalization.ChainLiftReesOpenPt

/-!
# The Laurent opens of the Rees algebra (Task B, Rees layer S6, producer part 4)

A Laurent open is given by `ε ∈ ℤ[Y]` and a global preimage `Pt` of `t = C(ε) T`. The rows are
exact over `ℤ`: `β = εᵈ`, `Qⱼ = ε^{d−δⱼ} gⱼ t^{δⱼ}` (`δⱼ ≤ d`), and `s·Pt − ε`. They are appended to
the kernel, L3 is `l3L_hφ` (made uniform over `GR` as `n! · dAⁿ`), and the result is packaged by
`exists_laurChart_open`. No local data is used: on `D(ε)` everything is a unit.

* `rowsL`, `rowsL_vanish`, `laur_open_of_rows`: the rows and the producer in a common `GR`
  (any `A`-piece `S`);
* `exists_laurT`: a `Pt` for an element `f` with `C(f) T` in the Rees algebra, up to a positive integer
  (`ε := D ε₀`); for the open `D(i)`, `i ∈ 𝔭` (`i^N ∈ F₁`). The head opens of a weighted chart use
  `Pt = s^{w−1} P̃_q` directly.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

set_option linter.unusedSectionVars false

variable {A : Type} [CommRing A] [Algebra ℚ A] {m kc l r : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (gZ : Fin r → MvPolynomial (Fin (m + (kc + l))) ℤ) (δ : Fin r → ℕ)

/-- The Laurent `y`-rows `ε^{d−δⱼ} gⱼ t^{δⱼ}` in the layout `(Y, s, t)`. -/
def laurQ (ε : MvPolynomial (Fin (m + (kc + l))) ℤ) (d : ℕ) (j : Fin r) :
    MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ :=
  rename (Fin.castAdd (1 + 1)) (ε ^ (d - δ j) * gZ j) * X (Fin.natAdd _ (Fin.natAdd 1 0)) ^ δ j

lemma aeval_evWL_castAdd (ε : MvPolynomial (Fin (m + (kc + l))) ℤ)
    (p : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    aeval (evWL G e ε) (rename (Fin.castAdd (1 + 1)) p) = LaurentPolynomial.C (toAZ G e p) := by
  rw [aeval_rename]
  have : (aeval (evWL G e ε ∘ Fin.castAdd (1 + 1))).toRingHom =
      (LaurentPolynomial.C : A →+* A[T;T⁻¹]).comp
        (e.toRingHom.comp ((Ideal.Quotient.mk _).comp toQZ)) := by
    refine MvPolynomial.ringHom_ext (fun n => intHom_C _ _ n) (fun v => ?_)
    simp [evWL, toQZ]
  exact RingHom.congr_fun this p

/-- The Laurent rows are exact: `C(εᵈ) yⱼ = Qⱼ(Y, T⁻¹, C(ε) T)`. -/
lemma laurQ_hy (ε : MvPolynomial (Fin (m + (kc + l))) ℤ) {d : ℕ} (hδ : ∀ j, δ j ≤ d) (j : Fin r) :
    LaurentPolynomial.C (toAZ G e (ε ^ d)) * reesYL G e gZ δ j =
      aeval (evWL G e ε) (laurQ gZ δ ε d j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (hδ j)
  rw [laurQ, Nat.add_sub_cancel_left, map_mul, aeval_evWL_castAdd, map_pow, aeval_X]
  simp only [evWL, Fin.addCases_right]
  rw [reesYL, show toAq G e (toQZ (gZ j)) = toAZ G e (gZ j) from rfl, mul_pow, T_pow, mul_one]
  simp only [toAZ_mul', toAZ, map_pow, map_mul, pow_add]
  ring

/-- Under `t ↦ Pt`, `ψ_W` followed by the global evaluation is `evWL`. -/
lemma aeval_evG_laurψW (Ly : Fin r → A[T;T⁻¹]) (ε : MvPolynomial (Fin (m + (kc + l))) ℤ)
    (Pt : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hPt : aeval (evG G e Ly) Pt = LaurentPolynomial.C (toAZ G e ε) * T 1)
    (q : MvPolynomial (Fin ((m + (kc + l)) + (1 + 1))) ℤ) :
    aeval (evG G e Ly) (aeval (laurψW Pt) q) = aeval (evWL G e ε) q := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  suffices hfun : (fun i => aeval (evG G e Ly) (laurψW Pt i)) = evWL G e ε by rw [hfun]
  funext v
  refine Fin.addCases (fun v => ?_) (fun v => ?_) v
  · simp [laurψW, evWL, evG, gY]
  · refine Fin.addCases (fun o => ?_) (fun o => ?_) v
    · simp [laurψW, evWL, evG_gS]
    · simp only [laurψW, evWL, Fin.addCases_right, aeval_X]
      exact hPt

/-- **The rows of a Laurent open**: `F_eq`, `s·Pt − ε`, and `εᵈ yⱼ − Qⱼ(Y, s, Pt)`. -/
def rowsL (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ) (d : ℕ)
    (ε : MvPolynomial (Fin (m + (kc + l))) ℤ) (Pt : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) :
    List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) :=
  (List.ofFn fun i : Fin m => rename gY (F (Fin.castAdd _ i))) ++
  [X gS * Pt - rename gY ε] ++
  (List.ofFn fun j : Fin r => rename gY (ε ^ d) * X (gYr j) - aeval (laurψW Pt) (laurQ gZ δ ε d j))

lemma rowsL_vanish (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
    (hF : ∀ i : Fin m, F (Fin.castAdd _ i) ∈ lspan G) {d : ℕ} (hδ : ∀ j, δ j ≤ d)
    (ε : MvPolynomial (Fin (m + (kc + l))) ℤ) (Pt : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hPt : aeval (evG G e (reesYL G e gZ δ)) Pt = LaurentPolynomial.C (toAZ G e ε) * T 1) :
    ∀ x ∈ rowsL gZ δ F d ε Pt, aeval (evG G e (reesYL G e gZ δ)) x = 0 := by
  intro x hx
  simp only [rowsL, List.mem_append, List.mem_ofFn, List.mem_singleton] at hx
  rcases hx with (⟨i, rfl⟩ | rfl) | ⟨j, rfl⟩
  · rw [aeval_evG_gY, toAZ_eq_zero_of_mem G e (hF i), map_zero]
  · rw [map_sub, map_mul, aeval_X, evG_gS, hPt, aeval_evG_gY, mul_comm (T _),
      mul_assoc (LaurentPolynomial.C _), ← T_add, show (1 : ℤ) + -1 = 0 by norm_num, T_zero,
      mul_one, sub_self]
  · rw [map_sub, map_mul, aeval_evG_gY, aeval_X, evG_gYr,
      aeval_evG_laurψW G e (reesYL G e gZ δ) ε Pt hPt, ← laurQ_hy G e gZ δ ε hδ j, sub_self]

/-- **A Laurent open of the Rees algebra from its rows.** For `ε ∈ ℤ[Y]` with a global preimage
`Pt` of `C(ε) T`, any `A`-piece `S`, and a global presentation `GR` containing the rows: chart data
and conormal injectivity on the open of `dW = n! · (S.h εᵈ ε)ⁿ`, renamed along `ε'`. -/
theorem laur_open_of_rows (S : SquarePiece m (kc + l) G) {d : ℕ} (hδ : ∀ j, δ j ≤ d)
    (ε : MvPolynomial (Fin (m + (kc + l))) ℤ) (Pt : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (GR : List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ))
    (hGR0 : ∀ g ∈ GR, aeval (evG G e (reesYL G e gZ δ)) g = 0)
    (hrows : ∀ x ∈ rowsL gZ δ S.F d ε Pt, x ∈ lspan GR)
    (ε' : Fin ((m + (kc + l)) + (1 + r)) ≃ Fin ((m + r) + ((1 + kc) + l))) :
    ∃ n : ℕ,
      let dW : MvPolynomial (Fin (((m + 1) + r) + ((1 + kc) + l))) ℤ :=
        ((n.factorial : ℕ) : MvPolynomial _ ℤ) * rename lvarY (S.h * (ε ^ d * ε)) ^ n
      let GR' := GR.map (rename ε')
      let ψ' := fun i => rename ε' (laurψ Pt i)
      (∃ T : ChartData GR', T.x = (fun i => rename ε' (Fin.addCases (Fin.addCases
          (fun _ => X gS) (fun q => rename gY (S.F (Fin.natAdd m (Fin.castAdd l q)))))
          (fun z => rename gY (S.F (Fin.natAdd m (Fin.natAdd kc z)))) i)) ∧
        T.c = aeval ψ' (dW ^ 2 * (1 ^ 2 *
          (jacPoly (laurSys S.F ε (ε ^ d) (laurQ gZ δ ε d))).det))) ∧
      ConormalInj GR' (aeval ψ' ((jacPoly (laurSys S.F ε (ε ^ d) (laurQ gZ δ ε d))).det * dW ^ 2)) := by
  set Q := laurQ gZ δ ε d
  set β := ε ^ d
  set dA := S.h * (β * ε) with hdA
  have hy : ∀ j, LaurentPolynomial.C (toAZ G e β) * reesYL G e gZ δ j =
      aeval (evWL G e ε) (Q j) := laurQ_hy G e gZ δ ε hδ
  -- L3, uniformly over `GR`
  obtain ⟨n, hn⟩ := exists_fact_pow_list (lspan (sysEq (laurSys S.F ε β Q))) (rename lvarY dA)
    (fun g => aeval laurφ g) GR fun g hg =>
      l3L_hφ G e S.F ε β Q S.h S.f S.genc dA (β * ε) (S.h * ε) (S.h * β) rfl (by rw [hdA]; ring)
        (by rw [hdA]; ring) (reesYL G e gZ δ) hy g (hGR0 g hg)
  refine ⟨n, ?_⟩
  exact exists_laurChart_open S.F ε β Q Pt GR ε'
    (fun i => hrows _ (by simp [rowsL]))
    (hrows _ (by simp [rowsL]))
    (fun j => hrows _ (by simp [rowsL, Q, β]))
    _ fun g hg => by rw [mul_assoc]; exact hn g hg n le_rfl

/-- **A preimage of `t`** for an element of `F₁`: `ε ↦ c f` (`c > 0`) and `Pt ↦ C(ε) T`. -/
lemma exists_laurT (Φ : WFil A) (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
    (hgF : ∀ i, toAq G e (toQZ (gZ i)) ∈ Φ.F (δ i))
    (hgen : ∀ (j : ℤ) (f : A), f ∈ Φ.F j →
      LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (insert (T (-1)) (Set.range (reesYL G e gZ δ))))
    {f : A} (hf : f ∈ Φ.F 1) :
    ∃ (ε : MvPolynomial (Fin (m + (kc + l))) ℤ) (c : ℕ)
      (Pt : MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ),
      0 < c ∧ toAZ G e ε = (c : A) * f ∧
      aeval (evG G e (reesYL G e gZ δ)) Pt = LaurentPolynomial.C (toAZ G e ε) * T 1 := by
  obtain ⟨Pq, hPq⟩ := reesAlg_le_range G e gZ δ Φ hneg hgF hgen (C_mul_T_mem_ReesAlg hf)
  obtain ⟨D, P', hD, hP'⟩ := int_clear Pq
  obtain ⟨c, ε₀, hc, hε₀⟩ := exists_toAq_int G e f
  refine ⟨(D : MvPolynomial _ ℤ) * ε₀, D * c, (c : MvPolynomial _ ℤ) * P', Nat.mul_pos hD hc,
    ?_, ?_⟩
  · rw [toAZ_mul', toAZ_natCast, show toAZ G e ε₀ = toAq G e (toQZ ε₀) from rfl, hε₀]
    push_cast; ring
  · have h1 : aeval (evG G e (reesYL G e gZ δ)) P' =
        aeval (R := ℚ) (reesVec G e gZ δ) (toQZ P') := by
      rw [← evG_reesYL G e gZ δ]; exact (aeval_int_cast _ _).symm
    rw [map_mul, map_natCast, h1, hP', map_mul, map_natCast, hPq, toAZ_mul', toAZ_natCast,
      show toAZ G e ε₀ = toAq G e (toQZ ε₀) from rfl, hε₀]
    simp only [map_mul, map_natCast]
    ring

end BezoutCounterexample.Principalization
