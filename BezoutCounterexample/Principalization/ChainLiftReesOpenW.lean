import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesL3d

/-!
# The weighted-chart open from L3 (Task B, Rees layer S6, producer part 1)

`exists_reesChart_of_l3`: L3 (`l3_hφ` for every global relation, `l3_hu` for every head coordinate)
gives the multipliers `dW` and `b` of `exists_reesChart_open`. Both are made uniform as
`n! · dAⁿ` (`exists_fact_pow`): integers are absorbed by a factorial, powers of `dA` by `n`.
The theorem uses no local data. The chart's `LocDataPt` enters only through `Hloc`
(`hloc_of_cent` + `hcent_of_locDataPt`); the rows enter only through `hy`/`hP`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive

/-- **Integer and power multipliers, uniformly**: `D (aᴺ x) ∈ J` with `D > 0` gives
`n'! (a^{n'} x) ∈ J` for all large `n'`. -/
lemma exists_fact_pow {R : Type*} [CommRing R] (J : Ideal R) (a x : R)
    (h : ∃ N D : ℕ, 0 < D ∧ (D : R) * (a ^ N * x) ∈ J) :
    ∃ n : ℕ, ∀ n', n ≤ n' → ((n'.factorial : ℕ) : R) * (a ^ n' * x) ∈ J := by
  obtain ⟨N, D, hD, hJ⟩ := h
  refine ⟨max N D, fun n' hn' => ?_⟩
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hD (le_trans (le_max_right _ _) hn')
  have hN : N ≤ n' := le_trans (le_max_left _ _) hn'
  have : ((n'.factorial : ℕ) : R) * (a ^ n' * x) = ((k : R) * a ^ (n' - N)) * ((D : R) * (a ^ N * x)) := by
    rw [hk, Nat.cast_mul, ← Nat.sub_add_cancel hN, pow_add, Nat.add_sub_cancel]
    ring
  rw [this]
  exact J.mul_mem_left _ hJ

/-- Uniformity over a list for `exists_fact_pow`. -/
lemma exists_fact_pow_list {R α : Type*} [CommRing R] (J : Ideal R) (a : R) (x : α → R)
    (L : List α) (h : ∀ i ∈ L, ∃ N D : ℕ, 0 < D ∧ (D : R) * (a ^ N * x i) ∈ J) :
    ∃ n : ℕ, ∀ i ∈ L, ∀ n', n ≤ n' → ((n'.factorial : ℕ) : R) * (a ^ n' * x i) ∈ J := by
  induction L with
  | nil => exact ⟨0, fun _ hi => absurd hi List.not_mem_nil⟩
  | cons i₀ L ih =>
    obtain ⟨n₀, hn₀⟩ := exists_fact_pow J a (x i₀) (h i₀ List.mem_cons_self)
    obtain ⟨n₁, hn₁⟩ := ih fun i hi => h i (List.mem_cons_of_mem _ hi)
    refine ⟨max n₀ n₁, fun i hi n' hn' => ?_⟩
    rcases List.mem_cons.1 hi with rfl | hi
    · exact hn₀ _ (le_trans (le_max_left _ _) hn')
    · exact hn₁ i hi _ (le_trans (le_max_right _ _) hn')

variable {A : Type} [CommRing A] [Algebra ℚ A] {m kc l r : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (γ β : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ)
  (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)

open LaurentPolynomial hiding C

/-- **The weighted-chart open from L3**: chart data and conormal injectivity of the global
presentation `GR` on the open of `dW = n! · dAⁿ` (renamed along `ε`). -/
theorem exists_reesChart_of_l3 (h : MvPolynomial (Fin (m + (kc + l))) ℤ) (f : ℕ)
    (hgen : ∀ g ∈ G, h ^ f * g ∈ lspan (List.ofFn fun i : Fin m => F (Fin.castAdd (kc + l) i)))
    (dA ch cb : MvPolynomial (Fin (m + (kc + l))) ℤ) (hdh : dA = h * ch) (hdb : dA = β * cb)
    (Ly : Fin r → A[T;T⁻¹])
    (hy : ∀ j, LaurentPolynomial.C (toAZ G e β) * Ly j = aeval (evW G e F γ w) (Q j))
    (Hloc : ∀ q : Pt A, toAZ G e dA ∉ q.ker →
      ∀ p : MvPolynomial (Option (Fin kc)) (Localization.AtPrime q.ker),
        aeval (lGen (xq G e F γ q) w) p = 0 → p ∈ Ideal.span (Set.range (lRel (xq G e F γ q) w)))
    (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hP : ∀ i, aeval (evG G e Ly) (P i) =
      LaurentPolynomial.C (toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i)))) * T (w i))
    (GR : List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ))
    (hGR : ∀ g ∈ GR, aeval (evG G e Ly) g = 0)
    (ε : Fin ((m + (kc + l)) + (1 + r)) ≃ Fin ((m + r) + ((1 + kc) + l)))
    (hFeq : ∀ i : Fin m, rename gY (F (Fin.castAdd _ i)) ∈ lspan GR)
    (hhead : ∀ q : Fin kc,
      rename gY (γ * F (Fin.natAdd m (Fin.castAdd l q))) - X gS ^ w q * P q ∈ lspan GR)
    (hyrow : ∀ j : Fin r, rename gY β * X (gYr j) - aeval (reesψW P) (Q j) ∈ lspan GR) :
    ∃ n : ℕ,
      let dW : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ :=
        ((n.factorial : ℕ) : MvPolynomial _ ℤ) * rename varY dA ^ n
      let GR' := GR.map (rename ε)
      let ψ' := fun i => rename ε (reesψ P i)
      (∃ T : ChartData GR', T.x = (fun i => rename ε (Fin.addCases (Fin.addCases
          (fun _ => X gS) P) (fun z => rename gY (F (Fin.natAdd m (Fin.natAdd kc z)))) i)) ∧
        T.c = aeval ψ' (dW ^ 2 * (dW ^ 2 * (jacPoly (reesSys F γ β w Q)).det))) ∧
      ConormalInj GR' (aeval ψ' ((jacPoly (reesSys F γ β w Q)).det * dW ^ 2)) := by
  set J := lspan (sysEq (reesSys F γ β w Q))
  set a : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ := rename varY dA
  -- `hφ`: uniform over `GR`
  obtain ⟨n₁, hn₁⟩ := exists_fact_pow_list J a (fun g => aeval reesφ g) GR fun g hg =>
    l3_hφ G e F γ β w Q h f hgen dA ch cb hdh hdb Ly hy Hloc g (hGR g hg)
  -- `hu`: uniform over the heads
  obtain ⟨n₂, hn₂⟩ := exists_fact_pow_list J a (fun i => aeval reesφ (P i) - X (varU i))
    (List.finRange kc) fun i _ => l3_hu G e F γ β w Q h f hgen dA ch cb hdh hdb Ly hy Hloc P i (hP i)
  set n := max n₁ n₂
  refine ⟨n, ?_⟩
  intro dW GR' ψ'
  have key : ∀ x, (∃ n₀, n₀ ≤ n ∧ ((n₀.factorial : ℕ) : MvPolynomial _ ℤ) * (a ^ n₀ * x) ∈ J) →
      dW * x ∈ J := by
    rintro x ⟨n₀, hn₀, hx⟩
    obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hn₀
    have : dW * x = ((k : MvPolynomial _ ℤ) * a ^ (n - n₀)) *
        (((n₀.factorial : ℕ) : MvPolynomial _ ℤ) * (a ^ n₀ * x)) := by
      simp only [dW, hk, Nat.cast_mul]
      rw [← Nat.sub_add_cancel hn₀, pow_add, Nat.add_sub_cancel]
      ring
    rw [this]; exact J.mul_mem_left _ hx
  have hcert := exists_reesChart_open F γ β w Q P GR ε hFeq hhead hyrow dW
    (fun g hg => key _ ⟨n, le_rfl, hn₁ g hg n (le_max_left _ _)⟩) dW
    (fun i => key _ ⟨n, le_rfl, hn₂ i (List.mem_finRange i) n (le_max_right _ _)⟩)
  exact hcert

end BezoutCounterexample.Principalization
