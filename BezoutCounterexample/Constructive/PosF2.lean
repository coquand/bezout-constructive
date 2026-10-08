import BezoutCounterexample.Constructive.KrullBar
import BezoutCounterexample.Constructive.DualityP

/-!
# (F1), (F2) as positive dichotomies (`~/COLL/bezout-positive.tex`, Lemma 1.1)

* `rees_escape`: in the Rees ring `B[Jt]` (inductively Noetherian), suppose that at every level
  either `d` goes one power deeper or an escape `D` holds: `d ∈ Jᵏ → d ∈ Jᵏ⁺¹ ∨ D`. Then
  `d ∈ J d` or `D`. This is `NBar.rees_or` of `KrullBar` with `pow_mem_or` replaced by the step
  hypothesis; the bar is the search bound, so no Markov principle is needed.
* `pos_F2`: for a partial chart `x, ∂` with `𝔭 = (x)` (`PChart`), the Rees ring of `𝔭`
  inductively Noetherian and `1 - a` a unit for `a ∈ 𝔭` (locality), and a decision
  `x ∈ 𝔭 ∨ E x` (at an explicit point `z`: `z(x) = 0`, or `E x := z(x) ≠ 0`), every `h` is `0` or
  has some derivative `∂^α h` with `E`. The step at level `k` tests the finitely many `α` of degree
  `k`; if all lie in `𝔭`, duality (`mem_F_iff`, weights `1`) puts `h` in `𝔭ᵏ⁺¹`.
-/

namespace BezoutCounterexample.Constructive

open Polynomial

section Escape

variable {B : Type*} [CommRing B]

/-- The bar invariant: the list is `d, d t, …, d tᵏ⁻¹` and `d ∈ Jᵏ`. -/
theorem NBar.rees_escape {J : Ideal B} {D : Prop} {d : B}
    (hstep : ∀ k, d ∈ J ^ k → d ∈ J ^ (k + 1) ∨ D) {L : List (reesSubring J)} (hL : NBar L) :
    ∀ k, L.map Subtype.val = pre (dPow d) k → d ∈ J ^ k → (∃ c ∈ J, d = c * d) ∨ D := by
  induction hL with
  | @good a l ha =>
    intro k hk _
    cases k with
    | zero => exact absurd hk (List.cons_ne_nil _ _)
    | succ m =>
      rw [List.map_cons, pre] at hk
      obtain ⟨h1, h2⟩ := List.cons.inj hk
      exact Or.inl (mem_mul_of_good h2 h1 ha)
  | @step l _ ih =>
    intro k hk hdk
    rcases hstep k hdk with h | hD
    · exact ih ⟨dPow d k, C_mul_X_pow_mem hdk⟩ (k + 1) (by rw [List.map_cons, hk]; rfl) h
    · exact Or.inr hD

/-- **The Rees bar with escape.** -/
theorem rees_escape {J : Ideal B} (hR : IndNoeth (reesSubring J)) {D : Prop} {d : B}
    (hstep : ∀ k, d ∈ J ^ k → d ∈ J ^ (k + 1) ∨ D) : (∃ c ∈ J, d = c * d) ∨ D :=
  NBar.rees_escape hstep hR 0 rfl (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)

end Escape

section Chart

variable {S : Type*} [CommRing S] [Algebra ℚ S] {j : ℕ} (c : PChart S j)

lemma wt_one (α : Fin j → ℕ) : wt (fun _ => 1) α = deg α := by simp [wt, deg]

/-- `x^β ∈ 𝔭^{|β|}`. -/
lemma mono_mem_P_pow (β : Fin j → ℕ) : c.mono β ∈ c.P ^ deg β := by
  have h : ∀ s : Finset (Fin j), ∏ i ∈ s, c.x i ^ β i ∈ c.P ^ (∑ i ∈ s, β i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (show c.x a ∈ c.P from Ideal.subset_span ⟨a, rfl⟩) _) ih
  exact h Finset.univ

/-- `F_t ≤ 𝔭ᵗ` for weights `1`. -/
lemma F_one_le_pow (t : ℕ) : c.F (fun _ => 1) t ≤ c.P ^ t := by
  rw [PChart.F, Ideal.span_le]
  rintro _ ⟨β, hβ, rfl⟩
  rw [wt_one] at hβ
  exact Ideal.pow_le_pow_right hβ (mono_mem_P_pow c β)

/-- `𝔭ᵗ ≤ F_t` for weights `1`. -/
lemma pow_le_F_one (t : ℕ) : c.P ^ t ≤ c.F (fun _ => 1) t := by
  induction t with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    intro x _
    have h1 : (1 : S) ∈ c.F (fun _ => 1) 0 := by
      have := c.mono_mem_F (w := fun _ => 1) (β := 0) (t := 0) (Nat.zero_le _)
      rwa [c.mono_zero] at this
    simpa using Ideal.mul_mem_left _ x h1
  | succ t ih =>
    rw [pow_succ, Ideal.mul_le]
    intro a ha b hb
    have ha' := ih ha
    rw [PChart.P] at hb
    refine Submodule.span_induction (p := fun b _ => a * b ∈ c.F (fun _ => 1) (t + 1)) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨i, rfl⟩
      rw [PChart.F] at ha'
      refine Submodule.span_induction (p := fun a _ => a * c.x i ∈ c.F (fun _ => 1) (t + 1))
        ?_ ?_ ?_ ?_ ha'
      · rintro _ ⟨β, hβ, rfl⟩
        rw [← c.mono_unit i, ← c.mono_add]
        refine c.mono_mem_F ?_
        rw [PChart.wt_add, PChart.wt_unit]; omega
      · rw [zero_mul]; exact Ideal.zero_mem _
      · intro u v _ _ hu hv; rw [add_mul]; exact Ideal.add_mem _ hu hv
      · intro r u _ hu; rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ hu
    · rw [mul_zero]; exact Ideal.zero_mem _
    · intro u v _ _ hu hv; rw [mul_add]; exact Ideal.add_mem _ hu hv
    · intro r u _ hu; rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hu

/-- Finitely many decisions. -/
lemma forall_or_exists_finset {P E : (Fin j → ℕ) → Prop} (h : ∀ α, P α ∨ E α) :
    ∀ s : Finset (Fin j → ℕ), (∀ α ∈ s, P α) ∨ ∃ α, E α := by
  intro s
  induction s using Finset.induction_on with
  | empty => exact Or.inl fun _ h => absurd h (Finset.notMem_empty _)
  | insert a s _ ih =>
    rcases ih with hs | he
    · rcases h a with ha | ha
      · refine Or.inl fun α hα => ?_
        rcases Finset.mem_insert.1 hα with rfl | hα
        · exact ha
        · exact hs α hα
      · exact Or.inr ⟨a, ha⟩
    · exact Or.inr he

/-- **Positive (F2)**: `h = 0`, or some derivative of `h` escapes. -/
theorem pos_F2 (hR : IndNoeth (reesSubring c.P)) (hloc : ∀ a ∈ c.P, IsUnit (1 - a))
    {E : S → Prop} (hdec : ∀ x : S, x ∈ c.P ∨ E x) (h : S) :
    h = 0 ∨ ∃ α, E (c.D α h) := by
  have hw : ∀ _ : Fin j, 1 ≤ (fun _ => 1 : Fin j → ℕ) ‹_› := fun _ => le_rfl
  have hstep : ∀ k, h ∈ c.P ^ k → h ∈ c.P ^ (k + 1) ∨ ∃ α, E (c.D α h) := by
    intro k hk
    have hlow := (c.mem_F_iff (fun _ => le_rfl) k h).1 (pow_le_F_one c k hk)
    rcases forall_or_exists_finset (P := fun α => c.D α h ∈ c.P) (E := fun α => E (c.D α h))
      (fun α => hdec _) (Finset.Nat.antidiagonalTuple j k) with hall | he
    · refine Or.inl (F_one_le_pow c (k + 1) ((c.mem_F_iff (fun _ => le_rfl) (k + 1) h).2 ?_))
      intro α hα
      rw [wt_one] at hα
      rcases Nat.lt_or_ge (deg α) k with hlt | hge
      · exact hlow α (by rw [wt_one]; exact hlt)
      · exact hall α (Finset.Nat.mem_antidiagonalTuple.2 (by
          show ∑ i, α i = k
          have : deg α = k := by omega
          exact this))
    · exact Or.inr he
  rcases rees_escape hR hstep with ⟨a, ha, hah⟩ | he
  · refine Or.inl ?_
    obtain ⟨u, hu⟩ := hloc a ha
    have h1 : (1 - a) * h = 0 := by rw [sub_mul, one_mul, ← hah, sub_self]
    rw [← hu] at h1
    exact (Units.mul_right_eq_zero u).1 h1
  · exact Or.inr he

end Chart

end BezoutCounterexample.Constructive
