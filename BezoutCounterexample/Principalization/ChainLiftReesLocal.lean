import Mathlib
import BezoutCounterexample.Principalization.ChainLiftBridgeHead

/-!
# The Rees algebra on one chart of the cover (Task B, Rees layer S5a)

Generic in the filtration: `Φ : WFil A` with `Φ.F j = compFPt I 𝔭 (j / d)` (R1, a hypothesis here;
`rfl` for D3.3d's `compFil`). For a chart `D k` of a `ChartCoverPt` with integer weights
`w = d · ek` and head numerators `a` (`exists_numerators`), in `A[T;T⁻¹]`:

* `exists_heads_rees` (**L1**): one `N` with `uₗ := C(gᴺ aₗ) T^{wₗ} ∈ ReesAlg Φ` for every `l`
  (`lid_A_pt` for the heads; `wₗ = 0` otherwise);
* `exists_rees_expansion` (**L2**): for `z ∈ Φ.F j`, `C(gˢ z) Tʲ = Σᵢ C(bᵢ) s^{eᵢ} ∏ₗ uₗ^{αᵢₗ}` with
  `s = T⁻¹`, `α` supported on the heads and `eᵢ + j = Σₗ αᵢₗ wₗ` (`hid_A_pt`).

L2 for the generators `yⱼ = C(gⱼ) T^{δⱼ}` is the `y`-row `β yⱼ − Qⱼ(s, u')` of the weighted-chart
model (`reesSys`), L1 is its head row `γ x̃ₗ − s^{wₗ} u'ₗ` (`C(gᴺ aₗ) = s^{wₗ} uₗ`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} {𝔭 : Ideal A}
  (hZp : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀)
  (Cp : ChartCoverPt I v₀ 𝔭) (Φ : WFil A) {d : ℕ}
  (hΦ : ∀ j : ℤ, Φ.F j = compFPt I 𝔭 ((j : ℚ) / d)) (hd : 0 < d)

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
lemma prod_T {ι : Type*} [DecidableEq ι] (u : Finset ι) (f : ι → ℤ) : ∏ l ∈ u, (T (f l) : A[T;T⁻¹]) = T (∑ l ∈ u, f l) := by
  induction u using Finset.induction_on with
  | empty => simp
  | insert x u hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, T_add]

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- A monomial in the `C(xₗ) T^{wₗ}` is `C(x^α) T^{Σ αₗ wₗ}`. -/
lemma prod_C_mul_T_pow {n : ℕ} (x : Fin n → A) (w : Fin n → ℕ) (α : Fin n →₀ ℕ) :
    ∏ l, (C (x l) * T (w l : ℤ)) ^ α l =
      C (∏ l, x l ^ α l) * T ((∑ l, α l * w l : ℕ) : ℤ) := by
  rw [map_prod, Nat.cast_sum, ← prod_T, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [mul_pow, ← map_pow, T_pow]
  push_cast; ring_nf

include hI hZp hΦ hd in
/-- **L1**: one power of the chart element puts every `C(aₗ) T^{wₗ}` into the Rees algebra. -/
theorem exists_heads_rees [Fact (Constructive.HasPres A)] (k : Fin Cp.n) (s : ℕ)
    (a : Fin (Cp.D k).n → A)
    (ha : ∀ i, (Cp.D k).cB.x i * algebraMap A (Cp.D k).B (Cp.D k).g ^ s =
      algebraMap A (Cp.D k).B (a i))
    (w : Fin (Cp.D k).n → ℕ) (hw : ∀ l, (w l : ℚ) = d * (Cp.D k).ek l) :
    ∃ N : ℕ, ∀ l, C ((Cp.D k).g ^ N * a l) * T (w l : ℤ) ∈ ReesAlg Φ := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  obtain ⟨N, hN⟩ := exists_uniform_list
    (P := fun l N => C ((Cp.D k).g ^ N * a l) * T (w l : ℤ) ∈ ReesAlg Φ)
    (fun l m n hmn hm => by
      rw [← Nat.sub_add_cancel hmn, pow_add, mul_assoc, map_mul, mul_assoc]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hm)
    (List.finRange (Cp.D k).n) fun l _ => by
      by_cases hl : (Cp.D k).ek l = 0
      · refine ⟨0, ?_⟩
        have hwl : w l = 0 := by have := hw l; rw [hl, mul_zero] at this; exact_mod_cast this
        rw [hwl, Nat.cast_zero, T_zero, mul_one]
        exact Subalgebra.algebraMap_mem _ _
      · obtain ⟨N, hN⟩ := lid_A_pt hI hZp Cp k s a ha l hl
        refine ⟨N, C_mul_T_mem_ReesAlg ?_⟩
        rw [hΦ, Int.cast_natCast, hw l, mul_div_cancel_left₀ _ hdq]
        exact hN
  exact ⟨N, fun l => hN l (List.mem_finRange l)⟩

include hI hZp hΦ hd in
/-- **L2**: an element of `F_j`, times a power of the chart element, is a polynomial in
`s = T⁻¹` and the `uₗ = C(gᴺ aₗ) T^{wₗ}` (any `N`), with coefficients in `A`. -/
theorem exists_rees_expansion [Fact (Constructive.HasPres A)] (k : Fin Cp.n) (s : ℕ)
    (a : Fin (Cp.D k).n → A)
    (ha : ∀ i, (Cp.D k).cB.x i * algebraMap A (Cp.D k).B (Cp.D k).g ^ s =
      algebraMap A (Cp.D k).B (a i))
    (w : Fin (Cp.D k).n → ℕ) (hw : ∀ l, (w l : ℚ) = d * (Cp.D k).ek l) (N : ℕ)
    {j : ℤ} {z : A} (hz : z ∈ Φ.F j) :
    ∃ (S K : ℕ) (b : Fin K → A) (α : Fin K → (Fin (Cp.D k).n →₀ ℕ)) (e : Fin K → ℕ),
      (∀ i l, (Cp.D k).ek l = 0 → α i l = 0) ∧
      (∀ i, (e i : ℤ) + j = ((∑ l, α i l * w l : ℕ) : ℤ)) ∧
      C ((Cp.D k).g ^ S * z) * T j =
        ∑ i, C (b i) * T (-(e i : ℤ)) *
          ∏ l, (C ((Cp.D k).g ^ N * a l) * T (w l : ℤ)) ^ α i l := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  rw [hΦ] at hz
  obtain ⟨S, K, b, α, hα0, hαt, hS⟩ := hid_A_pt hI hZp Cp k s a ha hz
  -- the weight inequality in `ℤ`
  have hle : ∀ i, j ≤ ((∑ l, α i l * w l : ℕ) : ℤ) := by
    intro i
    have h := hαt i
    rw [lam, div_le_iff₀ hdq] at h
    have : ((∑ l, α i l * w l : ℕ) : ℚ) = (∑ l, (α i l : ℚ) * (Cp.D k).ek l) * d := by
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hw l]; ring
    exact_mod_cast (show (j : ℚ) ≤ ((∑ l, α i l * w l : ℕ) : ℚ) by rw [this]; exact h)
  set M := ∑ i, ∑ l, α i l
  have hMi : ∀ i, ∑ l, α i l ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => ∑ l, α i l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨S + N * M, K, fun i => b i * (Cp.D k).g ^ (N * (M - ∑ l, α i l)), α,
    fun i => (((∑ l, α i l * w l : ℕ) : ℤ) - j).toNat, hα0, fun i => ?_, ?_⟩
  · dsimp only
    have := hle i
    omega
  · -- `gᴺᴹ ∏ aₗ^{αₗ} = g^{N(M − |α|)} ∏ (gᴺ aₗ)^{αₗ}`
    have hmon : ∀ i, (Cp.D k).g ^ (N * M) * ∏ l, a l ^ α i l =
        (Cp.D k).g ^ (N * (M - ∑ l, α i l)) * ∏ l, ((Cp.D k).g ^ N * a l) ^ α i l := by
      intro i
      simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
      rw [← mul_assoc, ← pow_add, ← Finset.mul_sum, ← mul_add, Nat.sub_add_cancel (hMi i)]
    have hA : (Cp.D k).g ^ (S + N * M) * z = ∑ i, b i * (Cp.D k).g ^ (N * (M - ∑ l, α i l)) *
        ∏ l, ((Cp.D k).g ^ N * a l) ^ α i l := by
      rw [pow_add, mul_comm ((Cp.D k).g ^ S), mul_assoc, hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm, hmon i]; ring
    rw [hA, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [prod_C_mul_T_pow, map_mul, map_mul]
    have hT : (T j : A[T;T⁻¹]) = T (-(((((∑ l, α i l * w l : ℕ) : ℤ) - j).toNat : ℕ) : ℤ)) *
        T ((∑ l, α i l * w l : ℕ) : ℤ) := by
      rw [← T_add]; congr 1; have := hle i; omega
    rw [hT]; ring

end BezoutCounterexample.Principalization
