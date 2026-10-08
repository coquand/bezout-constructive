import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesRows
import BezoutCounterexample.Principalization.LocDataPt

/-!
# L1/L2 and the rows on one `LocDataPt` chart (Task B, Rees layer S6; agnostic in the cover)

The same statements as `ChainLiftReesLocal`/`ChainLiftReesRows`, for one chart `D : LocDataPt`
(coll-7c, D3.4) instead of a chart of a `ChartCoverPt`. The cover enters only through two
hypotheses about that chart, both consequences of any point cover of `V(𝔭)`
(`global_of_RFB_pt` and `mem_compFPt_iff` today):

* `hglob`: chart membership `b ∈ RF_t` on `D(g)` gives `gᴺ b ∈ 𝓕_t` globally;
* `hloc`: `z ∈ 𝓕_t` gives `z ∈ RF_t` on `D(g)`.

`hid_B_pt` is `hid_B` (BridgeHead) for `LocDataPt`; it uses only the data of the chart.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive IsLocalization
open LaurentPolynomial hiding C

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal]

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- **hid in a chart** (`LocDataPt`). -/
theorem hid_B_pt (D : LocDataPt I v₀ 𝔪) (s : ℕ) (a : Fin D.n → A)
    (ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s = algebraMap A D.B (a i)) {t : ℚ} {z : A}
    (hzB : algebraMap A D.B z ∈ D.RFB t) :
    ∃ (S K : ℕ) (b : Fin K → A) (α : Fin K → (Fin D.n →₀ ℕ)),
      (∀ j l, D.ek l = 0 → α j l = 0) ∧ (∀ j, t ≤ lam D.ek (α j)) ∧
      D.g ^ S * z = ∑ j, b j * ∏ l, a l ^ α j l := by
  rw [LocDataPt.RFB, Chart.RF, Submodule.mem_span_set'] at hzB
  obtain ⟨K, f, gg, hfg⟩ := hzB
  obtain ⟨α, hα⟩ := Constructive.finite_choice_dep fun j => (gg j).2
  have hα0 := fun j => (hα j).1
  have hαt := fun j => (hα j).2.1
  have hαx := fun j => (hα j).2.2
  -- `x^α g^{s|α|} = a^α`
  set M := ∑ j, ∑ l, α j l
  have hmon : ∀ j, (∏ l, D.cB.x l ^ α j l) * algebraMap A D.B D.g ^ (s * ∑ l, α j l) =
      algebraMap A D.B (∏ l, a l ^ α j l) := by
    intro j
    rw [map_prod, pow_mul, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← mul_pow, ha l, map_pow]
  -- clear the coefficients
  obtain ⟨⟨c₀, hc₀⟩, hint⟩ := exist_integer_multiples_of_finite (Submonoid.powers D.g) f
  obtain ⟨s', rfl⟩ := hc₀
  obtain ⟨b, hb⟩ := Constructive.finite_choice_dep fun j => (hint j : ∃ a : A, _ = _)
  have hMj : ∀ j, ∑ l, α j l ≤ M := fun j =>
    Finset.single_le_sum (f := fun j => ∑ l, α j l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hB : algebraMap A D.B (D.g ^ (s * M + s') * z) = algebraMap A D.B
      (∑ j, b j * D.g ^ (s * (M - ∑ l, α j l)) * ∏ l, a l ^ α j l) := by
    rw [map_mul, ← hfg, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hbj : algebraMap A D.B (b j) = algebraMap A D.B D.g ^ s' * f j := by
      rw [hb j, Algebra.smul_def]; simp
    rw [map_mul, map_mul, ← hmon j, hbj, hαx j, smul_eq_mul, map_pow, map_pow]
    have : s * M + s' = s * (M - ∑ l, α j l) + s * ∑ l, α j l + s' := by
      rw [← mul_add, Nat.sub_add_cancel (hMj j)]
    rw [this, pow_add, pow_add]
    ring
  obtain ⟨⟨c₁, hc₁⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers D.g) D.B).1 hB
  obtain ⟨s'', rfl⟩ := hc₁
  refine ⟨s'' + (s * M + s'), K, fun j => D.g ^ s'' * (b j * D.g ^ (s * (M - ∑ l, α j l))),
    α, hα0, hαt, ?_⟩
  rw [pow_add, mul_assoc, hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

variable [IsNoetherianRing A] {𝔭 : Ideal A} (D : LocDataPt I v₀ 𝔪)
  (hglob : ∀ (b : A) (t : ℚ), algebraMap A D.B b ∈ D.RFB t → ∃ N : ℕ, D.g ^ N * b ∈ compFPt I 𝔭 t)
  (hloc : ∀ (t : ℚ) (z : A), z ∈ compFPt I 𝔭 t → algebraMap A D.B z ∈ D.RFB t)
  (Φ : WFil A) {d : ℕ} (hΦ : ∀ j : ℤ, Φ.F j = compFPt I 𝔭 ((j : ℚ) / d)) (hd : 0 < d)

include hglob hΦ hd in
/-- **L1**: one power of the chart element puts every `C(aₗ) T^{wₗ}` into the Rees algebra. -/
theorem exists_heads_rees_pt (s : ℕ)
    (a : Fin D.n → A)
    (ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s =
      algebraMap A D.B (a i))
    (w : Fin D.n → ℕ) (hw : ∀ l, (w l : ℚ) = d * D.ek l) :
    ∃ N : ℕ, ∀ l, LaurentPolynomial.C (D.g ^ N * a l) * T (w l : ℤ) ∈ ReesAlg Φ := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  obtain ⟨N, hN⟩ := exists_uniform_list
    (P := fun l N => LaurentPolynomial.C (D.g ^ N * a l) * T (w l : ℤ) ∈ ReesAlg Φ)
    (fun l m n hmn hm => by
      rw [← Nat.sub_add_cancel hmn, pow_add, mul_assoc, map_mul, mul_assoc]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hm)
    (List.finRange D.n) fun l _ => by
      by_cases hl : D.ek l = 0
      · refine ⟨0, ?_⟩
        have hwl : w l = 0 := by have := hw l; rw [hl, mul_zero] at this; exact_mod_cast this
        rw [hwl, Nat.cast_zero, T_zero, mul_one]
        exact Subalgebra.algebraMap_mem _ _
      · obtain ⟨N, hN⟩ := hglob _ _ (by rw [← ha l]; exact Ideal.mul_mem_right _ _ (D.cB.x_mem_RF D.ek l hl))
        refine ⟨N, C_mul_T_mem_ReesAlg ?_⟩
        rw [hΦ, Int.cast_natCast, hw l, mul_div_cancel_left₀ _ hdq]
        exact hN
  exact ⟨N, fun l => hN l (List.mem_finRange l)⟩

include hloc hΦ hd in
/-- **L2**: an element of `F_j`, times a power of the chart element, is a polynomial in
`s = T⁻¹` and the `uₗ = C(gᴺ aₗ) T^{wₗ}` (any `N`), with coefficients in `A`. -/
theorem exists_rees_expansion_pt (s : ℕ)
    (a : Fin D.n → A)
    (ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s =
      algebraMap A D.B (a i))
    (w : Fin D.n → ℕ) (hw : ∀ l, (w l : ℚ) = d * D.ek l) (N : ℕ)
    {j : ℤ} {z : A} (hz : z ∈ Φ.F j) :
    ∃ (S K : ℕ) (b : Fin K → A) (α : Fin K → (Fin D.n →₀ ℕ)) (e : Fin K → ℕ),
      (∀ i l, D.ek l = 0 → α i l = 0) ∧
      (∀ i, (e i : ℤ) + j = ((∑ l, α i l * w l : ℕ) : ℤ)) ∧
      LaurentPolynomial.C (D.g ^ S * z) * T j =
        ∑ i, LaurentPolynomial.C (b i) * T (-(e i : ℤ)) *
          ∏ l, (LaurentPolynomial.C (D.g ^ N * a l) * T (w l : ℤ)) ^ α i l := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  rw [hΦ] at hz
  obtain ⟨S, K, b, α, hα0, hαt, hS⟩ := hid_B_pt D s a ha (hloc _ _ hz)
  -- the weight inequality in `ℤ`
  have hle : ∀ i, j ≤ ((∑ l, α i l * w l : ℕ) : ℤ) := by
    intro i
    have h := hαt i
    rw [lam, div_le_iff₀ hdq] at h
    have : ((∑ l, α i l * w l : ℕ) : ℚ) = (∑ l, (α i l : ℚ) * D.ek l) * d := by
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hw l]; ring
    exact_mod_cast (show (j : ℚ) ≤ ((∑ l, α i l * w l : ℕ) : ℚ) by rw [this]; exact h)
  set M := ∑ i, ∑ l, α i l
  have hMi : ∀ i, ∑ l, α i l ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => ∑ l, α i l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨S + N * M, K, fun i => b i * D.g ^ (N * (M - ∑ l, α i l)), α,
    fun i => (((∑ l, α i l * w l : ℕ) : ℤ) - j).toNat, hα0, fun i => ?_, ?_⟩
  · dsimp only
    have := hle i
    omega
  · -- `gᴺᴹ ∏ aₗ^{αₗ} = g^{N(M − |α|)} ∏ (gᴺ aₗ)^{αₗ}`
    have hmon : ∀ i, D.g ^ (N * M) * ∏ l, a l ^ α i l =
        D.g ^ (N * (M - ∑ l, α i l)) * ∏ l, (D.g ^ N * a l) ^ α i l := by
      intro i
      simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
      rw [← mul_assoc, ← pow_add, ← Finset.mul_sum, ← mul_add, Nat.sub_add_cancel (hMi i)]
    have hA : D.g ^ (S + N * M) * z = ∑ i, b i * D.g ^ (N * (M - ∑ l, α i l)) *
        ∏ l, (D.g ^ N * a l) ^ α i l := by
      rw [pow_add, mul_comm (D.g ^ S), mul_assoc, hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm, hmon i]; ring
    rw [hA, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [prod_C_mul_T_pow, map_mul, map_mul]
    have hT : (T j : A[T;T⁻¹]) = T (-(((((∑ l, α i l * w l : ℕ) : ℤ) - j).toNat : ℕ) : ℤ)) *
        T ((∑ l, α i l * w l : ℕ) : ℤ) := by
      rw [← T_add]; congr 1; have := hle i; omega
    rw [hT]; ring


variable {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ)) (e : SmoothCert.QB G ≃+* A)
  {r : ℕ} (gZ : Fin r → MvPolynomial (Fin (m + n)) ℤ) (δ : Fin r → ℕ)
  (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
  (hgF : ∀ i, toAq G e (toQZ (gZ i)) ∈ Φ.F (δ i))
  (hgen : ∀ (j : ℤ) (f : A), f ∈ Φ.F j →
    LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (insert (T (-1)) (Set.range (reesYL G e gZ δ))))

include hglob hΦ hd hneg hgF hgen in
/-- **L1 through the presentation**: a lift of `gᴺ` and preimages of the `uₗ = C(gᴺ aₗ) T^{wₗ}`. -/
theorem exists_heads_poly_pt (s : ℕ) (a : Fin D.n → A)
    (ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s =
      algebraMap A D.B (a i))
    (w : Fin D.n → ℕ) (hw : ∀ l, (w l : ℚ) = d * D.ek l) :
    ∃ (N : ℕ) (pγ : MvPolynomial (Fin (m + n)) ℚ)
      (P : Fin D.n → MvPolynomial (Fin ((m + n) + (1 + r))) ℚ),
      toAq G e pγ = D.g ^ N ∧
      ∀ l, aeval (reesVec G e gZ δ) (P l) = LaurentPolynomial.C (D.g ^ N * a l) * T (w l : ℤ) := by
  obtain ⟨N, hN⟩ := exists_heads_rees_pt D hglob Φ hΦ hd s a ha w hw
  obtain ⟨pγ, hpγ⟩ := toAq_surjective G e (D.g ^ N)
  obtain ⟨P, hP⟩ := Constructive.finite_choice_dep fun l =>
    reesAlg_le_range G e gZ δ Φ hneg hgF hgen (hN l)
  exact ⟨N, pγ, P, hpγ, hP⟩

include hloc hΦ hd hgF in
/-- **L2 through the presentation**: the `y`-row of a generator, with lifts of the coefficients. -/
theorem exists_yrow_poly_pt (s : ℕ) (a : Fin D.n → A)
    (ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s =
      algebraMap A D.B (a i))
    (w : Fin D.n → ℕ) (hw : ∀ l, (w l : ℚ) = d * D.ek l) (N : ℕ) (j : Fin r) :
    ∃ (S K : ℕ) (pβ : MvPolynomial (Fin (m + n)) ℚ) (pb : Fin K → MvPolynomial (Fin (m + n)) ℚ)
      (α : Fin K → (Fin D.n →₀ ℕ)) (ex : Fin K → ℕ),
      toAq G e pβ = D.g ^ S ∧
      (∀ i l, D.ek l = 0 → α i l = 0) ∧
      (∀ i, (ex i : ℤ) + δ j = ((∑ l, α i l * w l : ℕ) : ℤ)) ∧
      LaurentPolynomial.C (toAq G e pβ) * reesYL G e gZ δ j =
        ∑ i, LaurentPolynomial.C (toAq G e (pb i)) * T (-(ex i : ℤ)) *
          ∏ l, (LaurentPolynomial.C (D.g ^ N * a l) * T (w l : ℤ)) ^ α i l := by
  obtain ⟨S, K, b, α, ex, hα0, hex, hS⟩ :=
    exists_rees_expansion_pt D hloc Φ hΦ hd s a ha w hw N (hgF j)
  obtain ⟨pβ, hpβ⟩ := toAq_surjective G e (D.g ^ S)
  obtain ⟨pb, hpb⟩ := Constructive.finite_choice_dep fun i => toAq_surjective G e (b i)
  refine ⟨S, K, pβ, pb, α, ex, hpβ, hα0, hex, ?_⟩
  rw [hpβ, reesYL, ← mul_assoc, ← map_mul, hS]
  simp only [hpb]

end BezoutCounterexample.Principalization
