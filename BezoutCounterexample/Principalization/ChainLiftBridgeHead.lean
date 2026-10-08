import Mathlib
import BezoutCounterexample.Principalization.ChartCover
import BezoutCounterexample.Principalization.ComponentFilPt
import BezoutCounterexample.Principalization.ChainLiftBridgeRees
import BezoutCounterexample.Constructive.ChainLiftChoice

/-!
# The head identities of a chart, in `A` (bridge (e))

For a separated chart cover `C` of the component `V(𝔭)` and a chart `D = C.D k` on
`D(g) = Spec D.B`, with head numerators `aₕ` (`x_h gˢ = aₕ` in `D.B`):

* `global_of_RFB`: a membership `b ∈ RFB_k(t)` spreads to `g^N b ∈ F_t(𝔭)` (all charts, by
  `LocData.exists_pow_mul_mem`, then `mem_compF_iff_chart`);
* `lid_A`: `g^N aₕ ∈ RI (wₕ)`, i.e. `g^N aₕ = Σ_γ c_γ g^γ` with `γ·deg ≥ wₕ`, `γ ≠ 0`;
* `hid_A`: for `z ∈ F_t`, `g^S z = Σ_j b_j a^{α_j}` with `α_j` supported on the head and
  `t ≤ λ_e(α_j)`.
* `global_of_RFB_pt`, `lid_A_pt`, `hid_A_pt`: the same over a cover at explicit points
  (`ChartCoverPt`) and the filtration at points `compFPt` (D3.3d); `hid_B` is the chart form
  shared by `hid_A` and `hid_A_pt`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} {𝔭 : Ideal A}
  (hZ : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 → I ≤ 𝔪 ∧ InvAt I 𝔪 v₀)
  (C : ChartCover I v₀ 𝔭)

include hI hZ in
/-- **Spreading a chart membership to `F_t`**, up to a power of the chart element. -/
theorem global_of_RFB [Fact (Constructive.HasPres A)] (k : Fin C.n) {b : A} {t : ℚ}
    (hb : algebraMap A (C.D k).B b ∈ (C.D k).RFB t) :
    ∃ N : ℕ, (C.D k).g ^ N * b ∈ compF I 𝔭 t := by
  obtain ⟨N, hN⟩ := Constructive.finite_choice_dep fun k' => (C.D k).exists_pow_mul_mem hI (C.D k') b t hb
  refine ⟨∑ k', N k', ?_⟩
  rw [mem_compF_iff_chart hI hZ C t]
  intro k'
  have hle : N k' ≤ ∑ k'', N k'' :=
    Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k')
  have : (C.D k).g ^ (∑ k'', N k'') * b = (C.D k).g ^ (∑ k'', N k'' - N k') * ((C.D k).g ^ N k' * b) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  rw [this, map_mul]
  exact Ideal.mul_mem_left _ _ (hN k')

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- **Head numerators**: a common power `gˢ` clears the chart functions. -/
theorem exists_numerators {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) :
    ∃ (s : ℕ) (a : Fin D.n → A), ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s = algebraMap A D.B (a i) := by
  obtain ⟨⟨b, hb⟩, hint⟩ := exist_integer_multiples_of_finite (Submonoid.powers D.g) D.cB.x
  obtain ⟨s, rfl⟩ := hb
  obtain ⟨a, ha⟩ := Constructive.finite_choice_dep fun i => (hint i : ∃ a : A, _ = _)
  refine ⟨s, a, fun i => ?_⟩
  rw [ha i, Algebra.smul_def, map_pow, mul_comm]

include hI hZ in
/-- **lid in `A`**: `g^N aₕ ∈ F_{eₕ}` for a head numerator `aₕ`. -/
theorem lid_A [Fact (Constructive.HasPres A)] (k : Fin C.n) (s : ℕ) (a : Fin (C.D k).n → A)
    (ha : ∀ i, (C.D k).cB.x i * algebraMap A (C.D k).B (C.D k).g ^ s =
      algebraMap A (C.D k).B (a i)) (h : Fin (C.D k).n) (hne : (C.D k).ek h ≠ 0) :
    ∃ N : ℕ, (C.D k).g ^ N * a h ∈ compF I 𝔭 ((C.D k).ek h) := by
  apply global_of_RFB hI hZ C k
  rw [← ha h]
  exact Ideal.mul_mem_right _ _ ((C.D k).cB.x_mem_RF (C.D k).ek h hne)

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- **hid in a chart**: a chart-ideal membership of `z`, up to a power of `g`, is a combination of
head monomials of weighted degree `≥ t`. -/
theorem hid_B {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) (s : ℕ) (a : Fin D.n → A)
    (ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s = algebraMap A D.B (a i)) {t : ℚ} {z : A}
    (hzB : algebraMap A D.B z ∈ D.RFB t) :
    ∃ (S K : ℕ) (b : Fin K → A) (α : Fin K → (Fin D.n →₀ ℕ)),
      (∀ j l, D.ek l = 0 → α j l = 0) ∧ (∀ j, t ≤ lam D.ek (α j)) ∧
      D.g ^ S * z = ∑ j, b j * ∏ l, a l ^ α j l := by
  rw [LocData.RFB, Chart.RF, Submodule.mem_span_set'] at hzB
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


include hI hZ in
/-- **hid in `A`**: an element of `F_t` is, up to a power of `g`, a combination of head monomials
of weighted degree `≥ t`. -/
theorem hid_A [Fact (Constructive.HasPres A)] (k : Fin C.n) (s : ℕ) (a : Fin (C.D k).n → A)
    (ha : ∀ i, (C.D k).cB.x i * algebraMap A (C.D k).B (C.D k).g ^ s =
      algebraMap A (C.D k).B (a i)) {t : ℚ} {z : A} (hz : z ∈ compF I 𝔭 t) :
    ∃ (S K : ℕ) (b : Fin K → A) (α : Fin K → (Fin (C.D k).n →₀ ℕ)),
      (∀ j l, (C.D k).ek l = 0 → α j l = 0) ∧ (∀ j, t ≤ lam (C.D k).ek (α j)) ∧
      (C.D k).g ^ S * z = ∑ j, b j * ∏ l, a l ^ α j l :=
  hid_B (C.D k) s a ha ((mem_compF_iff_chart hI hZ C t z).1 hz k)

section Pt

variable (hZp : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀)
  (Cp : ChartCoverPt I v₀ 𝔭)

include hI hZp in
/-- **Spreading a chart membership to `F_t` at points**, up to a power of the chart element. -/
theorem global_of_RFB_pt [Fact (Constructive.HasPres A)] (k : Fin Cp.n) {b : A} {t : ℚ}
    (hb : algebraMap A (Cp.D k).B b ∈ (Cp.D k).RFB t) :
    ∃ N : ℕ, (Cp.D k).g ^ N * b ∈ compFPt I 𝔭 t := by
  obtain ⟨N, hN⟩ := exists_uniform_list
    (P := fun j m => algebraMap A (Cp.D j).B ((Cp.D k).g ^ m * b) ∈ (Cp.D j).RFB t)
    (fun j m n hmn hm => by
      rw [← Nat.sub_add_cancel hmn, pow_add, mul_assoc, map_mul]
      exact Ideal.mul_mem_left _ _ hm)
    (List.finRange Cp.n) fun j _ => (Cp.D k).exists_pow_mul_mem_pt hI (Cp.D j) b t hb
  exact ⟨N, (Cp.mem_compFPt_iff hI hZp t _).2 fun j => hN j (List.mem_finRange j)⟩

include hI hZp in
/-- **lid in `A`, at points**: `g^N aₕ ∈ F_{eₕ}` for a head numerator `aₕ`. -/
theorem lid_A_pt [Fact (Constructive.HasPres A)] (k : Fin Cp.n) (s : ℕ) (a : Fin (Cp.D k).n → A)
    (ha : ∀ i, (Cp.D k).cB.x i * algebraMap A (Cp.D k).B (Cp.D k).g ^ s =
      algebraMap A (Cp.D k).B (a i)) (h : Fin (Cp.D k).n) (hne : (Cp.D k).ek h ≠ 0) :
    ∃ N : ℕ, (Cp.D k).g ^ N * a h ∈ compFPt I 𝔭 ((Cp.D k).ek h) := by
  apply global_of_RFB_pt hI hZp Cp k
  rw [← ha h]
  exact Ideal.mul_mem_right _ _ ((Cp.D k).cB.x_mem_RF (Cp.D k).ek h hne)

include hI hZp in
/-- **hid in `A`, at points**: an element of `F_t` is, up to a power of `g`, a combination of head
monomials of weighted degree `≥ t`. -/
theorem hid_A_pt [Fact (Constructive.HasPres A)] (k : Fin Cp.n) (s : ℕ) (a : Fin (Cp.D k).n → A)
    (ha : ∀ i, (Cp.D k).cB.x i * algebraMap A (Cp.D k).B (Cp.D k).g ^ s =
      algebraMap A (Cp.D k).B (a i)) {t : ℚ} {z : A} (hz : z ∈ compFPt I 𝔭 t) :
    ∃ (S K : ℕ) (b : Fin K → A) (α : Fin K → (Fin (Cp.D k).n →₀ ℕ)),
      (∀ j l, (Cp.D k).ek l = 0 → α j l = 0) ∧ (∀ j, t ≤ lam (Cp.D k).ek (α j)) ∧
      (Cp.D k).g ^ S * z = ∑ j, b j * ∏ l, a l ^ α j l :=
  hid_B (Cp.D k) s a ha ((Cp.mem_compFPt_iff hI hZp t z).1 hz k)

end Pt

end BezoutCounterexample.Principalization
