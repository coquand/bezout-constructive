import BezoutCounterexample.Principalization.QuotSeq
import BezoutCounterexample.Principalization.XiMinPos
import BezoutCounterexample.Constructive.CompList

/-!
# Method 1's step data, positively (Task D, R6; roadmap §1.2, §1.6)

`MC.SA.step_data_Q` minimises `Ξ` over the classical set
`S = {β | ∃ g ∈ I, coeff_β(τ g) ≠ 0, λ(β) < 1}`: nonemptiness by `by_contra` and (F2) through
`QuotSeqCond`, the minimum by `Nat.find` (`exists_min_Xi`). Here:

* the residue field is **decided** (`hdec : x ∈ 𝔪 ∨ IsUnit x`; at an explicit point `z`:
  `z(x) = 0` or not, in `L`), so `coeff_β(τ f) = 0` is decided (`Chart.coeff_tau_dec`);
* `I = (l)` is explicit, and the candidate set is reduced to the generators:
  `coeff_β(τ g) ≠ 0` for `g ∈ (l)` gives a generator `f` and `γ ≤ β` with `coeff_γ(τ f) ≠ 0`
  (`Chart.exists_gen_coeff_ne_zero`), and `Ξ(γ) ≤ Ξ(β)`, `λ(γ) ≤ λ(β)` (`Xi_le_of_le`);
* the first candidate `β₀` is an input (from (F2⁺): `pos_F2` on `(x_{<j})`), replacing
  `¬ J.Adm I`, which follows from it (`not_adm_of_witness`); `QuotSeqCond` is not used;
* the minimiser is `exists_min_Xi_pos` (bounded search).

`SA.step_data_pos` has the conclusion of `step_data_Q`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing BezoutCounterexample.Constructive

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] {n : ℕ}

/-! ### Monotonicity of `λ`, `tail` and `Ξ` -/

lemma lam_le_of_le {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) {γ β : Fin n →₀ ℕ} (h : γ ≤ β) :
    lam e γ ≤ lam e β :=
  Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast h i) (he i)

lemma tailSum_le_of_le {j : ℕ} {γ β : Fin n →₀ ℕ} (h : γ ≤ β) : tailSum j γ ≤ tailSum j β :=
  Finset.sum_le_sum fun i _ => h i

lemma Xi_le_of_le {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) (j : ℕ) {γ β : Fin n →₀ ℕ} (h : γ ≤ β)
    (hβ : lam e β < 1) : Xi e j γ ≤ Xi e j β := by
  have hl := lam_le_of_le he h
  have ht : (tailSum j γ : ℚ) ≤ tailSum j β := by exact_mod_cast tailSum_le_of_le h
  have h1 : 0 < 1 - lam e β := by linarith
  have h2 : 1 - lam e β ≤ 1 - lam e γ := by linarith
  rw [Xi, Xi]
  calc (tailSum j γ : ℚ) / (1 - lam e γ) ≤ tailSum j γ / (1 - lam e β) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) h1 h2
    _ ≤ tailSum j β / (1 - lam e β) := div_le_div_of_nonneg_right ht h1.le

/-! ### Decided coefficients and the reduction to generators -/

/-- A sum of decided terms which is nonzero has a nonzero term. -/
lemma exists_ne_zero_of_sum_ne_zero {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (f : ι → M) (hd : ∀ i, f i = 0 ∨ f i ≠ 0) :
    ∀ s : Finset ι, ∑ i ∈ s, f i ≠ 0 → ∃ i ∈ s, f i ≠ 0 := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro h; exact absurd Finset.sum_empty h
  | insert a s ha ih =>
    intro h
    rcases hd a with h0 | h0
    · rw [Finset.sum_insert ha, h0, zero_add] at h
      obtain ⟨i, hi, hfi⟩ := ih h
      exact ⟨i, Finset.mem_insert_of_mem hi, hfi⟩
    · exact ⟨a, Finset.mem_insert_self a s, h0⟩

namespace Chart

variable (c : Chart R n) (hdec : ∀ x : R, x ∈ maximalIdeal R ∨ IsUnit x)
include hdec

lemma coeff_tau_dec (β : Fin n →₀ ℕ) (f : R) :
    coeff β (c.tau f) = 0 ∨ coeff β (c.tau f) ≠ 0 := by
  rcases hdec (c.Dv β f) with h | h
  · exact Or.inl ((c.coeff_tau_eq_zero_iff f β).2 h)
  · exact Or.inr fun h0 => (mem_maximalIdeal _).1 ((c.coeff_tau_eq_zero_iff f β).1 h0) h

/-- **Reduction to the generators**: a nonzero coefficient of `τ g`, `g ∈ (l)`, sits above a
nonzero coefficient of some `τ f`, `f ∈ l`. -/
lemma exists_gen_coeff_ne_zero (l : List R) {g : R} (hg : g ∈ lspan l) :
    ∀ β : Fin n →₀ ℕ, coeff β (c.tau g) ≠ 0 →
      ∃ f ∈ l, ∃ γ ≤ β, coeff γ (c.tau f) ≠ 0 := by
  rw [lspan] at hg
  refine Submodule.span_induction (p := fun g _ => ∀ β : Fin n →₀ ℕ, coeff β (c.tau g) ≠ 0 →
      ∃ f ∈ l, ∃ γ ≤ β, coeff γ (c.tau f) ≠ 0) ?_ ?_ ?_ ?_ hg
  · intro f hf β hβ
    exact ⟨f, hf, β, le_rfl, hβ⟩
  · intro β hβ
    rw [map_zero, map_zero] at hβ
    exact absurd rfl hβ
  · intro a b _ _ ha hb β hβ
    rcases c.coeff_tau_dec hdec β a with h0 | h0
    · refine hb β fun hb0 => hβ ?_
      rw [map_add, map_add, h0, hb0, add_zero]
    · exact ha β h0
  · intro r a _ ha β hβ
    rw [smul_eq_mul, map_mul, coeff_mul] at hβ
    have hd : ∀ p : (Fin n →₀ ℕ) × (Fin n →₀ ℕ),
        coeff p.1 (c.tau r) * coeff p.2 (c.tau a) = 0 ∨
          coeff p.1 (c.tau r) * coeff p.2 (c.tau a) ≠ 0 := fun p => by
      rcases c.coeff_tau_dec hdec p.1 r with h1 | h1
      · exact Or.inl (by rw [h1, zero_mul])
      · rcases c.coeff_tau_dec hdec p.2 a with h2 | h2
        · exact Or.inl (by rw [h2, mul_zero])
        · exact Or.inr (mul_ne_zero h1 h2)
    obtain ⟨p, hp, hpne⟩ := exists_ne_zero_of_sum_ne_zero _ hd _ hβ
    have h2 : coeff p.2 (c.tau a) ≠ 0 := fun h => hpne (by rw [h, mul_zero])
    obtain ⟨f, hf, γ, hγ, hγne⟩ := ha p.2 h2
    have hp' : p.2 ≤ β := by
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp]; exact le_add_self
    exact ⟨f, hf, γ, hγ.trans hp', hγne⟩

end Chart

/-! ### The step data -/

namespace MC

variable {I : Ideal R} {j : ℕ} {J : MC R n}

omit [Algebra ℚ R] [IsLocalRing R] in
lemma lam_lt_dec (e : Fin n → ℚ) (β : Fin n →₀ ℕ) : lam e β < 1 ∨ ¬ lam e β < 1 := by
  by_cases h : lam e β < 1
  · exact Or.inl h
  · exact Or.inr h

/-- A witness of non-admissibility. -/
lemma not_adm_of_witness {f : R} (hf : f ∈ I) {β₀ : Fin n →₀ ℕ}
    (hβ₀ : coeff β₀ (J.c.tau f) ≠ 0) (hlt : lam J.e β₀ < 1) : ¬ J.Adm I := fun ha =>
  hβ₀ (J.centred.coeff_tau_eq_zero_of_mem_RF J.nonneg (ha hf) β₀ hlt)

/-- **Data of the Method-1 step, positively**: from a decided residue field, generators of `I`
and a first candidate `β₀` (from (F2⁺)), with the conclusion of `step_data_Q`. -/
lemma SA.step_data_pos (hdec : ∀ x : R, x ∈ maximalIdeal R ∨ IsUnit x) (l : List R)
    (hl : I = lspan l) (hSA : SA I j J) {f₀ : R} (hf₀ : f₀ ∈ l) {β₀ : Fin n →₀ ℕ}
    (hβ₀ : coeff β₀ (J.c.tau f₀) ≠ 0) (hlt₀ : lam J.e β₀ < 1) :
    ∃ (hj : j < n) (βs : Fin n →₀ ℕ) (f : R), f ∈ I ∧ coeff βs (J.c.tau f) ≠ 0 ∧
      lam J.e βs < 1 ∧ 0 < tailSum j βs ∧
      (∀ β : Fin n →₀ ℕ, (∃ g ∈ I, coeff β (J.c.tau g) ≠ 0) → lam J.e β < 1 →
        Xi J.e j βs ≤ Xi J.e j β) ∧
      (∀ J' : MC R n, J'.Adm I → (∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i) →
        0 < J'.e ⟨j, hj⟩ ∧ (1 - lam J.e βs) / tailSum j βs ≤ J'.e ⟨j, hj⟩) ∧
      (∀ i : Fin n, (i : ℕ) < j → (1 - lam J.e βs) / tailSum j βs ≤ J.e i) := by
  have hmemI : ∀ f ∈ l, f ∈ I := fun f hf => hl ▸ Ideal.subset_span hf
  have hna : ¬ J.Adm I := not_adm_of_witness (hmemI f₀ hf₀) hβ₀ hlt₀
  obtain ⟨J₀, hJ₀, hag₀⟩ := hSA.dom0
  obtain ⟨hj, hb₀⟩ := hSA.next_pos hna J₀ hJ₀ hag₀
  have hzero : ∀ i : Fin n, j ≤ (i : ℕ) → J.e i = 0 := fun i hi => hSA.e_eq_zero hi
  -- the decided candidate set of the generators
  set S : Set (Fin n →₀ ℕ) := {β | (∃ f ∈ l, coeff β (J.c.tau f) ≠ 0) ∧ lam J.e β < 1}
    with hSdef
  have hSdec : ∀ β, β ∈ S ∨ β ∉ S := fun β => by
    rcases list_exists_or_forall (P := fun f => coeff β (J.c.tau f) ≠ 0)
      (fun f => (J.c.coeff_tau_dec hdec β f).elim (fun h => Or.inr fun h' => h' h) Or.inl) l
      with hex | hall
    · rcases lam_lt_dec J.e β with h | h
      · exact Or.inl ⟨hex, h⟩
      · exact Or.inr fun hS => h hS.2
    · exact Or.inr fun hS => by
        obtain ⟨f, hf, hne⟩ := hS.1
        exact hall f hf hne
  have hpos : ∀ i : Fin n, (i : ℕ) < j → 0 < J.e i := fun i hi => hSA.e_pos hi
  obtain ⟨βs, hβs, hminS⟩ := exists_min_Xi_pos J.nonneg hpos S hSdec
    (β₀ := β₀) ⟨⟨f₀, hf₀, hβ₀⟩, hlt₀⟩ (fun β hβ => hβ.2)
  -- minimality over all of `I`
  have hmin : ∀ β : Fin n →₀ ℕ, (∃ g ∈ I, coeff β (J.c.tau g) ≠ 0) → lam J.e β < 1 →
      Xi J.e j βs ≤ Xi J.e j β := by
    rintro β ⟨g, hg, hne⟩ hβ
    obtain ⟨f, hf, γ, hγ, hγne⟩ :=
      J.c.exists_gen_coeff_ne_zero hdec l (hl ▸ hg) β hne
    have hγlt : lam J.e γ < 1 := (lam_le_of_le J.nonneg hγ).trans_lt hβ
    exact (hminS γ ⟨⟨f, hf, hγne⟩, hγlt⟩).trans (Xi_le_of_le J.nonneg j hγ hβ)
  -- general bound from admissible completions
  have hbound : ∀ J' : MC R n, J'.Adm I → (∀ i : Fin n, (i : ℕ) < j → J'.e i = J.e i) →
      ∀ β : Fin n →₀ ℕ, (∃ g ∈ I, coeff β (J.c.tau g) ≠ 0) →
        1 ≤ lam J.e β + J'.e ⟨j, hj⟩ * tailSum j β := by
    intro J' hJ' hag β ⟨g, hg, hne⟩
    obtain ⟨hj', hb'⟩ := hSA.next_pos hna J' hJ' hag
    have hc := hSA.compl_adm J' hJ' hag hj hb'
    have hnn : ∀ i, 0 ≤ compl J.e j (J'.e ⟨j, hj⟩) i := fun i => by
      simp only [compl]; split_ifs
      · exact J.nonneg i
      · exact hb'.le
    have := fun hlt => J.centred.coeff_tau_eq_zero_of_mem_RF hnn (hc hg) β hlt
    rw [← lam_compl hzero]
    exact le_of_not_gt fun hlt => hne (this hlt)
  obtain ⟨⟨f, hf, hfne⟩, hlt⟩ := hβs
  have h1 := hbound J₀ hJ₀ hag₀ βs ⟨f, hmemI f hf, hfne⟩
  have hN : 0 < tailSum j βs := by
    rcases Nat.eq_zero_or_pos (tailSum j βs) with h0 | h0
    · rw [h0, Nat.cast_zero, mul_zero, add_zero] at h1; linarith
    · exact h0
  have hNq : (0 : ℚ) < tailSum j βs := by exact_mod_cast hN
  refine ⟨hj, βs, f, hmemI f hf, hfne, hlt, hN, hmin, ?_, ?_⟩
  · intro J' hJ' hag
    obtain ⟨hj', hb'⟩ := hSA.next_pos hna J' hJ' hag
    refine ⟨hb', ?_⟩
    have := hbound J' hJ' hag βs ⟨f, hmemI f hf, hfne⟩
    rw [div_le_iff₀ hNq]; linarith
  · intro i hi
    have hle : (1 - lam J.e βs) / tailSum j βs ≤ J₀.e ⟨j, hj⟩ := by
      rw [div_le_iff₀ hNq]; linarith
    refine hle.trans ?_
    rw [← hag₀ i hi]
    exact J₀.anti (Fin.le_def.2 (by simp only; omega))

end MC

end BezoutCounterexample.Principalization
