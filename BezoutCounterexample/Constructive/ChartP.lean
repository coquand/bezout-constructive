import BezoutCounterexample.Principalization.Duality
import BezoutCounterexample.Constructive.DualityP

/-!
# `𝔭`-adic duality for HM charts

Transfer of `PChart.mem_F_iff` to the charts `Chart R n` of `Principalization/Chart.lean` and their
weighted ideals `Chart.F w t`, for arbitrary weights `w : Fin n → ℕ` (zero weights allowed):

  `g ∈ F_t(w)  ↔  ∂^β g ∈ (xᵢ : wᵢ ≠ 0)` for all `β` supported on `{wᵢ ≠ 0}` with `w · β < t`.

No locality, no Noetherian hypothesis, no Taylor map: this is the Krull-free half of
`Chart.IsCentred.mem_F_iff`. The coordinates with nonzero weight (the *head*) are enumerated
explicitly (`exists_enum`, by filtering `List.finRange n`), and form a `PChart` (`subP`).
-/

namespace BezoutCounterexample.Constructive

open BezoutCounterexample.Principalization

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n k : ℕ}

/-- An explicit injective enumeration of a decidable set of indices. -/
lemma exists_enum (p : Fin n → Prop) [DecidablePred p] :
    ∃ (k : ℕ) (ι : Fin k → Fin n), Function.Injective ι ∧ ∀ i, p i ↔ ∃ a, ι a = i := by
  let L := (List.finRange n).filter (fun i => decide (p i))
  refine ⟨L.length, L.get, List.nodup_iff_injective_get.1 ((List.nodup_finRange n).filter _),
    fun i => ?_⟩
  rw [← List.mem_iff_get]
  simp [L, List.mem_filter]

/-- The sub-chart of an HM chart on the coordinates `ι a`. -/
def subP (c : Chart R n) (ι : Fin k → Fin n) (hι : Function.Injective ι) : PChart R k where
  x a := c.x (ι a)
  d a := c.d (ι a)
  dual a b := by
    rw [c.d_x]
    by_cases h : a = b
    · subst h; simp
    · have h' : ι a ≠ ι b := fun e => h (hι e)
      simp [h, h']

/-- The multi-index of a list of sub-chart indices, in the coordinates of `c`. -/
noncomputable def lsum (ι : Fin k → Fin n) (l : List (Fin k)) : Fin n →₀ ℕ :=
  (l.map fun a => Finsupp.single (ι a) 1).sum

lemma lsum_nil (ι : Fin k → Fin n) : lsum ι [] = 0 := by simp [lsum]

lemma lsum_cons (ι : Fin k → Fin n) (a : Fin k) (l : List (Fin k)) :
    lsum ι (a :: l) = Finsupp.single (ι a) 1 + lsum ι l := by simp [lsum]

lemma lsum_apply (ι : Fin k → Fin n) (hι : Function.Injective ι) (l : List (Fin k)) (b : Fin k) :
    lsum ι l (ι b) = PChart.cnt l b := by
  induction l with
  | nil => simp [lsum_nil, PChart.cnt]
  | cons a l ih =>
    rw [lsum_cons, Finsupp.add_apply, ih, PChart.cnt_cons, Pi.add_apply, Finsupp.single_apply,
      unit]
    by_cases h : a = b
    · subst h; simp [add_comm]
    · have h' : ι a ≠ ι b := fun e => h (hι e)
      simp [h', Ne.symm h]

lemma lsum_apply_off (ι : Fin k → Fin n) (l : List (Fin k)) {i : Fin n} (hi : ∀ a, ι a ≠ i) :
    lsum ι l i = 0 := by
  induction l with
  | nil => simp [lsum_nil]
  | cons a l ih => simp [lsum_cons, ih, hi a]

lemma weight_lsum (w : Fin n → ℕ) (ι : Fin k → Fin n) (l : List (Fin k)) :
    Finsupp.weight w (lsum ι l) = wt (fun a => w (ι a)) (PChart.cnt l) := by
  induction l with
  | nil => simp [lsum_nil, wt, PChart.cnt]
  | cons a l ih =>
    rw [lsum_cons, map_add, ih, PChart.cnt_cons, PChart.wt_add, PChart.wt_unit,
      Finsupp.weight_single, one_smul, add_comm]

variable (c : Chart R n) {ι : Fin k → Fin n} (hι : Function.Injective ι)

lemma Dl_subP (l : List (Fin k)) (f : R) : (subP c ι hι).Dl l f = c.D (lsum ι l) f := by
  induction l with
  | nil => rw [lsum_nil, c.D_zero]; rfl
  | cons a l ih =>
    rw [lsum_cons, add_comm, c.D_add_single, ← ih]; rfl

/-! ## The head of a weight vector -/

variable {w : Fin n → ℕ} (hrange : ∀ i, w i ≠ 0 ↔ ∃ a, ι a = i)
include hι hrange

omit [Algebra ℚ R] hι in
lemma w_eq_zero_of_off {i : Fin n} (hi : ∀ a, ι a ≠ i) : w i = 0 := by
  rcases Nat.eq_zero_or_pos (w i) with h | h
  · exact h
  · obtain ⟨a, ha⟩ := (hrange i).1 (Nat.pos_iff_ne_zero.1 h)
    exact absurd ha (hi a)

omit [Algebra ℚ R] in
lemma weight_eq_wt (α : Fin n →₀ ℕ) :
    Finsupp.weight w α = wt (fun a => w (ι a)) (fun a => α (ι a)) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℕ (w i)), wt]
  refine (Fintype.sum_of_injective ι hι _ _ (fun i hi => ?_) (fun a => ?_)).symm
  · rw [w_eq_zero_of_off hrange (fun a ha => hi ⟨a, ha⟩), smul_zero]
  · rw [smul_eq_mul, mul_comm]

/-- Head-supported multi-indices come from lists. -/
lemma eq_lsum_ofIdx {β : Fin n →₀ ℕ} (hβ : ∀ i, w i = 0 → β i = 0) :
    β = lsum ι (PChart.ofIdx fun a => β (ι a)) := by
  ext i
  rcases Nat.eq_zero_or_pos (w i) with h | h
  · rw [hβ i h, lsum_apply_off ι _ (fun a ha => (hrange i).2 ⟨a, ha⟩ h)]
  · obtain ⟨a, rfl⟩ := (hrange i).1 (Nat.pos_iff_ne_zero.1 h)
    rw [lsum_apply ι hι, PChart.cnt_ofIdx]

omit hι in
lemma lsum_supp (l : List (Fin k)) (i : Fin n) (hi : w i = 0) : lsum ι l i = 0 :=
  lsum_apply_off ι l fun a ha => (hrange i).2 ⟨a, ha⟩ hi

/-- Head-supported monomials are monomials of the sub-chart. -/
lemma prod_eq_mono {α : Fin n →₀ ℕ} (hα : ∀ i, w i = 0 → α i = 0) :
    ∏ i, c.x i ^ α i = (subP c ι hι).mono (fun a => α (ι a)) := by
  rw [PChart.mono]
  refine (Fintype.prod_of_injective ι hι _ _ (fun i hi => ?_) (fun a => rfl)).symm
  rw [hα i (w_eq_zero_of_off hrange (fun a ha => hi ⟨a, ha⟩)), pow_zero]

lemma F_eq_subP (t : ℕ) : c.F w t = (subP c ι hι).F (fun a => w (ι a)) t := by
  apply le_antisymm
  · rw [Chart.F, Ideal.span_le]
    rintro _ ⟨α, hα, ht, rfl⟩
    rw [prod_eq_mono c hι hrange hα]
    exact (subP c ι hι).mono_mem_F (by rw [← weight_eq_wt hι hrange]; exact ht)
  · rw [PChart.F, Ideal.span_le]
    rintro _ ⟨β', ht, rfl⟩
    have hsupp := lsum_supp hrange (ι := ι) (PChart.ofIdx β')
    have hβ' : (fun a => lsum ι (PChart.ofIdx β') (ι a)) = β' := by
      funext a; rw [lsum_apply ι hι, PChart.cnt_ofIdx]
    refine Ideal.subset_span ⟨lsum ι (PChart.ofIdx β'), hsupp, ?_, ?_⟩
    · rw [weight_lsum, PChart.cnt_ofIdx]; exact ht
    · rw [prod_eq_mono c hι hrange hsupp, hβ']

lemma P_eq_subP : Ideal.span (c.x '' {i | w i ≠ 0}) = (subP c ι hι).P := by
  rw [PChart.P]
  congr 1
  ext f
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨a, rfl⟩ := (hrange i).1 hi
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨ι a, (hrange (ι a)).2 ⟨a, rfl⟩, rfl⟩

omit hι hrange

/-- **`𝔭`-adic duality for HM charts.** Membership in `F_t(w)` is tested by head derivatives
modulo the head ideal `(xᵢ : wᵢ ≠ 0)`. -/
theorem mem_F_iff_P (w : Fin n → ℕ) (t : ℕ) (g : R) :
    g ∈ c.F w t ↔ ∀ β : Fin n →₀ ℕ, (∀ i, w i = 0 → β i = 0) → Finsupp.weight w β < t →
      c.D β g ∈ Ideal.span (c.x '' {i | w i ≠ 0}) := by
  obtain ⟨k, ι, hι, hrange⟩ := exists_enum (fun i => w i ≠ 0)
  have hw : ∀ a, 1 ≤ w (ι a) := fun a => Nat.pos_of_ne_zero ((hrange (ι a)).2 ⟨a, rfl⟩)
  rw [F_eq_subP c hι hrange, P_eq_subP c hι hrange, (subP c ι hι).mem_F_iff hw]
  constructor
  · intro H β hβ hwt
    rw [eq_lsum_ofIdx hι hrange hβ, ← Dl_subP c hι]
    refine H _ ?_
    rw [← weight_eq_wt hι hrange]; exact hwt
  · intro H α' hwt
    have h := H (lsum ι (PChart.ofIdx α')) (lsum_supp hrange _)
      (by rw [weight_lsum, PChart.cnt_ofIdx]; exact hwt)
    rw [← Dl_subP c hι] at h
    exact h

end BezoutCounterexample.Constructive
