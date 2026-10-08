import BezoutCounterexample.Constructive.PolyBar
import BezoutCounterexample.Constructive.ValBar

/-!
# Decidable ideal membership in `ℚ[Y₁, …, Y_N]` (Gröbner bases)

`mem_lspan_dec`: for a finite list `G₀` and any `f`, `f ∈ (G₀) ∨ f ∉ (G₀)`. Consequences for
`A = ℚ[Y] ⧸ (G₀)`: a zero test (`quot_eq_zero_or`), decidable divisibility (`quot_dvdDec`, in the
`DvdDec` form of `ValBar.lean`) and decidable membership in finitely generated ideals
(`quot_mem_lspan_dec`), transported along ring isomorphisms (`DvdDec.of_ringEquiv`,
`mem_lspan_dec_of_ringEquiv`).

* `top_reduce_rep`: `top_reduce` (`TopReduce.lean`) together with a standard representation
  `f - r = Σ hᵢ gᵢ` with every `hᵢ gᵢ` of degree `≤ deg f`.
* `isGB_of_crit` (**Buchberger's criterion**): if every S-polynomial `S(gᵢ, gⱼ)` has a
  representation `Σ kₗ gₗ` with every term of degree `< lcm(lm gᵢ, lm gⱼ)`, then every nonzero
  element of `(G)` has leading monomial divisible by some `lm gᵢ`. Well-founded induction on the
  bound `δ` of a representation `f = Σ hᵢ gᵢ`: either `δ` survives in `f` (and then some `lm gᵢ`
  divides it), or the top parts cancel, `Σ cᵢ lc(gᵢ) = 0`, and pivoting on one index rewrites them
  through S-polynomials with a smaller bound. The new bound is the degree of the auxiliary
  polynomial `Σ_{μ ∈ supports} μ` (`exists_bnd`), so no decision of the monomial order is used.
* `exists_gb` (**Buchberger's algorithm**): every list has a Gröbner basis with the same span.
  Termination by bar induction on Dickson's lemma (`af_finsupp_le`), with the invariant of
  `PolyBar.lean`; every round recomputes all S-polynomials and adds one remainder whose leading
  monomial is divisible by no previous one.

Decisions: equality in `ℚ`, `f = 0`, `≤` on `Fin N →₀ ℕ` (pointwise), finite searches. The linear
order on monomials is only used through `<`-induction and order lemmas, never decided.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {N : ℕ}

/-- Decided equality (`eq_or_ne` is `Classical.em`; this one uses the `DecidableEq` instance). -/
lemma deq {α : Type*} [DecidableEq α] (x y : α) : x = y ∨ x ≠ y :=
  if h : x = y then Or.inl h else Or.inr h

section Bnd

/-- All monomials of `p` are `≤ δ` in the monomial order. -/
def Bnd (p : MvPolynomial (Fin N) ℚ) (δ : Fin N →₀ ℕ) : Prop :=
  ∀ μ ∈ p.support, (mo N).toSyn μ ≤ (mo N).toSyn δ

/-- All monomials of `p` are `< δ` in the monomial order. -/
def BndLt (p : MvPolynomial (Fin N) ℚ) (δ : Fin N →₀ ℕ) : Prop :=
  ∀ μ ∈ p.support, (mo N).toSyn μ < (mo N).toSyn δ

lemma bnd_zero (δ : Fin N →₀ ℕ) : Bnd (0 : MvPolynomial (Fin N) ℚ) δ := by
  intro μ hμ; simp at hμ

lemma bndLt_zero (δ : Fin N →₀ ℕ) : BndLt (0 : MvPolynomial (Fin N) ℚ) δ := by
  intro μ hμ; simp at hμ

lemma bnd_degree (p : MvPolynomial (Fin N) ℚ) : Bnd p ((mo N).degree p) :=
  fun _ hμ => (mo N).le_degree hμ

lemma Bnd.mono {p : MvPolynomial (Fin N) ℚ} {δ δ' : Fin N →₀ ℕ} (h : Bnd p δ)
    (hle : (mo N).toSyn δ ≤ (mo N).toSyn δ') : Bnd p δ' :=
  fun μ hμ => (h μ hμ).trans hle

lemma Bnd.lt {p : MvPolynomial (Fin N) ℚ} {δ δ' : Fin N →₀ ℕ} (h : Bnd p δ)
    (hlt : (mo N).toSyn δ < (mo N).toSyn δ') : BndLt p δ' :=
  fun μ hμ => (h μ hμ).trans_lt hlt

lemma BndLt.bnd {p : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (h : BndLt p δ) : Bnd p δ :=
  fun μ hμ => (h μ hμ).le

lemma Bnd.add {p q : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (hp : Bnd p δ) (hq : Bnd q δ) :
    Bnd (p + q) δ := by
  intro μ hμ
  rcases Finset.mem_union.1 (MvPolynomial.support_add hμ) with h | h
  · exact hp μ h
  · exact hq μ h

lemma BndLt.add {p q : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (hp : BndLt p δ)
    (hq : BndLt q δ) : BndLt (p + q) δ := by
  intro μ hμ
  rcases Finset.mem_union.1 (MvPolynomial.support_add hμ) with h | h
  · exact hp μ h
  · exact hq μ h

lemma Bnd.neg {p : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (hp : Bnd p δ) : Bnd (-p) δ := by
  intro μ hμ
  exact hp μ (by rwa [MvPolynomial.support_neg] at hμ)

lemma Bnd.sub {p q : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (hp : Bnd p δ) (hq : Bnd q δ) :
    Bnd (p - q) δ := by
  rw [sub_eq_add_neg]; exact hp.add hq.neg

lemma bnd_mul {p q : MvPolynomial (Fin N) ℚ} {a b : Fin N →₀ ℕ} (hp : Bnd p a) (hq : Bnd q b) :
    Bnd (p * q) (a + b) := by
  intro μ hμ
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul p q hμ)
  rw [map_add, map_add]
  exact add_le_add (hp x hx) (hq y hy)

lemma bndLt_mul {p q : MvPolynomial (Fin N) ℚ} {a b : Fin N →₀ ℕ} (hp : Bnd p a)
    (hq : BndLt q b) : BndLt (p * q) (a + b) := by
  intro μ hμ
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul p q hμ)
  rw [map_add, map_add]
  exact add_lt_add_of_le_of_lt (hp x hx) (hq y hy)

lemma bnd_monomial (β : Fin N →₀ ℕ) (c : ℚ) : Bnd (monomial β c : MvPolynomial (Fin N) ℚ) β := by
  intro μ hμ
  rw [Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hμ)]

lemma bnd_sum {k : ℕ} {P : Fin k → MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ}
    (h : ∀ i, Bnd (P i) δ) : Bnd (∑ i, P i) δ := by
  induction k with
  | zero => simpa using bnd_zero δ
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    exact (h 0).add (ih fun i => h i.succ)

lemma bndLt_sum {k : ℕ} {P : Fin k → MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ}
    (h : ∀ i, BndLt (P i) δ) : BndLt (∑ i, P i) δ := by
  induction k with
  | zero => simpa using bndLt_zero δ
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    exact (h 0).add (ih fun i => h i.succ)

/-- A monomial `δ` in the support of a polynomial bounded by `δ` is its degree. -/
lemma degree_eq_of_bnd {p : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (h : Bnd p δ)
    (hδ : δ ∈ p.support) : (mo N).degree p = δ := by
  have hp : p ≠ 0 := by rintro rfl; simp at hδ
  exact (mo N).toSyn.injective
    (le_antisymm (h _ ((mo N).degree_mem_support hp)) ((mo N).le_degree hδ))

lemma not_mem_support_of_bndLt {p : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (h : BndLt p δ) :
    p.coeff δ = 0 := by
  rcases deq (p.coeff δ) 0 with h0 | h0
  · exact h0
  · exact absurd (h δ (MvPolynomial.mem_support_iff.2 h0)) (lt_irrefl _)

/-- A nonzero finite sum of rationals has a nonzero term (finite search). -/
lemma exists_ne_zero_of_sum {k : ℕ} {a : Fin k → ℚ} (h : ∑ i, a i ≠ 0) : ∃ i, a i ≠ 0 := by
  induction k with
  | zero => simp at h
  | succ k ih =>
    rcases deq (a 0) 0 with h0 | h0
    · rw [Fin.sum_univ_succ, h0, zero_add] at h
      obtain ⟨i, hi⟩ := ih h
      exact ⟨i.succ, hi⟩
    · exact ⟨0, h0⟩

/-- **A common bound attained in a support.** For finitely many polynomials, either all vanish, or
some `δ` bounds all of them and lies in one of their supports. `δ` is the degree of
`Σ_{μ ∈ ⋃ supports} μ`, whose coefficients are `1` on the union of the supports. -/
lemma exists_bnd {k : ℕ} (P : Fin k → MvPolynomial (Fin N) ℚ) :
    (∀ j, P j = 0) ∨ ∃ δ, (∀ j, Bnd (P j) δ) ∧ ∃ j, δ ∈ (P j).support := by
  let S : Finset (Fin N →₀ ℕ) := Finset.univ.biUnion fun j => (P j).support
  let Q : MvPolynomial (Fin N) ℚ := ∑ ν ∈ S, monomial ν 1
  have hQ : ∀ μ, Q.coeff μ = if μ ∈ S then 1 else 0 := by
    intro μ
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    exact Finset.sum_ite_eq' S μ (fun _ => (1 : ℚ))
  have hS : ∀ j, ∀ μ ∈ (P j).support, μ ∈ Q.support := by
    intro j μ hμ
    have hm : μ ∈ S := Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hμ⟩
    rw [MvPolynomial.mem_support_iff, hQ]
    simp only [hm, ↓reduceIte]
    exact one_ne_zero
  rcases deq Q 0 with h0 | h0
  · refine Or.inl fun j => ?_
    ext μ
    rcases deq ((P j).coeff μ) 0 with h | h
    · simpa using h
    · have := hS j μ (MvPolynomial.mem_support_iff.2 h)
      rw [h0] at this; simp at this
  · refine Or.inr ⟨(mo N).degree Q, fun j μ hμ => (mo N).le_degree (hS j μ hμ), ?_⟩
    have hd := (mo N).degree_mem_support h0
    rw [MvPolynomial.mem_support_iff, hQ] at hd
    split_ifs at hd with hm
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hm
      exact ⟨j, hj⟩
    · exact absurd rfl hd

end Bnd

section Rep

variable (G : List (MvPolynomial (Fin N) ℚ))

/-- `f = Σ hᵢ gᵢ` with every term bounded by `δ`. -/
def Rep (f : MvPolynomial (Fin N) ℚ) (δ : Fin N →₀ ℕ) : Prop :=
  ∃ h : Fin G.length → MvPolynomial (Fin N) ℚ,
    f = ∑ i, h i * G.get i ∧ ∀ i, Bnd (h i * G.get i) δ

/-- `f = Σ hᵢ gᵢ` with every term strictly below `δ`. -/
def RepLt (f : MvPolynomial (Fin N) ℚ) (δ : Fin N →₀ ℕ) : Prop :=
  ∃ h : Fin G.length → MvPolynomial (Fin N) ℚ,
    f = ∑ i, h i * G.get i ∧ ∀ i, BndLt (h i * G.get i) δ

variable {G}

lemma rep_zero (δ : Fin N →₀ ℕ) : Rep G 0 δ :=
  ⟨0, by simp, fun i => by simpa using bnd_zero δ⟩

lemma repLt_zero (δ : Fin N →₀ ℕ) : RepLt G 0 δ :=
  ⟨0, by simp, fun i => by simpa using bndLt_zero δ⟩

lemma Rep.add {f f' : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (h : Rep G f δ)
    (h' : Rep G f' δ) : Rep G (f + f') δ := by
  obtain ⟨a, rfl, ha⟩ := h
  obtain ⟨b, rfl, hb⟩ := h'
  refine ⟨a + b, by simp [add_mul, Finset.sum_add_distrib], fun i => ?_⟩
  rw [Pi.add_apply, add_mul]
  exact (ha i).add (hb i)

lemma RepLt.add {f f' : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (h : RepLt G f δ)
    (h' : RepLt G f' δ) : RepLt G (f + f') δ := by
  obtain ⟨a, rfl, ha⟩ := h
  obtain ⟨b, rfl, hb⟩ := h'
  refine ⟨a + b, by simp [add_mul, Finset.sum_add_distrib], fun i => ?_⟩
  rw [Pi.add_apply, add_mul]
  exact (ha i).add (hb i)

lemma RepLt.sum {k : ℕ} {F : Fin k → MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ}
    (h : ∀ i, RepLt G (F i) δ) : RepLt G (∑ i, F i) δ := by
  induction k with
  | zero => simpa using repLt_zero δ
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    exact (h 0).add (ih fun i => h i.succ)

lemma RepLt.monomial_mul {f : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (h : RepLt G f δ)
    (β : Fin N →₀ ℕ) (c : ℚ) : RepLt G (monomial β c * f) (β + δ) := by
  obtain ⟨a, rfl, ha⟩ := h
  refine ⟨fun i => monomial β c * a i, by rw [Finset.mul_sum]; simp [mul_assoc], fun i => ?_⟩
  rw [mul_assoc]
  exact bndLt_mul (bnd_monomial β c) (ha i)

lemma Rep.repLt {f : MvPolynomial (Fin N) ℚ} {δ δ' : Fin N →₀ ℕ} (h : Rep G f δ)
    (hlt : (mo N).toSyn δ < (mo N).toSyn δ') : RepLt G f δ' := by
  obtain ⟨a, rfl, ha⟩ := h
  exact ⟨a, rfl, fun i => (ha i).lt hlt⟩

/-- A monomial multiple of one generator. -/
lemma rep_single (i : Fin G.length) (β : Fin N →₀ ℕ) (c : ℚ) :
    Rep G (monomial β c * G.get i) (β + (mo N).degree (G.get i)) := by
  refine ⟨Pi.single i (monomial β c), ?_, fun j => ?_⟩
  · rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
  · rcases deq j i with rfl | hj
    · rw [Pi.single_eq_same]
      exact bnd_mul (bnd_monomial β c) (bnd_degree _)
    · rw [Pi.single_eq_of_ne hj, zero_mul]
      exact bnd_zero _

lemma mem_lspan_of_rep {f : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (h : Rep G f δ) :
    f ∈ lspan G := by
  obtain ⟨a, rfl, -⟩ := h
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span (List.get_mem G i))

lemma mem_lspan_of_repLt {f : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ} (h : RepLt G f δ) :
    f ∈ lspan G := by
  obtain ⟨a, rfl, -⟩ := h
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span (List.get_mem G i))

/-- Every element of `(G)` has some representation. -/
lemma exists_rep_of_mem {f : MvPolynomial (Fin N) ℚ} (hf : f ∈ lspan G) :
    ∃ h : Fin G.length → MvPolynomial (Fin N) ℚ, f = ∑ i, h i * G.get i := by
  have hset : {x | x ∈ G} = Set.range G.get := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    exact List.mem_iff_get
  rw [lspan, hset] at hf
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hf
  exact ⟨c, hc.symm⟩

/-- **Top reduction with a standard representation.** -/
theorem top_reduce_rep (hG : ∀ g ∈ G, g ≠ 0) (f : MvPolynomial (Fin N) ℚ) :
    ∃ r, Rep G (f - r) ((mo N).degree f) ∧ Bnd r ((mo N).degree f) ∧
      (r = 0 ∨ (r ≠ 0 ∧ ¬ DvG G ((mo N).degree r))) := by
  suffices H : ∀ d : (mo N).syn, ∀ f : MvPolynomial (Fin N) ℚ,
      (mo N).toSyn ((mo N).degree f) = d →
        ∃ r, Rep G (f - r) ((mo N).degree f) ∧ Bnd r ((mo N).degree f) ∧
          (r = 0 ∨ (r ≠ 0 ∧ ¬ DvG G ((mo N).degree r))) from
    H _ f rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
  intro f hfd
  if hf : f = 0 then
    exact ⟨0, by rw [hf, sub_zero]; exact rep_zero _, bnd_zero _, Or.inl rfl⟩
  else if hdv : ∃ g ∈ G, (mo N).degree g ≤ (mo N).degree f then
    obtain ⟨g, hgG, hgf⟩ := hdv
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hgG
    have hg0 := hG _ hgG
    if hdeg : (mo N).degree f = 0 then
      have hg : (mo N).degree (G.get i) = 0 := le_antisymm (hdeg ▸ hgf) zero_le
      refine ⟨0, ?_, bnd_zero _, Or.inl rfl⟩
      have hgC := (mo N).eq_C_of_degree_eq_zero hg
      have hlc : (mo N).leadingCoeff (G.get i) ≠ 0 := (mo N).leadingCoeff_ne_zero_iff.2 hg0
      have hfC := (mo N).eq_C_of_degree_eq_zero hdeg
      generalize (mo N).leadingCoeff (G.get i) = c at hgC hlc
      have heq : f - 0 = monomial 0 ((mo N).leadingCoeff f * c⁻¹) * G.get i := by
        rw [sub_zero, hgC, ← C_apply, ← map_mul, mul_assoc, inv_mul_cancel₀ hlc, mul_one]
        exact hfC
      have := rep_single i 0 ((mo N).leadingCoeff f * c⁻¹)
      rw [zero_add, hg, ← heq] at this
      rwa [hdeg]
    else
      have hb : IsUnit ((mo N).leadingCoeff (G.get i)) :=
        isUnit_iff_ne_zero.2 ((mo N).leadingCoeff_ne_zero_iff.2 hg0)
      have hlt := (mo N).degree_reduce_lt hb hgf hdeg
      obtain ⟨r, hr, hrb, hr'⟩ := ih _ (hfd ▸ hlt) ((mo N).reduce hb f) rfl
      refine ⟨r, ?_, hrb.mono hlt.le, hr'⟩
      have hsplit : f - r = monomial ((mo N).degree f - (mo N).degree (G.get i))
          (hb.unit⁻¹ * (mo N).leadingCoeff f) * G.get i + ((mo N).reduce hb f - r) := by
        rw [MonomialOrder.reduce]; ring
      rw [hsplit]
      have h1 := rep_single i ((mo N).degree f - (mo N).degree (G.get i))
        (hb.unit⁻¹ * (mo N).leadingCoeff f)
      rw [tsub_add_cancel_of_le hgf] at h1
      obtain ⟨a, ha, hab⟩ := hr
      exact h1.add ⟨a, ha, fun j => (hab j).mono hlt.le⟩
  else
    exact ⟨f, by rw [sub_self]; exact rep_zero _, bnd_degree f, Or.inr ⟨hf, hdv⟩⟩

end Rep

section Buchberger

variable {G : List (MvPolynomial (Fin N) ℚ)}

/-- The S-polynomial, normalised by the leading coefficients. -/
noncomputable def spoly (g g' : MvPolynomial (Fin N) ℚ) : MvPolynomial (Fin N) ℚ :=
  monomial ((mo N).degree g ⊔ (mo N).degree g' - (mo N).degree g) ((mo N).leadingCoeff g)⁻¹ * g -
    monomial ((mo N).degree g ⊔ (mo N).degree g' - (mo N).degree g')
      ((mo N).leadingCoeff g')⁻¹ * g'

/-- `X^α g` has coefficient `lc g` at `α + deg g`, read off at any `δ ≥ deg g`. -/
lemma coeff_monomial_mul_top {g : MvPolynomial (Fin N) ℚ} {δ : Fin N →₀ ℕ}
    (hd : (mo N).degree g ≤ δ) (c : ℚ) :
    (monomial (δ - (mo N).degree g) c * g).coeff δ = c * (mo N).leadingCoeff g := by
  rw [MvPolynomial.coeff_monomial_mul']
  simp only [tsub_le_self, ↓reduceIte, tsub_tsub_cancel_of_le hd]
  rfl

lemma bnd_monomial_mul_top (g : MvPolynomial (Fin N) ℚ) {δ : Fin N →₀ ℕ}
    (hd : (mo N).degree g ≤ δ) (c : ℚ) : Bnd (monomial (δ - (mo N).degree g) c * g) δ := by
  have := bnd_mul (bnd_monomial (δ - (mo N).degree g) c) (bnd_degree g)
  rwa [tsub_add_cancel_of_le hd] at this

lemma lt_of_bnd_of_ne {μ δ : Fin N →₀ ℕ} (h : (mo N).toSyn μ ≤ (mo N).toSyn δ) (hne : μ ≠ δ) :
    (mo N).toSyn μ < (mo N).toSyn δ :=
  lt_of_le_of_ne h fun h' => hne ((mo N).toSyn.injective h')

/-- The leading terms cancel in an S-polynomial. -/
lemma spoly_bndLt {g g' : MvPolynomial (Fin N) ℚ} (hg : g ≠ 0) (hg' : g' ≠ 0) :
    BndLt (spoly g g') ((mo N).degree g ⊔ (mo N).degree g') := by
  have h1 := le_sup_left (a := (mo N).degree g) (b := (mo N).degree g')
  have h2 := le_sup_right (a := (mo N).degree g) (b := (mo N).degree g')
  have hb : Bnd (spoly g g') ((mo N).degree g ⊔ (mo N).degree g') :=
    (bnd_monomial_mul_top g h1 _).sub (bnd_monomial_mul_top g' h2 _)
  have hc : (spoly g g').coeff ((mo N).degree g ⊔ (mo N).degree g') = 0 := by
    rw [spoly, MvPolynomial.coeff_sub, coeff_monomial_mul_top h1, coeff_monomial_mul_top h2,
      inv_mul_cancel₀ ((mo N).leadingCoeff_ne_zero_iff.2 hg),
      inv_mul_cancel₀ ((mo N).leadingCoeff_ne_zero_iff.2 hg'), sub_self]
  intro μ hμ
  refine lt_of_bnd_of_ne (hb μ hμ) fun h => ?_
  rw [h] at hμ
  exact MvPolynomial.mem_support_iff.1 hμ hc

/-- Buchberger's condition: every S-polynomial has a representation below the lcm. -/
def Crit (G : List (MvPolynomial (Fin N) ℚ)) : Prop :=
  ∀ i j : Fin G.length, RepLt G (spoly (G.get i) (G.get j))
    ((mo N).degree (G.get i) ⊔ (mo N).degree (G.get j))

/-- Gröbner basis: every nonzero element of `(G)` has leading monomial divisible by some
`lm gᵢ`. -/
def IsGB (G : List (MvPolynomial (Fin N) ℚ)) : Prop :=
  ∀ f ∈ lspan G, f = 0 ∨ DvG G ((mo N).degree f)

/-- Finite search over `Fin k`. -/
lemma fin_forall_or_exists {k : ℕ} {A B : Fin k → Prop} (h : ∀ i, A i ∨ B i) :
    (∀ i, A i) ∨ ∃ i, B i := by
  induction k with
  | zero => exact Or.inl fun i => i.elim0
  | succ k ih =>
    rcases h 0 with h0 | h0
    · rcases ih (A := fun i => A i.succ) (B := fun i => B i.succ) (fun i => h i.succ) with
        h' | ⟨i, hi⟩
      · exact Or.inl fun i => Fin.cases h0 h' i
      · exact Or.inr ⟨i.succ, hi⟩
    · exact Or.inr ⟨0, h0⟩

lemma bndLt_mul' {p q : MvPolynomial (Fin N) ℚ} {a b : Fin N →₀ ℕ} (hp : BndLt p a)
    (hq : Bnd q b) : BndLt (p * q) (a + b) := by
  rw [mul_comm, add_comm]; exact bndLt_mul hq hp

/-- **The reduction step** of Buchberger's criterion: if the top coefficient cancels, the bound
can be lowered. -/
theorem repLt_of_rep_of_coeff (hG : ∀ g ∈ G, g ≠ 0) (hc : Crit G) {f : MvPolynomial (Fin N) ℚ}
    {δ : Fin N →₀ ℕ} {h : Fin G.length → MvPolynomial (Fin N) ℚ}
    (hf : f = ∑ i, h i * G.get i) (hb : ∀ i, Bnd (h i * G.get i) δ) (hδ : f.coeff δ = 0) :
    RepLt G f δ := by
  -- the top parts
  let d : Fin G.length → Fin N →₀ ℕ := fun i => (mo N).degree (G.get i)
  let lc : Fin G.length → ℚ := fun i => (mo N).leadingCoeff (G.get i)
  have hlc : ∀ i, lc i ≠ 0 := fun i =>
    (mo N).leadingCoeff_ne_zero_iff.2 (hG _ (List.get_mem G i))
  let c : Fin G.length → ℚ := fun i => if d i ≤ δ then (h i).coeff (δ - d i) else 0
  let h' : Fin G.length → MvPolynomial (Fin N) ℚ := fun i => h i - monomial (δ - d i) (c i)
  let a : Fin G.length → ℚ := fun i => c i * lc i
  -- (A) the remaining parts are strictly below `δ`
  have hA : ∀ i, BndLt (h' i * G.get i) δ := by
    intro i
    by_cases hD : d i ≤ δ
    · have hc' : c i = (h i).coeff (δ - d i) := by simp only [c, hD, ↓reduceIte]
      have hlt : BndLt (h' i) (δ - d i) := by
        intro μ hμ
        have hμ' : (h' i).coeff μ ≠ 0 := MvPolynomial.mem_support_iff.1 hμ
        rcases deq μ (δ - d i) with rfl | hne
        · exact absurd (by simp only [h', MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial,
            ↓reduceIte, hc', sub_self]) hμ'
        · have hμh : μ ∈ (h i).support := by
            rw [MvPolynomial.mem_support_iff]
            have : (h' i).coeff μ = (h i).coeff μ := by
              simp only [h', MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, sub_eq_self]
              exact ite_eq_right_iff.2 fun h => absurd h (Ne.symm hne)
            rwa [← this]
          have hh0 : h i ≠ 0 := by rintro h0; rw [h0] at hμh; simp at hμh
          have hprod : h i * G.get i ≠ 0 := mul_ne_zero hh0 (hG _ (List.get_mem G i))
          have hdeg := hb i _ ((mo N).degree_mem_support hprod)
          rw [(mo N).degree_mul hh0 (hG _ (List.get_mem G i)), ← tsub_add_cancel_of_le hD,
            map_add, map_add] at hdeg
          have hle : (mo N).toSyn ((mo N).degree (h i)) ≤ (mo N).toSyn (δ - d i) :=
            le_of_add_le_add_right hdeg
          exact lt_of_bnd_of_ne (((mo N).le_degree hμh).trans hle) hne
      have := bndLt_mul' hlt (bnd_degree (G.get i))
      rwa [tsub_add_cancel_of_le hD] at this
    · have hc0 : c i = 0 := by simp only [c, hD, ↓reduceIte]
      have hh' : h' i = h i := by simp only [h', hc0, map_zero, sub_zero]
      rw [hh']
      rcases deq (h i) 0 with h0 | hh0
      · rw [h0, zero_mul]; exact bndLt_zero δ
      have hprod : h i * G.get i ≠ 0 := mul_ne_zero hh0 (hG _ (List.get_mem G i))
      have hle := hb i _ ((mo N).degree_mem_support hprod)
      have hne : (mo N).degree (h i * G.get i) ≠ δ := by
        intro heq
        rw [(mo N).degree_mul hh0 (hG _ (List.get_mem G i))] at heq
        exact hD (heq ▸ le_add_self)
      intro μ hμ
      exact ((mo N).le_degree hμ).trans_lt (lt_of_bnd_of_ne hle hne)
  -- (B) top coefficients
  have hB : ∀ i, (monomial (δ - d i) (c i) * G.get i).coeff δ = a i := by
    intro i
    by_cases hD : d i ≤ δ
    · exact coeff_monomial_mul_top hD (c i)
    · have hc0 : c i = 0 := by simp only [c, hD, ↓reduceIte]
      simp only [a, hc0, map_zero, zero_mul]
      rfl
  -- (C) the splitting of `f`
  have hC : f = ∑ i, h' i * G.get i + ∑ i, monomial (δ - d i) (c i) * G.get i := by
    rw [hf, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [h', sub_mul, sub_add_cancel]
  -- (D) the top coefficients cancel
  have hD : ∑ i, a i = 0 := by
    have := congrArg (fun p => p.coeff δ) hC
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sum] at this
    rw [hδ, Finset.sum_eq_zero (fun i _ => not_mem_support_of_bndLt (hA i)), zero_add] at this
    rw [this]
    exact (Finset.sum_congr rfl fun i _ => hB i).symm
  have hrest : RepLt G (∑ i, h' i * G.get i) δ := ⟨h', rfl, hA⟩
  rw [hC]
  refine hrest.add ?_
  rcases fin_forall_or_exists (A := fun i => ¬ d i ≤ δ) (B := fun i => d i ≤ δ)
      (fun i => if hD : d i ≤ δ then Or.inr hD else Or.inl hD) with hnone | ⟨i₀, hi₀⟩
  · -- no top part at all
    have : ∑ i, monomial (δ - d i) (c i) * G.get i = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hc0 : c i = 0 := by simp only [c, hnone i, ↓reduceIte]
      rw [hc0, map_zero, zero_mul]
    rw [this]; exact repLt_zero δ
  -- pivot on `i₀`
  let L : Fin G.length → Fin N →₀ ℕ := fun i => d i ⊔ d i₀
  have hE : ∀ i, monomial (δ - L i) (a i) * spoly (G.get i) (G.get i₀) =
      monomial (δ - d i) (c i) * G.get i -
        monomial (δ - d i₀) (a i * (lc i₀)⁻¹) * G.get i₀ := by
    intro i
    by_cases hD : d i ≤ δ
    · have hL : L i ≤ δ := sup_le hD hi₀
      have hc' : a i * (lc i)⁻¹ = c i := by
        simp only [a]; rw [mul_assoc, mul_inv_cancel₀ (hlc i), mul_one]
      simp only [spoly, mul_sub, ← mul_assoc, MvPolynomial.monomial_mul_monomial]
      rw [tsub_add_tsub_cancel hL (le_sup_left : d i ≤ L i),
        tsub_add_tsub_cancel hL (le_sup_right : d i₀ ≤ L i)]
      simp only [lc] at hc'
      rw [hc']
    · have hc0 : c i = 0 := by simp only [c, hD, ↓reduceIte]
      simp only [a, hc0, zero_mul, map_zero, sub_zero]
  have hsum : ∑ i, monomial (δ - d i) (c i) * G.get i =
      ∑ i, monomial (δ - L i) (a i) * spoly (G.get i) (G.get i₀) := by
    rw [Finset.sum_congr rfl fun i _ => hE i, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← map_sum, ← Finset.sum_mul, hD, zero_mul, map_zero, zero_mul, sub_zero]
  rw [hsum]
  refine RepLt.sum fun i => ?_
  by_cases hD' : d i ≤ δ
  · have := (hc i i₀).monomial_mul (δ - L i) (a i)
    rwa [tsub_add_cancel_of_le (sup_le hD' hi₀)] at this
  · have hc0 : c i = 0 := by simp only [c, hD', ↓reduceIte]
    have : a i = 0 := by simp only [a, hc0, zero_mul]
    rw [this, map_zero, zero_mul]; exact repLt_zero δ

/-- From a representation with bound `δ` to a Gröbner witness, by induction on `δ`. -/
theorem dvG_of_rep (hG : ∀ g ∈ G, g ≠ 0) (hc : Crit G) :
    ∀ (δ : Fin N →₀ ℕ) (f : MvPolynomial (Fin N) ℚ), Rep G f δ →
      f = 0 ∨ DvG G ((mo N).degree f) := by
  suffices H : ∀ e : (mo N).syn, ∀ δ, (mo N).toSyn δ = e → ∀ f, Rep G f δ →
      f = 0 ∨ DvG G ((mo N).degree f) from fun δ => H _ δ rfl
  intro e
  induction e using WellFoundedLT.induction with
  | _ e ih =>
  intro δ hδe f ⟨h, hf, hb⟩
  rcases deq (f.coeff δ) 0 with hδ | hδ
  · obtain ⟨k, hk, hkb⟩ := repLt_of_rep_of_coeff hG hc hf hb hδ
    rcases exists_bnd (fun j => k j * G.get j) with h0 | ⟨δ', hδ', j, hj⟩
    · left; rw [hk]; exact Finset.sum_eq_zero fun j _ => h0 j
    · exact ih _ (hδe ▸ hkb j δ' hj) δ' rfl f ⟨k, hk, hδ'⟩
  · have hsum : f.coeff δ = ∑ i, (h i * G.get i).coeff δ := by
      rw [hf, MvPolynomial.coeff_sum]
    obtain ⟨i, hi⟩ := exists_ne_zero_of_sum (hsum ▸ hδ)
    have hmem : δ ∈ (h i * G.get i).support := MvPolynomial.mem_support_iff.2 hi
    have hdeg := degree_eq_of_bnd (hb i) hmem
    have hhi : h i ≠ 0 := by rintro h0; rw [h0, zero_mul] at hi; exact hi rfl
    rw [(mo N).degree_mul hhi (hG _ (List.get_mem G i))] at hdeg
    have hfb : Bnd f δ := hf ▸ bnd_sum hb
    have hfdeg := degree_eq_of_bnd hfb (MvPolynomial.mem_support_iff.2 hδ)
    right
    rw [hfdeg]
    exact ⟨G.get i, List.get_mem G i, hdeg ▸ le_add_self⟩

/-- **Buchberger's criterion.** -/
theorem isGB_of_crit (hG : ∀ g ∈ G, g ≠ 0) (hc : Crit G) : IsGB G := by
  intro f hf
  obtain ⟨h, hh⟩ := exists_rep_of_mem hf
  rcases exists_bnd (fun i => h i * G.get i) with h0 | ⟨δ, hδ, -⟩
  · left; rw [hh]; exact Finset.sum_eq_zero fun i _ => h0 i
  · exact dvG_of_rep hG hc δ f ⟨h, hh, hδ⟩

/-- One round: either Buchberger's condition holds, or some S-polynomial leaves a new remainder. -/
theorem crit_or_new (hG : ∀ g ∈ G, g ≠ 0) :
    Crit G ∨ ∃ r, r ∈ lspan G ∧ r ≠ 0 ∧ ¬ DvG G ((mo N).degree r) := by
  have step : ∀ i j : Fin G.length, RepLt G (spoly (G.get i) (G.get j))
      ((mo N).degree (G.get i) ⊔ (mo N).degree (G.get j)) ∨
        ∃ r, r ∈ lspan G ∧ r ≠ 0 ∧ ¬ DvG G ((mo N).degree r) := by
    intro i j
    have hgi := hG _ (List.get_mem G i)
    have hgj := hG _ (List.get_mem G j)
    obtain ⟨r, hr, -, h0 | ⟨hr0, hdv⟩⟩ := top_reduce_rep hG (spoly (G.get i) (G.get j))
    · left
      rw [h0, sub_zero] at hr
      rcases deq (spoly (G.get i) (G.get j)) 0 with hS | hS
      · rw [hS]; exact repLt_zero _
      · exact hr.repLt (spoly_bndLt hgi hgj _ ((mo N).degree_mem_support hS))
    · right
      refine ⟨r, ?_, hr0, hdv⟩
      have hS : spoly (G.get i) (G.get j) ∈ lspan G := by
        rw [spoly]
        exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (List.get_mem G i)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (List.get_mem G j)))
      have := sub_mem hS (mem_lspan_of_rep hr)
      rwa [sub_sub_cancel] at this
  rcases fin_forall_or_exists (fun i => fin_forall_or_exists (step i)) with h | ⟨_, _, hr⟩
  · exact Or.inl h
  · exact Or.inr hr

lemma lspan_cons_of_mem {r : MvPolynomial (Fin N) ℚ} (hr : r ∈ lspan G) :
    lspan (r :: G) = lspan G :=
  le_antisymm (Ideal.span_le.2 fun z hz => by
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hr
    · exact Ideal.subset_span hz) (lspan_le_cons G r)

/-- **Buchberger's algorithm**, terminating by bar induction on Dickson's lemma. -/
theorem gb_complete {T : (Fin N →₀ ℕ) → (Fin N →₀ ℕ) → Prop} (hT : AF T) :
    ∀ G : List (MvPolynomial (Fin N) ℚ), (∀ g ∈ G, g ≠ 0) →
      (∀ x y, T x y → x ≤ y ∨ DvG G x) →
        ∃ G', lspan G' = lspan G ∧ (∀ g ∈ G', g ≠ 0) ∧ IsGB G' := by
  induction hT with
  | now hT =>
    intro G hG hl
    rcases crit_or_new hG with hc | ⟨r, hrm, hr0, hdv⟩
    · exact ⟨G, rfl, hG, isGB_of_crit hG hc⟩
    have hdeg : (mo N).degree r = 0 := by
      rcases hl _ 0 (hT _ _) with h | h
      · exact le_antisymm h zero_le
      · exact absurd h hdv
    refine ⟨r :: G, lspan_cons_of_mem hrm, ?_, fun f _ => Or.inr ⟨r, List.mem_cons_self, ?_⟩⟩
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact hr0
      · exact hG g hg
    · rw [hdeg]; exact zero_le
  | up _ ih =>
    intro G hG hl
    rcases crit_or_new hG with hc | ⟨r, hrm, hr0, hdv⟩
    · exact ⟨G, rfl, hG, isGB_of_crit hG hc⟩
    obtain ⟨G', hG'span, hG'0, hG'gb⟩ := ih ((mo N).degree r) (r :: G) (fun g hg => by
        rcases List.mem_cons.1 hg with rfl | hg
        · exact hr0
        · exact hG g hg) (fun x y h => by
        rcases h with h | h
        · exact (hl x y h).imp_right (DvG.cons r)
        · rcases hl _ x h with h | h
          · exact Or.inr ⟨r, List.mem_cons_self, h⟩
          · exact absurd h hdv)
    exact ⟨G', hG'span.trans (lspan_cons_of_mem hrm), hG'0, hG'gb⟩

/-- Every finite list has a Gröbner basis with the same span. -/
theorem exists_gb (G₀ : List (MvPolynomial (Fin N) ℚ)) :
    ∃ G, lspan G = lspan G₀ ∧ (∀ g ∈ G, g ≠ 0) ∧ IsGB G := by
  let G₁ := G₀.filter fun g => decide (g ≠ 0)
  have h0 : ∀ g ∈ G₁, g ≠ 0 := fun g hg => of_decide_eq_true (List.mem_filter.1 hg).2
  have hspan : lspan G₁ = lspan G₀ := by
    refine le_antisymm (Ideal.span_mono fun g hg => (List.mem_filter.1 hg).1)
      (Ideal.span_le.2 fun g hg => ?_)
    rcases deq g 0 with rfl | hg0
    · exact zero_mem _
    · exact Ideal.subset_span (List.mem_filter.2 ⟨hg, decide_eq_true hg0⟩)
  obtain ⟨G, hG, hG0, hgb⟩ := gb_complete (af_finsupp_le N) G₁ h0 fun x y h => Or.inl h
  exact ⟨G, hG.trans hspan, hG0, hgb⟩

/-- **Decidable ideal membership** in `ℚ[Y₁, …, Y_N]`. -/
theorem mem_lspan_dec (G₀ : List (MvPolynomial (Fin N) ℚ)) (f : MvPolynomial (Fin N) ℚ) :
    f ∈ lspan G₀ ∨ f ∉ lspan G₀ := by
  obtain ⟨G, hG, hG0, hgb⟩ := exists_gb G₀
  rw [← hG]
  obtain ⟨r, hr, h0 | ⟨hr0, hdv⟩⟩ := top_reduce G hG0 f
  · rw [h0, sub_zero] at hr; exact Or.inl hr
  · refine Or.inr fun hf => ?_
    have hrm : r ∈ lspan G := by
      have := sub_mem hf hr; rwa [sub_sub_cancel] at this
    rcases hgb r hrm with h | h
    · exact hr0 h
    · exact hdv h

end Buchberger

section Quotient

variable (G₀ : List (MvPolynomial (Fin N) ℚ))

/-- **Zero test** in `ℚ[Y] ⧸ (G₀)`. -/
theorem quot_eq_zero_or (a : MvPolynomial (Fin N) ℚ ⧸ lspan G₀) : a = 0 ∨ a ≠ 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rcases mem_lspan_dec G₀ p with h | h
  · exact Or.inl (Ideal.Quotient.eq_zero_iff_mem.2 h)
  · exact Or.inr fun h' => h (Ideal.Quotient.eq_zero_iff_mem.1 h')

lemma lspan_cons_eq_sup {R : Type*} [CommRing R] (p : R) (l : List R) :
    lspan (p :: l) = Ideal.span {p} ⊔ lspan l := by
  rw [lspan, lspan, ← Ideal.span_insert]
  congr 1
  ext x
  simp only [List.mem_cons, Set.mem_insert_iff, Set.mem_ofPred_eq]

lemma lspan_append_eq_sup {R : Type*} [CommRing R] (l l' : List R) :
    lspan (l ++ l') = lspan l ⊔ lspan l' := by
  rw [lspan, lspan, lspan, ← Ideal.span_union]
  congr 1
  ext x
  simp only [List.mem_append, Set.mem_union, Set.mem_ofPred_eq]

lemma quot_dvd_iff (p q : MvPolynomial (Fin N) ℚ) :
    Ideal.Quotient.mk (lspan G₀) p ∣ Ideal.Quotient.mk (lspan G₀) q ↔ q ∈ lspan (p :: G₀) := by
  rw [lspan_cons_eq_sup, Submodule.mem_sup]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, Ideal.Quotient.eq] at hc
    exact ⟨p * c', Ideal.mem_span_singleton'.2 ⟨c', mul_comm _ _⟩, q - p * c', hc,
      add_sub_cancel _ _⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hz, add_zero, map_mul, mul_comm]

/-- **Decidable divisibility** in `ℚ[Y] ⧸ (G₀)`. -/
theorem quot_dvdDec : DvdDec (MvPolynomial (Fin N) ℚ ⧸ lspan G₀) := by
  intro a b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [quot_dvd_iff]
  exact mem_lspan_dec _ q

lemma exists_lift_list {R : Type*} [CommRing R] (I : Ideal R) (L : List (R ⧸ I)) :
    ∃ L' : List R, L'.map (Ideal.Quotient.mk I) = L := by
  induction L with
  | nil => exact ⟨[], rfl⟩
  | cons x L ih =>
    obtain ⟨L', hL'⟩ := ih
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x' :: L', by rw [List.map_cons, hL']⟩

/-- **Decidable membership** in finitely generated ideals of `ℚ[Y] ⧸ (G₀)`. -/
theorem quot_mem_lspan_dec (L : List (MvPolynomial (Fin N) ℚ ⧸ lspan G₀))
    (x : MvPolynomial (Fin N) ℚ ⧸ lspan G₀) : x ∈ lspan L ∨ x ∉ lspan L := by
  obtain ⟨L', rfl⟩ := exists_lift_list _ L
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hmap : lspan (L'.map (Ideal.Quotient.mk (lspan G₀))) =
      Ideal.map (Ideal.Quotient.mk (lspan G₀)) (lspan L') := by
    rw [lspan, lspan, Ideal.map_span]
    congr 1
    ext y
    simp only [List.mem_map, Set.mem_ofPred_eq, Set.mem_image]
  have hiff : Ideal.Quotient.mk (lspan G₀) q ∈ lspan (L'.map (Ideal.Quotient.mk (lspan G₀))) ↔
      q ∈ lspan (L' ++ G₀) := by
    rw [hmap, lspan_append_eq_sup, Submodule.mem_sup,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · rintro ⟨y, hy, hyq⟩
      rw [Ideal.Quotient.eq] at hyq
      exact ⟨y, hy, q - y, by rw [← neg_sub]; exact neg_mem hyq, add_sub_cancel _ _⟩
    · rintro ⟨y, hy, z, hz, rfl⟩
      refine ⟨y, hy, ?_⟩
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hz, add_zero]
  rw [hiff]
  exact mem_lspan_dec _ q

end Quotient

section Transport

variable {A B : Type*} [CommRing A] [CommRing B]

lemma DvdDec.of_ringEquiv (e : A ≃+* B) (h : DvdDec B) : DvdDec A := by
  intro a b
  rcases h (e a) (e b) with ⟨c, hc⟩ | hn
  · refine Or.inl ⟨e.symm c, e.injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply, hc]
  · exact Or.inr fun ⟨c, hc⟩ => hn ⟨e c, by rw [hc, map_mul]⟩

lemma mem_lspan_dec_of_ringEquiv (e : A ≃+* B)
    (h : ∀ (L : List B) (y : B), y ∈ lspan L ∨ y ∉ lspan L) (L : List A) (x : A) :
    x ∈ lspan L ∨ x ∉ lspan L := by
  have hiff : x ∈ lspan L ↔ e x ∈ lspan (L.map e) := by
    have hmap : lspan (L.map e) = Ideal.map e (lspan L) := by
      rw [lspan, lspan, Ideal.map_span]
      congr 1
      ext y
      simp only [List.mem_map, Set.mem_ofPred_eq, Set.mem_image]
    rw [hmap, Ideal.mem_map_of_equiv]
    constructor
    · exact fun hx => ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', he⟩
      rwa [← e.injective he]
  rw [hiff]
  exact h _ _

end Transport

end BezoutCounterexample.Constructive
