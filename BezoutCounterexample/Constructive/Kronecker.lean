import BezoutCounterexample.Constructive.DecTransfer
import BezoutCounterexample.Constructive.Groebner
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.NumberTheory.Divisors

/-!
# Factorisation in `ℚ[X]` (Kronecker + Gauss; `docs/d5-plan.md`, Handoff 2, option 2, step 1)

* `kronecker_search`: for `F ∈ ℤ[X]`, `F ≠ 0`, and a degree bound `d`, either some `G ∈ ℚ[X]` with
  `0 < deg G ≤ d` divides `F`, or every divisor `g ∈ ℤ[X]` of `F` of degree `≤ d` is constant.
  Kronecker: take a set `T` of `≥ d + 1` integers with `F(t) ≠ 0` (found among `0, …, deg F + d`,
  since `F` has at most `deg F` roots); a divisor `g` has `g(t) ∣ F(t)`, so `g` is the Lagrange
  interpolant of one of the finitely many tuples `(e_t)_{t ∈ T}`, `e_t ∣ F(t)`; each interpolant is
  tested (`0 < deg`, `≤ d`, divisibility in `ℚ[X]`). The search is generic in `d`, so it also
  serves the multivariate case via Kronecker substitution (step 2).
* `factor_search`: the same over `ℚ`: `f ≠ 0` has a factor `g` with `0 < deg g ≤ d`, or none.
  From `kronecker_search` by clearing denominators and Gauss's lemma (a rational divisor `g`
  becomes the primitive part of an integral multiple, still dividing).
* `irreducible_or_split`: `f` with `0 < deg f` is irreducible or `f = g h` with both degrees
  positive.
* `exists_factorisation`: every `f ≠ 0` is a unit times a product of irreducibles;
  `exists_irreducible_dvd`: a nonconstant `f` has an irreducible factor.
* `irreducible_quotient` (input for (G2)): `ℚ[X] ⧸ (p)` is a discrete field (`x = 0 ∨ IsUnit x`).

No `@[cprim]`. The decisions are: `ℤ` and `ℚ` equality, `ℕ` order, divisibility in `ℚ[X]`
(`dvdDec_polynomial`), and a search through a finite set (`Finset.exists_or_forall_not'`).
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open Polynomial

section Search

/-- A search through a finite set with a decidable predicate. -/
lemma Multiset.exists_or_forall_not' {α : Type*} (m : Multiset α) {P : α → Prop}
    (h : ∀ a, P a ∨ ¬ P a) : (∃ a ∈ m, P a) ∨ ∀ a ∈ m, ¬ P a := by
  induction m using Multiset.induction_on with
  | empty => exact Or.inr fun a ha => absurd ha (Multiset.notMem_zero a)
  | cons b m ih =>
    rcases h b with hb | hb
    · exact Or.inl ⟨b, Multiset.mem_cons_self b m, hb⟩
    rcases ih with ⟨a, ha, hPa⟩ | hn
    · exact Or.inl ⟨a, Multiset.mem_cons_of_mem ha, hPa⟩
    · refine Or.inr fun a ha => ?_
      rcases Multiset.mem_cons.1 ha with rfl | ha
      · exact hb
      · exact hn a ha

lemma Finset.exists_or_forall_not' {α : Type*} (s : Finset α) {P : α → Prop}
    (h : ∀ a, P a ∨ ¬ P a) : (∃ a ∈ s, P a) ∨ ∀ a ∈ s, ¬ P a :=
  Multiset.exists_or_forall_not' s.val h

end Search

section Divisors

/-- The (finitely many) integer divisors of `m`. -/
def intDivisors (m : ℤ) : Finset ℤ :=
  m.natAbs.divisors.image (fun k : ℕ => (k : ℤ)) ∪ m.natAbs.divisors.image (fun k : ℕ => -(k : ℤ))

lemma mem_intDivisors {a m : ℤ} (hm : m ≠ 0) (h : a ∣ m) : a ∈ intDivisors m := by
  have hk : a.natAbs ∈ m.natAbs.divisors :=
    Nat.mem_divisors.2 ⟨Int.natAbs_dvd_natAbs.2 h, Int.natAbs_ne_zero.2 hm⟩
  unfold intDivisors
  rcases Int.natAbs_eq a with ha | ha
  · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨_, hk, ha.symm⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, hk, ha.symm⟩)

end Divisors

section Kronecker

lemma dvdDec_rat : DvdDec ℚ := by
  intro a b
  rcases deq a 0 with rfl | ha
  · rcases deq b 0 with rfl | hb
    · exact Or.inl dvd_rfl
    · exact Or.inr fun h => hb (zero_dvd_iff.1 h)
  · exact Or.inl ⟨a⁻¹ * b, by rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]⟩

lemma dvdDec_ratPoly : DvdDec ℚ[X] :=
  dvdDec_polynomial (fun a => deq a 0) dvdDec_rat

/-- Kronecker's node set: `≥ d + 1` integers at which `F` does not vanish. -/
lemma exists_nodes {F : ℤ[X]} (hF : F ≠ 0) (d : ℕ) :
    ∃ T : Finset ℤ, d + 1 ≤ T.card ∧ ∀ t ∈ T, F.eval t ≠ 0 := by
  set S := (Finset.range (F.natDegree + d + 1)).image (fun k : ℕ => (k : ℤ))
  have hS : S.card = F.natDegree + d + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  refine ⟨S.filter (fun t => F.eval t ≠ 0), ?_, fun t ht => (Finset.mem_filter.1 ht).2⟩
  have hZ : (S.filter (fun t => ¬ F.eval t ≠ 0)).card ≤ F.natDegree := by
    refine card_le_degree_of_subset_roots fun z hz => ?_
    have hz' := (Finset.mem_filter.1 (show z ∈ S.filter (fun t => ¬ F.eval t ≠ 0) from hz)).2
    exact (mem_roots hF).2 (by simpa using hz')
  have := Finset.card_filter_add_card_filter_not (s := S) (fun t => F.eval t ≠ 0)
  omega

lemma natDegree_map_int (g : ℤ[X]) : (g.map (algebraMap ℤ ℚ)).natDegree = g.natDegree :=
  natDegree_map_eq_of_injective (RingHom.injective_int _) g

/-- **Kronecker's factor search** over `ℤ`, with a degree bound. -/
theorem kronecker_search {F : ℤ[X]} (hF : F ≠ 0) (d : ℕ) :
    (∃ G : ℚ[X], 0 < G.natDegree ∧ G.natDegree ≤ d ∧ G ∣ F.map (algebraMap ℤ ℚ)) ∨
      ∀ g : ℤ[X], g ∣ F → g.natDegree ≤ d → g.natDegree = 0 := by
  obtain ⟨T, hT, hTF⟩ := exists_nodes hF d
  let ι := {t // t ∈ T}
  let node : ι → ℚ := fun t => ((t : ℤ) : ℚ)
  have hinj : Set.InjOn node (Finset.univ : Finset ι) := fun a _ b _ h =>
    Subtype.ext (Int.cast_injective h)
  let interp : (ι → ℤ) → ℚ[X] := fun e =>
    Lagrange.interpolate Finset.univ node (fun t => ((e t : ℤ) : ℚ))
  let cands := Fintype.piFinset (fun t : ι => intDivisors (F.eval (t : ℤ)))
  let P : (ι → ℤ) → Prop := fun e =>
    0 < (interp e).natDegree ∧ (interp e).natDegree ≤ d ∧ interp e ∣ F.map (algebraMap ℤ ℚ)
  have hP : ∀ e, P e ∨ ¬ P e := by
    intro e
    rcases Decidable.em (0 < (interp e).natDegree) with h1 | h1
    · rcases Decidable.em ((interp e).natDegree ≤ d) with h2 | h2
      · rcases dvdDec_ratPoly (interp e) (F.map (algebraMap ℤ ℚ)) with h3 | h3
        · exact Or.inl ⟨h1, h2, h3⟩
        · exact Or.inr fun h => h3 h.2.2
      · exact Or.inr fun h => h2 h.2.1
    · exact Or.inr fun h => h1 h.1
  rcases Finset.exists_or_forall_not' cands hP with ⟨e, -, he⟩ | hn
  · exact Or.inl ⟨interp e, he⟩
  refine Or.inr fun g hg hgd => ?_
  -- `g` is the interpolant of its own values
  let e : ι → ℤ := fun t => g.eval (t : ℤ)
  have he : e ∈ cands := Fintype.mem_piFinset.2 fun t =>
    mem_intDivisors (hTF _ t.2) (eval_dvd hg)
  have hcard : (Finset.univ : Finset ι).card = T.card := by
    simp [ι]
  have hdeg : (g.map (algebraMap ℤ ℚ)).degree < (Finset.univ : Finset ι).card := by
    rw [hcard]
    refine (degree_le_natDegree).trans_lt ?_
    rw [natDegree_map_int]
    exact_mod_cast (show g.natDegree < T.card by omega)
  have hint : g.map (algebraMap ℤ ℚ) = interp e := by
    refine Lagrange.eq_interpolate_of_eval_eq _ hinj hdeg fun t _ => ?_
    simp [node, e, eval_map, eval₂_at_intCast]
  rcases Nat.eq_zero_or_pos g.natDegree with h0 | hpos
  · exact h0
  exfalso
  refine hn e he ⟨?_, ?_, ?_⟩
  · rw [← hint, natDegree_map_int]; exact hpos
  · rw [← hint, natDegree_map_int]; exact hgd
  · rw [← hint]; exact Polynomial.map_dvd _ hg

end Kronecker

section Gauss

/-- Clearing denominators. -/
lemma exists_int_multiple (p : ℚ[X]) :
    ∃ (q : ℤ[X]) (b : ℚ), b ≠ 0 ∧ q.map (algebraMap ℤ ℚ) = C b * p := by
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors ℤ) p, (b : ℚ),
    Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hb), ?_⟩
  rw [hq]; ext i; simp [zsmul_eq_mul]

/-- A rational divisor of `F` gives a primitive integral divisor of the same degree (Gauss). -/
lemma exists_int_dvd {F : ℤ[X]} {g : ℚ[X]} (hg : g ∣ F.map (algebraMap ℤ ℚ)) :
    ∃ g' : ℤ[X], g' ∣ F ∧ g'.natDegree = g.natDegree := by
  obtain ⟨q, b, hb, hq⟩ := exists_int_multiple g
  refine ⟨q.primPart, ?_, ?_⟩
  · refine (q.isPrimitive_primPart.dvd_iff_fraction_map_dvd_fraction_map ℚ).2 ?_
    refine (Polynomial.map_dvd _ q.primPart_dvd).trans ?_
    rw [hq]
    exact (((IsUnit.mk0 b hb).map C).mul_left_dvd).2 hg
  · rw [natDegree_primPart, ← natDegree_map_int, hq, natDegree_C_mul hb]

end Gauss

section Rat

/-- **Factor search** in `ℚ[X]` with a degree bound. -/
theorem factor_search {f : ℚ[X]} (hf : f ≠ 0) (d : ℕ) :
    (∃ g : ℚ[X], 0 < g.natDegree ∧ g.natDegree ≤ d ∧ g ∣ f) ∨
      ∀ g : ℚ[X], g ∣ f → g.natDegree ≤ d → g.natDegree = 0 := by
  obtain ⟨F, b, hb, hF⟩ := exists_int_multiple f
  have hCb : IsUnit (C b) := (IsUnit.mk0 b hb).map C
  have hF0 : F ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hF
    exact hf ((hCb.mul_right_eq_zero).1 hF.symm)
  have hdvd : ∀ {g : ℚ[X]}, g ∣ F.map (algebraMap ℤ ℚ) ↔ g ∣ f := by
    intro g; rw [hF]; exact hCb.dvd_mul_left
  rcases kronecker_search hF0 d with ⟨G, h1, h2, h3⟩ | hn
  · exact Or.inl ⟨G, h1, h2, hdvd.1 h3⟩
  refine Or.inr fun g hg hgd => ?_
  obtain ⟨g', hg', hdeg⟩ := exists_int_dvd (hdvd.2 hg)
  rw [← hdeg]
  exact hn g' hg' (hdeg ▸ hgd)

lemma isUnit_of_natDegree_eq_zero' {g : ℚ[X]} (hg : g ≠ 0) (h : g.natDegree = 0) : IsUnit g := by
  rw [eq_C_of_natDegree_eq_zero h] at hg ⊢
  exact (IsUnit.mk0 _ fun h0 => hg (by rw [h0, C_0])).map C

/-- **Decidable irreducibility** in `ℚ[X]`. -/
theorem irreducible_or_split {f : ℚ[X]} (hf : 0 < f.natDegree) :
    Irreducible f ∨ ∃ g h : ℚ[X], f = g * h ∧ 0 < g.natDegree ∧ 0 < h.natDegree := by
  have hf0 : f ≠ 0 := fun h => by rw [h, natDegree_zero] at hf; exact lt_irrefl 0 hf
  rcases factor_search hf0 (f.natDegree - 1) with ⟨g, h1, h2, ⟨h, hh⟩⟩ | hn
  · have hg0 : g ≠ 0 := fun h => by rw [h, natDegree_zero] at h1; exact lt_irrefl 0 h1
    have hh0 : h ≠ 0 := fun h' => hf0 (by rw [hh, h', mul_zero])
    have := natDegree_mul hg0 hh0
    rw [← hh] at this
    exact Or.inr ⟨g, h, hh, h1, by omega⟩
  refine Or.inl ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu; omega
  have ha0 : a ≠ 0 := fun h => hf0 (by rw [hab, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hf0 (by rw [hab, h, mul_zero])
  have hdeg := natDegree_mul ha0 hb0
  rw [← hab] at hdeg
  rcases Decidable.em (a.natDegree ≤ f.natDegree - 1) with hle | hle
  · exact Or.inl (isUnit_of_natDegree_eq_zero' ha0 (hn a ⟨b, hab⟩ hle))
  · exact Or.inr (isUnit_of_natDegree_eq_zero' hb0 (by omega))

/-- **Factorisation** in `ℚ[X]`: a unit times a product of irreducibles. -/
theorem exists_factorisation {f : ℚ[X]} (hf : f ≠ 0) :
    ∃ (u : ℚ[X]) (l : List ℚ[X]), IsUnit u ∧ (∀ p ∈ l, Irreducible p) ∧ f = u * l.prod := by
  suffices H : ∀ n, ∀ f : ℚ[X], f ≠ 0 → f.natDegree = n →
      ∃ (u : ℚ[X]) (l : List ℚ[X]), IsUnit u ∧ (∀ p ∈ l, Irreducible p) ∧ f = u * l.prod from
    H _ f hf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf hn
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · exact ⟨f, [], isUnit_of_natDegree_eq_zero' hf h0, by simp, by simp⟩
  rcases irreducible_or_split hpos with hirr | ⟨g, h, hgh, hg, hh⟩
  · exact ⟨1, [f], isUnit_one, by simpa using hirr, by simp⟩
  have hg0 : g ≠ 0 := fun h' => hf (by rw [hgh, h', zero_mul])
  have hh0 : h ≠ 0 := fun h' => hf (by rw [hgh, h', mul_zero])
  have hdeg := natDegree_mul hg0 hh0
  rw [← hgh] at hdeg
  obtain ⟨u, l, hu, hl, rfl⟩ := ih g.natDegree (by omega) g hg0 rfl
  obtain ⟨v, m, hv, hm, rfl⟩ := ih h.natDegree (by omega) h hh0 rfl
  refine ⟨u * v, l ++ m, hu.mul hv, fun p hp => ?_, ?_⟩
  · rcases List.mem_append.1 hp with hp | hp
    · exact hl p hp
    · exact hm p hp
  · rw [hgh, List.prod_append]; ring

/-- Every nonconstant `f` has an irreducible factor. -/
theorem exists_irreducible_dvd {f : ℚ[X]} (hf : 0 < f.natDegree) : ∃ p, Irreducible p ∧ p ∣ f := by
  suffices H : ∀ n, ∀ f : ℚ[X], 0 < f.natDegree → f.natDegree = n → ∃ p, Irreducible p ∧ p ∣ f from
    H _ f hf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf hn
  rcases irreducible_or_split hf with hirr | ⟨g, h, hgh, hg, hh⟩
  · exact ⟨f, hirr, dvd_rfl⟩
  have hf0 : f ≠ 0 := fun h => by rw [h, natDegree_zero] at hf; exact lt_irrefl 0 hf
  have hg0 : g ≠ 0 := fun h' => hf0 (by rw [hgh, h', zero_mul])
  have hh0 : h ≠ 0 := fun h' => hf0 (by rw [hgh, h', mul_zero])
  have hdeg := natDegree_mul hg0 hh0
  rw [← hgh] at hdeg
  obtain ⟨p, hp, hpg⟩ := ih g.natDegree (by omega) g hg rfl
  exact ⟨p, hp, hpg.trans ⟨h, hgh⟩⟩

/-- **(G2) data**: for `p` irreducible, `ℚ[X] ⧸ (p)` is a discrete field: every element is `0` or
a unit (positive form of maximality; Mathlib's `Ideal.IsMaximal` is not used, since `J = ⊤` from
`¬ J ≤ (p)` would need an element of `J` outside `(p)`). -/
theorem irreducible_quotient {p : ℚ[X]} (hp : Irreducible p) (x : ℚ[X] ⧸ Ideal.span {p}) :
    x = 0 ∨ IsUnit x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rcases dvdDec_ratPoly p a with h | h
  · exact Or.inl ((Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton.2 h))
  obtain ⟨u, v, huv⟩ := (hp.coprime_iff_not_dvd).2 h
  refine Or.inr (IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ v) ?_)
  have hp0 : Ideal.Quotient.mk (Ideal.span {p}) p = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton_self p)
  rw [← map_mul, mul_comm, show v * a = 1 - u * p by rw [← huv]; ring, map_sub, map_one, map_mul,
    hp0, mul_zero, sub_zero]

end Rat

end BezoutCounterexample.Constructive
