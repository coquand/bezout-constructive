import BezoutCounterexample.Constructive.NoethBar

/-!
# Top reduction by a finite list over `ℚ`

`top_reduce`: for a finite list `G` of nonzero polynomials in `ℚ[Y₁, …, Y_N]` and any `f`, there is
`r ≡ f mod (G)` which is either `0` or has leading monomial (lex) divisible by no leading monomial
of `G`. Well-founded induction on the lex degree; each step decides `f = 0` and the finite search
`∃ g ∈ G, lm g ∣ lm f` (decidable equality of `ℚ`, decidable `≤` on `ℕ`), and subtracts one
monomial multiple of `g` (`MonomialOrder.reduce`).

This is the only algorithm the Hilbert basis theorem (`PolyBar.lean`) needs: the list `G` is the
list of remainders produced so far, not a Gröbner basis of the ideal, so Buchberger's algorithm
does not enter.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {N : ℕ}

/-- The lexicographic monomial order on `Fin N`. -/
noncomputable abbrev mo (N : ℕ) : MonomialOrder (Fin N) := MonomialOrder.lex

/-- Some element of the list `G` has leading monomial dividing `x`. -/
def DvG (G : List (MvPolynomial (Fin N) ℚ)) (x : Fin N →₀ ℕ) : Prop :=
  ∃ g ∈ G, (mo N).degree g ≤ x

/-- A nonzero polynomial of degree `0` divides everything. -/
lemma mem_span_of_degree_eq_zero {g : MvPolynomial (Fin N) ℚ} (hg0 : g ≠ 0)
    (hg : (mo N).degree g = 0) (f : MvPolynomial (Fin N) ℚ) :
    f ∈ Ideal.span {g} := by
  have hgC := (mo N).eq_C_of_degree_eq_zero hg
  have hlc : (mo N).leadingCoeff g ≠ 0 := (mo N).leadingCoeff_ne_zero_iff.2 hg0
  generalize (mo N).leadingCoeff g = c at hgC hlc
  have : f = (f * C c⁻¹) * g := by
    rw [hgC, mul_assoc, ← map_mul, inv_mul_cancel₀ hlc, map_one, mul_one]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

lemma span_singleton_le_lspan {G : List (MvPolynomial (Fin N) ℚ)} {g : MvPolynomial (Fin N) ℚ}
    (hg : g ∈ G) : Ideal.span {g} ≤ lspan G :=
  Ideal.span_mono fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hg

/-- **Top reduction** by a finite list of nonzero polynomials. -/
theorem top_reduce (G : List (MvPolynomial (Fin N) ℚ)) (hG : ∀ g ∈ G, g ≠ 0)
    (f : MvPolynomial (Fin N) ℚ) :
    ∃ r, f - r ∈ lspan G ∧ (r = 0 ∨ (r ≠ 0 ∧ ¬ DvG G ((mo N).degree r))) := by
  suffices H : ∀ d : (mo N).syn, ∀ f : MvPolynomial (Fin N) ℚ,
      (mo N).toSyn ((mo N).degree f) = d →
        ∃ r, f - r ∈ lspan G ∧ (r = 0 ∨ (r ≠ 0 ∧ ¬ DvG G ((mo N).degree r))) from
    H _ f rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
  intro f hfd
  if hf : f = 0 then
    exact ⟨0, by rw [hf, sub_zero]; exact zero_mem _, Or.inl rfl⟩
  else if hdv : ∃ g ∈ G, (mo N).degree g ≤ (mo N).degree f then
    obtain ⟨g, hgG, hgf⟩ := hdv
    have hg0 := hG g hgG
    if hdeg : (mo N).degree f = 0 then
      -- `g` is a nonzero constant
      have hg : (mo N).degree g = 0 := le_antisymm (hdeg ▸ hgf) zero_le
      refine ⟨0, ?_, Or.inl rfl⟩
      rw [sub_zero]
      exact span_singleton_le_lspan hgG (mem_span_of_degree_eq_zero hg0 hg f)
    else
      have hb : IsUnit ((mo N).leadingCoeff g) :=
        isUnit_iff_ne_zero.2 ((mo N).leadingCoeff_ne_zero_iff.2 hg0)
      have hlt := (mo N).degree_reduce_lt hb hgf hdeg
      obtain ⟨r, hr, hr'⟩ := ih _ (hfd ▸ hlt) ((mo N).reduce hb f) rfl
      refine ⟨r, ?_, hr'⟩
      have hq : f - (mo N).reduce hb f ∈ lspan G := by
        rw [MonomialOrder.reduce, sub_sub_cancel]
        exact span_singleton_le_lspan hgG (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
      have := add_mem hq hr
      rwa [sub_add_sub_cancel] at this
  else
    exact ⟨f, by rw [sub_self]; exact zero_mem _, Or.inr ⟨hf, hdv⟩⟩

end BezoutCounterexample.Constructive
