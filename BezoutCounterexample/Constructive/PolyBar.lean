import BezoutCounterexample.Constructive.NoethBar
import BezoutCounterexample.Constructive.AlmostFull
import BezoutCounterexample.Constructive.TopReduce

/-!
# `ℚ[Y₁, …, Y_N]` is inductively Noetherian (Coquand–Persson)

Induction on Dickson's lemma in almost-full form (`af_finsupp_le`). Along the bar we keep, besides
the list `l` of polynomials read so far, the list `G ⊆ (l)` of nonzero remainders produced so far,
with the invariant

  `T x y → x ≤ y ∨ DvG G x`,   `DvG G x :≡ ∃ g ∈ G, lm g ∣ x`.

Each bar step reads one polynomial `a` and top-reduces it by `G` (`top_reduce`): either the
remainder is `0`, so `a ∈ (G) ⊆ (l)` (good), or it is a nonzero `r` whose leading monomial `m` is
outside `DvG G`; then lifting `T` by `m` keeps the invariant for `a :: l` and `r :: G`.

Only division by the finite list `G` is used: `G` need not be a Gröbner basis of `(l)`, so no
Buchberger algorithm and no normal form modulo `(l)` is needed. Fully constructive.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {N : ℕ}

lemma DvG.cons {G : List (MvPolynomial (Fin N) ℚ)} {x : Fin N →₀ ℕ} (r : MvPolynomial (Fin N) ℚ)
    (h : DvG G x) : DvG (r :: G) x := by
  obtain ⟨g, hg, hle⟩ := h
  exact ⟨g, List.mem_cons_of_mem r hg, hle⟩

lemma lspan_le_cons (l : List (MvPolynomial (Fin N) ℚ)) (a : MvPolynomial (Fin N) ℚ) :
    lspan l ≤ lspan (a :: l) :=
  Ideal.span_mono fun _ hz => List.mem_cons_of_mem a hz

/-- **The bar induction.** -/
theorem nbar_of_af {T : (Fin N →₀ ℕ) → (Fin N →₀ ℕ) → Prop} (hT : AF T) :
    ∀ (l G : List (MvPolynomial (Fin N) ℚ)), (∀ g ∈ G, g ∈ lspan l ∧ g ≠ 0) →
      (∀ x y, T x y → x ≤ y ∨ DvG G x) → NBar l := by
  induction hT with
  | now hT =>
    intro l G hG hl
    refine NBar.step fun a => ?_
    have hGl : lspan G ≤ lspan l := Ideal.span_le.2 fun g hg => (hG g hg).1
    rcases top_reduce G (fun g hg => (hG g hg).2) a with ⟨r, hr, h0 | ⟨hr0, hdv⟩⟩
    · rw [h0, sub_zero] at hr
      exact NBar.good (hGl hr)
    -- `r` is a nonzero constant in `(a :: l)`
    have hdeg : (mo N).degree r = 0 := by
      rcases hl _ 0 (hT _ _) with h | h
      · exact le_antisymm h zero_le
      · exact absurd h hdv
    have hmem : r ∈ lspan (a :: l) := by
      have ha : a ∈ lspan (a :: l) := Ideal.subset_span List.mem_cons_self
      have := sub_mem ha (lspan_le_cons l a (hGl hr))
      rwa [sub_sub_cancel] at this
    refine NBar.step fun b => NBar.good ?_
    exact (Ideal.span_le.2 fun z hz => by rw [Set.mem_singleton_iff.1 hz]; exact hmem)
      (mem_span_of_degree_eq_zero hr0 hdeg b)
  | up _ ih =>
    intro l G hG hl
    refine NBar.step fun a => ?_
    have hGl : lspan G ≤ lspan l := Ideal.span_le.2 fun g hg => (hG g hg).1
    rcases top_reduce G (fun g hg => (hG g hg).2) a with ⟨r, hr, h0 | ⟨hr0, hdv⟩⟩
    · rw [h0, sub_zero] at hr
      exact NBar.good (hGl hr)
    have hmem : r ∈ lspan (a :: l) := by
      have ha : a ∈ lspan (a :: l) := Ideal.subset_span List.mem_cons_self
      have := sub_mem ha (lspan_le_cons l a (hGl hr))
      rwa [sub_sub_cancel] at this
    refine ih ((mo N).degree r) (a :: l) (r :: G) ?_ fun x y h => ?_
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨hmem, hr0⟩
      · exact ⟨lspan_le_cons l a (hG g hg).1, (hG g hg).2⟩
    rcases h with h | h
    · exact (hl x y h).imp_right (DvG.cons r)
    · rcases hl _ x h with h | h
      · exact Or.inr ⟨r, List.mem_cons_self, h⟩
      · exact absurd h hdv

/-- **Hilbert basis theorem**, inductive form, for `ℚ[Y₁, …, Y_N]`. -/
theorem polyBar : PolyBar := fun N =>
  nbar_of_af (af_finsupp_le N) [] [] (fun _ h => absurd h List.not_mem_nil)
    fun _ _ h => Or.inl h

end BezoutCounterexample.Constructive
