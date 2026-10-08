import Mathlib
import BezoutCounterexample.Principalization.Points
import BezoutCounterexample.Constructive.ChainLiftCertGlue

/-!
# Covers by points (Task B, Rees layer S6)

`exists_cover_of_pts`: if no explicit point of the presented ring `ℚ[Y] ⧸ (GR)` lies in the common zero
set of `e₁, …, e_J`, then a positive integer lies in `(e) + (GR)` over `ℤ`. Membership of `1` is
decided (`HasPres.mem_dec`); otherwise `HasPres.exists_pt` gives a point, contradicting the hypothesis.
This replaces composing the cover identities by hand (design §12).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive

/-- **A cover from points.** -/
theorem exists_cover_of_pts {N : ℕ} (GR : List (MvPolynomial (Fin N) ℤ)) {J : ℕ}
    (e : Fin J → MvPolynomial (Fin N) ℤ)
    (h : ∀ P : Pt (MvPolynomial (Fin N) ℚ ⧸ lspan (GR.map toQZ)),
      ∃ j, Ideal.Quotient.mk (lspan (GR.map toQZ)) (toQZ (e j)) ∉ P.ker) :
    ∃ C : ℕ, 0 < C ∧ (C : MvPolynomial (Fin N) ℤ) ∈ Ideal.span (Set.range e) ⊔ lspan GR := by
  set I := lspan (GR.map toQZ)
  have hp : HasPres (MvPolynomial (Fin N) ℚ ⧸ I) := ⟨N, GR.map toQZ, ⟨RingEquiv.refl _⟩⟩
  set l : List (MvPolynomial (Fin N) ℚ ⧸ I) := List.ofFn fun j => Ideal.Quotient.mk I (toQZ (e j))
  rcases hp.mem_dec l 1 with h1 | h1
  · -- lift `1 ∈ (ē)` to `1 ∈ (GR, e)` over `ℚ`, then clear to `ℤ`
    have hl : lspan l = (lspan (List.ofFn fun j => toQZ (e j))).map (Ideal.Quotient.mk I) := by
      rw [lspan, lspan, Ideal.map_span]
      congr 1
      ext x
      simp [l]
    rw [hl, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    obtain ⟨y, hy, hy1⟩ := h1
    have h1' : toQZ (1 : MvPolynomial (Fin N) ℤ) ∈ lspan ((GR ++ List.ofFn e).map toQZ) := by
      rw [map_one, show (1 : MvPolynomial (Fin N) ℚ) = (1 - y) + y by ring]
      have hsub : (1 : MvPolynomial (Fin N) ℚ) - y ∈ I := by
        rw [← Ideal.Quotient.eq, map_one, hy1]
      refine add_mem (Ideal.span_mono (fun x hx => ?_) hsub) (Ideal.span_mono (fun x hx => ?_) hy)
      · simp only [Set.mem_ofPred_eq, List.map_append, List.mem_append] at hx ⊢
        exact Or.inl hx
      · simp only [Set.mem_ofPred_eq, List.map_append, List.mem_append, List.map_ofFn,
          List.mem_ofFn] at hx ⊢
        obtain ⟨j, rfl⟩ := hx
        exact Or.inr ⟨j, rfl⟩
    obtain ⟨D, hD, hDm⟩ := int_mem _ _ h1'
    refine ⟨D, hD, ?_⟩
    rw [mul_one] at hDm
    refine (Ideal.span_le.2 ?_ : lspan (GR ++ List.ofFn e) ≤ _) hDm
    intro x hx
    simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_ofFn] at hx
    rcases hx with hx | ⟨j, rfl⟩
    · exact Ideal.mem_sup_right (Ideal.subset_span hx)
    · exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)
  · exfalso
    obtain ⟨P, hP⟩ := HasPres.exists_pt hp l h1
    obtain ⟨j, hj⟩ := h P
    exact hj (hP (Ideal.subset_span (List.mem_ofFn.2 ⟨j, rfl⟩)))

end BezoutCounterexample.Principalization
