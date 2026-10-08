import BezoutCounterexample.Constructive.NoethBar

/-!
# Explicit generators of a transform (leaf; gens threading along HM's tower)

`exists_gens_of_map_eq_mul`: if `I = (gens)` and `I R = (x) J` in a domain `R` with `x ≠ 0`, then
`J = (gens')` explicitly: write `f gᵢ = x hᵢ` with `hᵢ ∈ J`, and cancel `x`. Used for the divisorial
transform `I = (π^a) I₁` and the torsor transform `I U = (s^d) I₁`.
-/

namespace BezoutCounterexample.Constructive

/-- **Generators of a transform.** -/
theorem exists_gens_of_map_eq_mul {A R : Type*} [CommRing A] [CommRing R] [IsDomain R]
    (f : A →+* R) {I : Ideal A} {gens : List A} (hI : I = lspan gens) {x : R} (hx : x ≠ 0)
    {J : Ideal R} (h : I.map f = Ideal.span {x} * J) : ∃ gens' : List R, J = lspan gens' := by
  have key : ∀ l : List A, (∀ g ∈ l, f g ∈ Ideal.span {x} * J) →
      ∃ hs : List R, (∀ y ∈ hs, y ∈ J) ∧ ∀ g ∈ l, ∃ y ∈ hs, f g = x * y := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨[], fun _ h => absurd h List.not_mem_nil,
        fun _ h => absurd h List.not_mem_nil⟩
    | cons a l ih =>
      intro hl
      obtain ⟨hs, hJ, hg⟩ := ih fun g hg => hl g (List.mem_cons_of_mem _ hg)
      obtain ⟨z, hz, hza⟩ := Ideal.mem_span_singleton_mul.1 (hl a List.mem_cons_self)
      refine ⟨z :: hs, fun y hy => ?_, fun g hg' => ?_⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hz
        · exact hJ y hy
      · rcases List.mem_cons.1 hg' with rfl | hg'
        · exact ⟨z, List.mem_cons_self, hza.symm⟩
        · obtain ⟨y, hy, e⟩ := hg g hg'
          exact ⟨y, List.mem_cons_of_mem _ hy, e⟩
  obtain ⟨hs, hJ, hg⟩ := key gens fun g hg => h ▸ Ideal.mem_map_of_mem f (hI ▸ Ideal.subset_span hg)
  refine ⟨hs, le_antisymm ?_ ?_⟩
  · rw [← Ideal.span_singleton_mul_right_mono hx, ← h, hI, lspan, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨g, hg', rfl⟩
    obtain ⟨y, hy, e⟩ := hg g hg'
    rw [SetLike.mem_coe, e]
    exact Ideal.mem_span_singleton_mul.2 ⟨y, Ideal.subset_span hy, rfl⟩
  · rw [lspan, Ideal.span_le]
    exact fun y hy => hJ y hy

end BezoutCounterexample.Constructive
