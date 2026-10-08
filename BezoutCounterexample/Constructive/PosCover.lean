import BezoutCounterexample.Constructive.NoethBar

/-!
# Positive covers by bar induction (`~/COLL/bezout-positive.tex`, Theorem 1.3)

Let `I` be an ideal of `A` with `A ⧸ I` inductively Noetherian, `P` a property of elements
("`D(g)` carries a certificate"), and suppose:

* (G) membership of `1` in `I + (l)` is decidable for finite lists `l`;
* (step) whenever the certified list `l` does not yet cover (`1 ∉ I + (l)`), some certified `g`
  lies outside `I + (l)`. In the application `g` comes from a certificate computed at an explicit
  point `z ∈ V(I + (l))` with `z(g) ≠ 0` (Nullstellensatz with explicit points), which is why
  `g ∉ I + (l)`.

Then some certified list covers: `1 ∈ I + (l)` (`exists_cover`). This is the old "Noetherian
induction on closed subsets of `V(I)`", with the bar in place of both the descending chain
condition and its `¬¬` form: the images of the chosen `g` in `A ⧸ I` never form a good list,
since each new entry avoids the ideal of the older ones. No `¬¬`, no Markov, no choice: each
step produces one element. Replaces `NNMax` / `not_not_one_mem_cert` of `Cover.lean`.
-/

namespace BezoutCounterexample.Constructive

variable {A : Type*} [CommRing A]

/-- Membership in the ideal of an image list in `A ⧸ I`. -/
lemma mem_I_sup_of_mk_mem (I : Ideal A) {g : A} {l : List A}
    (h : Ideal.Quotient.mk I g ∈ lspan (l.map (Ideal.Quotient.mk I))) : g ∈ I ⊔ lspan l := by
  have hmap : lspan (l.map (Ideal.Quotient.mk I)) = (lspan l).map (Ideal.Quotient.mk I) := by
    rw [lspan, lspan, Ideal.map_span]
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact List.mem_map.2 ⟨y, hy, rfl⟩
  rw [hmap] at h
  have h2 := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h
  obtain ⟨x, hx, hxg⟩ := h2
  have hgx : g - x ∈ I := Ideal.Quotient.eq.1 hxg.symm
  have : g = (g - x) + x := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left hgx) (Ideal.mem_sup_right hx)

/-- The bar invariant: the images of a fresh certified list. -/
theorem NBar.exists_cover (I : Ideal A) (P : A → Prop)
    (hdec : ∀ l : List A, (1 : A) ∈ I ⊔ lspan l ∨ (1 : A) ∉ I ⊔ lspan l)
    (hstep : ∀ l : List A, (∀ g ∈ l, P g) → (1 : A) ∉ I ⊔ lspan l →
      ∃ g, P g ∧ g ∉ I ⊔ lspan l)
    {L : List (A ⧸ I)} (hL : NBar L) :
    ∀ l : List A, L = l.map (Ideal.Quotient.mk I) → (∀ g ∈ l, P g) →
      (∀ g l₀, l = g :: l₀ → g ∉ I ⊔ lspan l₀) →
      ∃ l' : List A, (∀ g ∈ l', P g) ∧ (1 : A) ∈ I ⊔ lspan l' := by
  induction hL with
  | @good a L₀ ha =>
    intro l hl _ hfresh
    exfalso
    cases l with
    | nil => exact List.cons_ne_nil _ _ hl
    | cons g l₀ =>
      obtain ⟨hag, hL₀⟩ := List.cons.inj hl
      rw [hag, hL₀] at ha
      exact hfresh g l₀ rfl (mem_I_sup_of_mk_mem I ha)
  | @step L₀ _ ih =>
    intro l hl hP _
    rcases hdec l with h1 | h1
    · exact ⟨l, hP, h1⟩
    · obtain ⟨g, hg, hgl⟩ := hstep l hP h1
      refine ih (Ideal.Quotient.mk I g) (g :: l) (by rw [hl]; rfl) ?_ ?_
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hg
        · exact hP x hx
      · intro g' l₀ h
        obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact hgl

/-- **Positive covers by bar induction.** -/
theorem exists_cover (I : Ideal A) (hN : IndNoeth (A ⧸ I)) (P : A → Prop)
    (hdec : ∀ l : List A, (1 : A) ∈ I ⊔ lspan l ∨ (1 : A) ∉ I ⊔ lspan l)
    (hstep : ∀ l : List A, (∀ g ∈ l, P g) → (1 : A) ∉ I ⊔ lspan l →
      ∃ g, P g ∧ g ∉ I ⊔ lspan l) :
    ∃ l : List A, (∀ g ∈ l, P g) ∧ (1 : A) ∈ I ⊔ lspan l :=
  NBar.exists_cover I P hdec hstep hN [] rfl (fun _ h => absurd h List.not_mem_nil)
    (fun _ _ h => absurd h (List.cons_ne_nil _ _).symm)

end BezoutCounterexample.Constructive
