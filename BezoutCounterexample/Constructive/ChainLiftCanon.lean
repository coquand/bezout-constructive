import Mathlib
import BezoutCounterexample.Constructive.ChainLiftUnique
import BezoutCounterexample.Constructive.NoethBar

/-!
# Canonical generators of finitely generated ideals (Task A, C2)

For a ring `R` with an enumeration `en : ℕ → R` (C1: `enumQuo` transported along a presentation)
and decidable membership in finitely generated ideals (`HasPres.mem_dec`), every finitely generated
ideal `I` gets a **canonical** generating list, a function of `I` alone:

* `canonIdx I hI`: the indices `k < n` with `en k ∈ I`, where `n` is the least length such that
  these elements generate `I` (`Nat.find`; the bound comes from explicit preimages of the
  generators of a list `L` with `I = lspan L`, so no Markov step is involved; `L` enters only through
  Props, and the decisions are read through `decOfOr`);
* `canonGens I hI := (canonIdx I hI).map en`, `lspan_canonGens : lspan (canonGens I hI) = I`;
* `canonIdx_injective`: so `I ≤χ J :↔ List.le (canonIdx I) (canonIdx J)` (core's lexicographic order,
  decided by the axiom-free `List.decidableLE`) is a decidable total order on finitely generated
  ideals, and a finite set of them has a unique `≤χ`-minimum (`existsUnique_canonMin`). (Not Mathlib's
  `LinearOrder (List ℕ)`: it takes its decidability from `linearOrderOfSTO`, i.e. classically.)
-/

namespace BezoutCounterexample.Constructive

variable {R : Type*} [CommRing R] (en : ℕ → R) (hen : Function.Surjective en)
  (dec : ∀ (L : List R) (x : R), x ∈ lspan L ∨ x ∉ lspan L)

/-- Membership in a finitely generated ideal, as `Decidable` (unique choice). -/
noncomputable def memDec (I : Ideal R) (hI : ∃ L : List R, I = lspan L) (x : R) :
    Decidable (x ∈ I) :=
  decOfOr (by obtain ⟨L, rfl⟩ := hI; exact dec L x)

/-- The enumerated elements of `I` among the first `n`. -/
noncomputable def prefixIdx (I : Ideal R) (hI : ∃ L : List R, I = lspan L) (n : ℕ) : List ℕ :=
  (List.range n).filter fun k => @decide (en k ∈ I) (memDec dec I hI (en k))

omit hen in
lemma mem_prefixIdx {I : Ideal R} {hI : ∃ L : List R, I = lspan L} {n k : ℕ} :
    k ∈ prefixIdx en dec I hI n ↔ k < n ∧ en k ∈ I := by
  rw [prefixIdx, List.mem_filter, List.mem_range]
  exact and_congr_right fun _ => @decide_eq_true_iff _ (memDec dec I hI (en k))

/-- Decided finite conjunctions over a list. -/
lemma list_forall_dec {α : Type*} (L : List α) (p : α → Prop) (hp : ∀ a, p a ∨ ¬ p a) :
    (∀ a ∈ L, p a) ∨ ¬ ∀ a ∈ L, p a := by
  induction L with
  | nil => exact Or.inl fun a h => absurd h List.not_mem_nil
  | cons b L ih =>
    rcases hp b with hb | hb
    · rcases ih with h | h
      · exact Or.inl fun a ha => (List.mem_cons.1 ha).elim (fun e => e ▸ hb) (h a)
      · exact Or.inr fun h' => h fun a ha => h' a (List.mem_cons_of_mem _ ha)
    · exact Or.inr fun h' => hb (h' b List.mem_cons_self)

/-- The spanning property of a prefix. -/
def Spans (I : Ideal R) (hI : ∃ L : List R, I = lspan L) (n : ℕ) : Prop :=
  I ≤ lspan ((prefixIdx en dec I hI n).map en)

lemma spans_dec (I : Ideal R) (hI : ∃ L : List R, I = lspan L) (n : ℕ) :
    Spans en dec I hI n ∨ ¬ Spans en dec I hI n := by
  obtain ⟨L, hL⟩ := hI
  have key : Spans en dec I ⟨L, hL⟩ n ↔ ∀ a ∈ L, a ∈ lspan ((prefixIdx en dec I ⟨L, hL⟩ n).map en) := by
    constructor
    · intro h a ha; exact h (hL ▸ Ideal.subset_span ha)
    · intro h; exact hL.le.trans (Ideal.span_le.2 fun a ha => h a ha)
  rcases list_forall_dec L _ (fun a => dec _ a) with h | h
  · exact Or.inl (key.2 h)
  · exact Or.inr fun h' => h (key.1 h')

include hen

/-- Explicit bound: the preimages of the generators. -/
lemma exists_spans (I : Ideal R) (hI : ∃ L : List R, I = lspan L) : ∃ n, Spans en dec I hI n := by
  obtain ⟨L, hL⟩ := hI
  have hbound : ∀ L' : List R, (∀ a ∈ L', a ∈ I) →
      ∃ n, ∀ a ∈ L', a ∈ (prefixIdx en dec I ⟨L, hL⟩ n).map en := by
    intro L' hL'
    induction L' with
    | nil => exact ⟨0, fun a h => absurd h List.not_mem_nil⟩
    | cons b L' ih =>
      obtain ⟨n, hn⟩ := ih fun a ha => hL' a (List.mem_cons_of_mem _ ha)
      obtain ⟨k, hk⟩ := hen b
      refine ⟨n + k + 1, fun a ha => ?_⟩
      rcases List.mem_cons.1 ha with rfl | ha
      · exact List.mem_map.2 ⟨k, (mem_prefixIdx en dec).2 ⟨by omega, hk ▸ hL' _ List.mem_cons_self⟩, hk⟩
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (hn a ha)
        obtain ⟨hjn, hjI⟩ := (mem_prefixIdx en dec).1 hj
        exact List.mem_map.2 ⟨j, (mem_prefixIdx en dec).2 ⟨by omega, hjI⟩, rfl⟩
  obtain ⟨n, hn⟩ := hbound L fun a ha => hL ▸ Ideal.subset_span ha
  exact ⟨n, hL.le.trans (Ideal.span_le.2 fun a ha => Ideal.subset_span (hn a ha))⟩

/-- The least spanning length. -/
noncomputable def canonLen (I : Ideal R) (hI : ∃ L : List R, I = lspan L) : ℕ :=
  @Nat.find (Spans en dec I hI) (fun n => decOfOr (spans_dec en dec I hI n))
    (exists_spans en hen dec I hI)

/-- **The canonical index list** of a finitely generated ideal. -/
noncomputable def canonIdx (I : Ideal R) (hI : ∃ L : List R, I = lspan L) : List ℕ :=
  prefixIdx en dec I hI (canonLen en hen dec I hI)

/-- **The canonical generators** of a finitely generated ideal. -/
noncomputable def canonGens (I : Ideal R) (hI : ∃ L : List R, I = lspan L) : List R :=
  (canonIdx en hen dec I hI).map en

theorem lspan_canonGens (I : Ideal R) (hI : ∃ L : List R, I = lspan L) :
    lspan (canonGens en hen dec I hI) = I := by
  apply le_antisymm
  · rw [lspan, Ideal.span_le]
    intro a ha
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
    exact ((mem_prefixIdx en dec).1 hk).2
  · exact @Nat.find_spec (Spans en dec I hI) (fun n => decOfOr (spans_dec en dec I hI n))
      (exists_spans en hen dec I hI)

theorem canonIdx_injective {I J : Ideal R} (hI : ∃ L : List R, I = lspan L)
    (hJ : ∃ L : List R, J = lspan L) (h : canonIdx en hen dec I hI = canonIdx en hen dec J hJ) :
    I = J := by
  rw [← lspan_canonGens en hen dec I hI, ← lspan_canonGens en hen dec J hJ, canonGens, canonGens, h]

/-- **The canonical minimum** of a finite nonempty family of finitely generated ideals, for the
order `I ≤χ J :↔ List.le (canonIdx I) (canonIdx J)`: unique, so it can be extracted by unique choice. -/
theorem existsUnique_canonMin (S : Set (Ideal R)) (Ls : List (List R)) (hne : Ls ≠ [])
    (hS : ∀ P, P ∈ S ↔ ∃ L ∈ Ls, lspan L = P) :
    ∃! P : Ideal R, ∃ (hP : P ∈ S), ∀ (Q : Ideal R) (hQ : Q ∈ S),
      List.le (canonIdx en hen dec P (by obtain ⟨L, -, rfl⟩ := (hS P).1 hP; exact ⟨L, rfl⟩))
        (canonIdx en hen dec Q (by obtain ⟨L, -, rfl⟩ := (hS Q).1 hQ; exact ⟨L, rfl⟩)) := by
  -- the minimum over the list `Ls`
  have hmin : ∀ Ls' : List (List R), Ls' ≠ [] → ∃ L₀ ∈ Ls', ∀ L ∈ Ls',
      List.le (canonIdx en hen dec (lspan L₀) ⟨L₀, rfl⟩) (canonIdx en hen dec (lspan L) ⟨L, rfl⟩) := by
    intro Ls' hLs'
    induction Ls' with
    | nil => exact absurd rfl hLs'
    | cons L₁ Ls' ih =>
      rcases Ls' with _ | ⟨L₂, Ls''⟩
      · exact ⟨L₁, List.mem_cons_self, fun L hL => by
          rw [List.mem_singleton.1 hL]; exact List.le_refl _⟩
      · obtain ⟨L₀, hL₀, hL₀min⟩ := ih (List.cons_ne_nil _ _)
        rcases List.le_total (canonIdx en hen dec (lspan L₁) ⟨L₁, rfl⟩)
            (canonIdx en hen dec (lspan L₀) ⟨L₀, rfl⟩) with h | h
        · refine ⟨L₁, List.mem_cons_self, fun L hL => ?_⟩
          rcases List.mem_cons.1 hL with rfl | hL
          · exact List.le_refl _
          · exact List.le_trans h (hL₀min L hL)
        · refine ⟨L₀, List.mem_cons_of_mem _ hL₀, fun L hL => ?_⟩
          rcases List.mem_cons.1 hL with rfl | hL
          · exact h
          · exact hL₀min L hL
  obtain ⟨L₀, hL₀, hL₀min⟩ := hmin Ls hne
  have hP₀ : lspan L₀ ∈ S := (hS _).2 ⟨L₀, hL₀, rfl⟩
  refine ⟨lspan L₀, ⟨hP₀, fun Q hQ => ?_⟩, fun P ⟨hP, hPmin⟩ => ?_⟩
  · obtain ⟨L, hL, rfl⟩ := (hS Q).1 hQ
    exact hL₀min L hL
  · obtain ⟨L, hL, rfl⟩ := (hS P).1 hP
    exact canonIdx_injective en hen dec ⟨L, rfl⟩ ⟨L₀, rfl⟩
      (List.le_antisymm (hPmin _ hP₀) (hL₀min L hL))

end BezoutCounterexample.Constructive
