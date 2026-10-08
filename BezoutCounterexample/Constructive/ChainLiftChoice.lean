import Mathlib

/-!
# Finite choice (Task B, S2/S3)

Choice over a finite index type, by induction on `Fin m` and an enumeration `ι ≃ Fin n`
(`Finite.exists_equiv_fin`, which is the definition of `Finite`, used inside proofs of `Prop`s).
No axiom of choice and no decidable equality. These replace `Classical.choice`/`choose` over finite
index sets in the bridge files.

* `fin_nonempty_pi`, `finite_nonempty_pi`: `(∀ i, Nonempty (X i)) → Nonempty (∀ i, X i)`.
* `finite_choice_dep`: `(∀ i, ∃ a : α i, P i a) → ∃ f, ∀ i, P i (f i)`.
* `finite_choice`: the non-dependent case (compare `ChainLiftMinorPoly.fintype_choice`, which asks
  for `Fintype` and `DecidableEq`).
-/

namespace BezoutCounterexample.Constructive

/-- Finite choice of inhabitants over `Fin m`. -/
theorem fin_nonempty_pi : ∀ {m : ℕ} {X : Fin m → Sort*}, (∀ j, Nonempty (X j)) →
    Nonempty (∀ j, X j)
  | 0, _, _ => ⟨fun j => j.elim0⟩
  | _ + 1, X, h => by
    obtain ⟨a⟩ := h 0
    obtain ⟨f⟩ := fin_nonempty_pi (X := fun j => X j.succ) fun j => h j.succ
    exact ⟨Fin.cons a f⟩

/-- Finite choice of inhabitants over a finite type. -/
theorem finite_nonempty_pi {ι : Type*} [Finite ι] {X : ι → Sort*}
    (h : ∀ i, Nonempty (X i)) : Nonempty (∀ i, X i) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨g⟩ := fin_nonempty_pi (X := fun j => X (e.symm j)) fun j => h _
  exact ⟨fun i => e.symm_apply_apply i ▸ g (e i)⟩

/-- **Finite choice** (dependent) over a finite type. -/
theorem finite_choice_dep {ι : Type*} [Finite ι] {α : ι → Sort*}
    {P : ∀ i, α i → Prop} (h : ∀ i, ∃ a, P i a) : ∃ f : ∀ i, α i, ∀ i, P i (f i) := by
  obtain ⟨g⟩ := finite_nonempty_pi (X := fun i => {a // P i a}) fun i =>
    let ⟨a, ha⟩ := h i; ⟨⟨a, ha⟩⟩
  exact ⟨fun i => (g i).1, fun i => (g i).2⟩

/-- **Finite choice** over a finite type. -/
theorem finite_choice {ι α : Type*} [Finite ι] {P : ι → α → Prop} (h : ∀ i, ∃ a, P i a) :
    ∃ f : ι → α, ∀ i, P i (f i) :=
  finite_choice_dep h

end BezoutCounterexample.Constructive
