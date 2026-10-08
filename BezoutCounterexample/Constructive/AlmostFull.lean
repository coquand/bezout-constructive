import Mathlib

/-!
# Almost-full relations and Dickson's lemma (inductive form)

Following Vytiniotis–Coquand–Wahlstedt (*Stop when you are almost-full*, ITP 2012), after
Coquand's intuitionistic Ramsey theorem: `AF R` is the inductive predicate

* `AF R` if `R` is total;
* `AF R` if `AF (R↑a)` for all `a`, where `(R↑a) x y := R x y ∨ R a x`.

No sequences, no choice. Closure under intersection (`AF.inter`) goes through three lemmas
`oplus₀`, `oplus₁`, `oplus₂` (nullary, unary, binary side conditions), each a single induction.
`af_nat_le` is `AF (≤)` on `ℕ` (a decidable comparison per step), and `af_finsupp_le` is Dickson's
lemma: `AF (≤)` on `Fin N →₀ ℕ`.
-/

namespace BezoutCounterexample.Constructive

universe u

variable {X : Type u}

/-- Almost-full relations, inductively. -/
inductive AF : (X → X → Prop) → Prop
  | now {R : X → X → Prop} : (∀ x y, R x y) → AF R
  | up {R : X → X → Prop} : (∀ a, AF (fun x y => R x y ∨ R a x)) → AF R

namespace AF

theorem mono {R : X → X → Prop} (h : AF R) :
    ∀ {S : X → X → Prop}, (∀ x y, R x y → S x y) → AF S := by
  induction h with
  | now hR => exact fun hRS => AF.now fun x y => hRS x y (hR x y)
  | up _ ih =>
    intro S hRS
    exact AF.up fun a => ih a fun x y h => h.elim (fun h => Or.inl (hRS x y h))
      (fun h => Or.inr (hRS a x h))

/-- Pullback along a map. -/
theorem comap {Y : Type*} {R : X → X → Prop} (h : AF R) (f : Y → X) :
    AF (fun x y => R (f x) (f y)) := by
  induction h with
  | now hR => exact AF.now fun x y => hR _ _
  | up _ ih => exact AF.up fun a => ih (f a)

/-- Nullary side conditions. -/
theorem oplus₀ {T₁ : X → X → Prop} (h₁ : AF T₁) :
    ∀ {T₂ : X → X → Prop}, AF T₂ → ∀ {R : X → X → Prop} {A B : Prop},
      (∀ x y, T₁ x y → R x y ∨ A) → (∀ x y, T₂ x y → R x y ∨ B) →
        AF (fun x y => R x y ∨ (A ∧ B)) := by
  induction h₁ with
  | now hT =>
    intro T₂ h₂ R A B hA hB
    refine h₂.mono fun x y h => ?_
    rcases hB x y h with h | h
    · exact Or.inl h
    · rcases hA x y (hT x y) with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', h⟩
  | @up T₁ _ ih =>
    intro T₂ h₂ R A B hA hB
    refine AF.up fun c => ?_
    refine (ih c h₂ (R := fun x y => R x y ∨ R c x) (A := A) (B := B) ?_ ?_).mono ?_
    · intro x y h
      rcases h with h | h
      · exact (hA x y h).imp_left Or.inl
      · exact (hA c x h).imp_left Or.inr
    · intro x y h
      exact (hB x y h).imp_left Or.inl
    · intro x y h
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)

/-- Unary side conditions. -/
theorem oplus₁ {T₁ : X → X → Prop} (h₁ : AF T₁) :
    ∀ {T₂ : X → X → Prop}, AF T₂ → ∀ {R : X → X → Prop} {A B : X → Prop},
      (∀ x y, T₁ x y → R x y ∨ A x) → (∀ x y, T₂ x y → R x y ∨ B x) →
        AF (fun x y => R x y ∨ (A x ∧ B x)) := by
  induction h₁ with
  | now hT =>
    intro T₂ h₂ R A B hA hB
    refine h₂.mono fun x y h => ?_
    rcases hB x y h with h | h
    · exact Or.inl h
    · rcases hA x y (hT x y) with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', h⟩
  | @up T₁ hup₁ ih₁ =>
    intro T₂ h₂
    induction h₂ with
    | now hT =>
      intro R A B hA hB
      refine (AF.up hup₁).mono fun x y h => ?_
      rcases hA x y h with h | h
      · exact Or.inl h
      · rcases hB x y (hT x y) with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩
    | @up T₂ hup₂ ih₂ =>
      intro R A B hA hB
      refine AF.up fun c => ?_
      -- the goal relation is `R'' ∨ (A c ∧ B c)`, with `R'' x y := R x y ∨ R c x ∨ (A x ∧ B x)`
      have hAc : AF (fun x y => (R x y ∨ R c x ∨ (A x ∧ B x)) ∨ A c) := by
        refine (ih₁ c (AF.up hup₂) (R := fun x y => R x y ∨ R c x ∨ A c) (A := A) (B := B)
          ?_ ?_).mono ?_
        · intro x y h
          rcases h with h | h
          · rcases hA x y h with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
          · rcases hA c x h with h | h
            · exact Or.inl (Or.inr (Or.inl h))
            · exact Or.inl (Or.inr (Or.inr h))
        · intro x y h
          exact (hB x y h).imp_left Or.inl
        · intro x y h
          rcases h with (h | h | h) | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inr h
          · exact Or.inl (Or.inr (Or.inr h))
      have hBc : AF (fun x y => (R x y ∨ R c x ∨ (A x ∧ B x)) ∨ B c) := by
        refine (ih₂ c (R := fun x y => R x y ∨ R c x ∨ B c) (A := A) (B := B) ?_ ?_).mono ?_
        · intro x y h
          exact (hA x y h).imp_left Or.inl
        · intro x y h
          rcases h with h | h
          · rcases hB x y h with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
          · rcases hB c x h with h | h
            · exact Or.inl (Or.inr (Or.inl h))
            · exact Or.inl (Or.inr (Or.inr h))
        · intro x y h
          rcases h with (h | h | h) | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inr h
          · exact Or.inl (Or.inr (Or.inr h))
      refine (oplus₀ hAc hBc (R := fun x y => R x y ∨ R c x ∨ (A x ∧ B x)) (A := A c) (B := B c)
        (fun x y h => h) (fun x y h => h)).mono ?_
      intro x y h
      rcases h with (h | h | h) | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

/-- Binary side conditions. -/
theorem oplus₂ {T₁ : X → X → Prop} (h₁ : AF T₁) :
    ∀ {T₂ : X → X → Prop}, AF T₂ → ∀ {R A B : X → X → Prop},
      (∀ x y, T₁ x y → R x y ∨ A x y) → (∀ x y, T₂ x y → R x y ∨ B x y) →
        AF (fun x y => R x y ∨ (A x y ∧ B x y)) := by
  induction h₁ with
  | now hT =>
    intro T₂ h₂ R A B hA hB
    refine h₂.mono fun x y h => ?_
    rcases hB x y h with h | h
    · exact Or.inl h
    · rcases hA x y (hT x y) with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', h⟩
  | @up T₁ hup₁ ih₁ =>
    intro T₂ h₂
    induction h₂ with
    | now hT =>
      intro R A B hA hB
      refine (AF.up hup₁).mono fun x y h => ?_
      rcases hA x y h with h | h
      · exact Or.inl h
      · rcases hB x y (hT x y) with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩
    | @up T₂ hup₂ ih₂ =>
      intro R A B hA hB
      refine AF.up fun c => ?_
      -- the goal relation is `R'' ∨ (A c x ∧ B c x)`, `R'' x y := R x y ∨ R c x ∨ (A x y ∧ B x y)`
      have hAc : AF (fun x y => (R x y ∨ R c x ∨ (A x y ∧ B x y)) ∨ A c x) := by
        refine (ih₁ c (AF.up hup₂) (R := fun x y => R x y ∨ R c x ∨ A c x) (A := A) (B := B)
          ?_ ?_).mono ?_
        · intro x y h
          rcases h with h | h
          · rcases hA x y h with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
          · rcases hA c x h with h | h
            · exact Or.inl (Or.inr (Or.inl h))
            · exact Or.inl (Or.inr (Or.inr h))
        · intro x y h
          exact (hB x y h).imp_left Or.inl
        · intro x y h
          rcases h with (h | h | h) | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inr h
          · exact Or.inl (Or.inr (Or.inr h))
      have hBc : AF (fun x y => (R x y ∨ R c x ∨ (A x y ∧ B x y)) ∨ B c x) := by
        refine (ih₂ c (R := fun x y => R x y ∨ R c x ∨ B c x) (A := A) (B := B) ?_ ?_).mono ?_
        · intro x y h
          exact (hA x y h).imp_left Or.inl
        · intro x y h
          rcases h with h | h
          · rcases hB x y h with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
          · rcases hB c x h with h | h
            · exact Or.inl (Or.inr (Or.inl h))
            · exact Or.inl (Or.inr (Or.inr h))
        · intro x y h
          rcases h with (h | h | h) | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inr h
          · exact Or.inl (Or.inr (Or.inr h))
      refine (oplus₁ hAc hBc (R := fun x y => R x y ∨ R c x ∨ (A x y ∧ B x y))
        (A := A c) (B := B c) (fun x y h => h) (fun x y h => h)).mono ?_
      intro x y h
      rcases h with (h | h | h) | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

/-- **Intersection** (intuitionistic Ramsey). -/
theorem inter {R S : X → X → Prop} (hR : AF R) (hS : AF S) : AF (fun x y => R x y ∧ S x y) :=
  (oplus₂ hR hS (R := fun _ _ => False) (A := R) (B := S) (fun _ _ h => Or.inr h)
    (fun _ _ h => Or.inr h)).mono fun _ _ h => h.resolve_left id

end AF

lemma af_nat_le_up (a : ℕ) : AF (fun x y : ℕ => x ≤ y ∨ a ≤ x) := by
  induction a with
  | zero => exact AF.now fun x _ => Or.inr (Nat.zero_le x)
  | succ a ih =>
    refine AF.up fun b => ?_
    if hb : a + 1 ≤ b then
      exact AF.now fun _ _ => Or.inr (Or.inr hb)
    else
      refine ih.mono fun x y h => ?_
      rcases h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl (Nat.le_trans (Nat.le_of_lt_succ (Nat.lt_of_not_le hb)) h))

/-- `≤` on `ℕ` is almost full. -/
theorem af_nat_le : AF (fun x y : ℕ => x ≤ y) := AF.up af_nat_le_up

/-- The first `k` coordinates. -/
lemma af_fin_le (N : ℕ) : ∀ k, AF (fun x y : Fin N → ℕ => ∀ i : Fin N, (i : ℕ) < k → x i ≤ y i)
  | 0 => AF.now fun _ _ i hi => absurd hi (Nat.not_lt_zero _)
  | k + 1 => by
    if hk : k < N then
      refine ((af_fin_le N k).inter (af_nat_le.comap fun x : Fin N → ℕ => x ⟨k, hk⟩)).mono ?_
      intro x y h i hi
      if hik : (i : ℕ) < k then
        exact h.1 i hik
      else
        have : i = ⟨k, hk⟩ := Fin.ext (Nat.le_antisymm (Nat.le_of_lt_succ hi)
          (Nat.le_of_not_lt hik))
        rw [this]; exact h.2
    else
      refine (af_fin_le N k).mono fun x y h i hi => h i (Nat.lt_of_lt_of_le i.2 ?_)
      exact Nat.le_of_not_lt hk

/-- **Dickson's lemma**, inductive form: divisibility of monomials is almost full. -/
theorem af_finsupp_le (N : ℕ) : AF (fun x y : Fin N →₀ ℕ => x ≤ y) :=
  ((af_fin_le N N).comap fun x : Fin N →₀ ℕ => (x : Fin N → ℕ)).mono fun _ _ h =>
    Finsupp.le_def.2 fun i => h i i.2

end BezoutCounterexample.Constructive
