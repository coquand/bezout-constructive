import BezoutCounterexample.Constructive.DynPrime

/-!
# The associated graded ring is a domain, prime-or-split (D5; `docs/d5-plan.md`, step 3)

Dynamical form of `Principalization.compFil_mul_not_mem` (the input of `rees_s_prime`). There,
`𝔭` is prime, and primality enters only through **torsion-freeness** of the graded pieces
(`not_mem_loc`): `h ∉ 𝔭`, `h x ∈ F_{a+1}` give `x ∈ F_{a+1}`.

Here `(P)` is an explicit radical ideal, and the filtration `F` is abstract. The two hypotheses are
prime-free:

* `hT` (torsion-freeness): for `u` a **non-zero-divisor mod `(P)`** (`NZDmod P u`), `u x ∈ F_{j+1}`
  and `x ∈ F_j` give `x ∈ F_{j+1}`;
* the valuation property in partition-of-unity form: `x y ∈ F_{a+b+1}` gives `g + g' = 1` with
  `g x ∈ F_{a+1}` and `g' y ∈ F_{b+1}` (classically: the components of `V(P)` where
  `x ∈ F_{a+1}`, resp. `y ∈ F_{b+1}`, are open and closed and cover `V(P)`). It is passed as the
  elements `g, g'`.

`gr_dyn`: if moreover `x ∉ F_{a+1}` and `y ∉ F_{b+1}`, then `(P)` splits. The colon `((P) : g)` is
computed (`HasPres.exists_colon`) and its generators are tested: if all lie in `(P)`, `g` is a
non-zero-divisor and `hT` gives `x ∈ F_{a+1}`; otherwise `c g ∈ (P)` with `c ∉ (P)`, and
`dynPrimeRad` either splits or gives `g ∈ (P)`, in which case `g' = 1 - g` is a non-zero-divisor and
`hT` gives `y ∈ F_{b+1}`. For `𝔭` prime there is no split, and this is `compFil_mul_not_mem`.
-/

namespace BezoutCounterexample.Constructive

variable {A : Type*} [CommRing A]

/-- `u` is a non-zero-divisor modulo `(P)`. -/
def NZDmod (P : List A) (u : A) : Prop := ∀ c, c * u ∈ lspan P → c ∈ lspan P

/-- `(P)` is the intersection of two radical, strictly larger, explicit ideals. -/
def RadSplit (P : List A) : Prop :=
  ∃ L₁ L₂ : List A, IsRadL L₁ ∧ IsRadL L₂ ∧ lspan P ≤ lspan L₁ ∧ lspan P ≤ lspan L₂ ∧
    (∃ y ∈ lspan L₁, y ∉ lspan P) ∧ (∃ y ∈ lspan L₂, y ∉ lspan P) ∧
    ∀ y, y ∈ lspan P ↔ y ∈ lspan L₁ ∧ y ∈ lspan L₂

/-- Finite search: every element of `L` lies in `(P)`, or one does not. -/
lemma list_search (h : HasPres A) (P L : List A) :
    (∀ c ∈ L, c ∈ lspan P) ∨ ∃ c ∈ L, c ∉ lspan P := by
  induction L with
  | nil => exact Or.inl fun c hc => absurd hc List.not_mem_nil
  | cons c L ih =>
    rcases h.mem_dec P c with hc | hc
    · rcases ih with hall | ⟨c', hc', hc'P⟩
      · exact Or.inl fun x hx => (List.mem_cons.1 hx).elim (· ▸ hc) (hall x)
      · exact Or.inr ⟨c', List.mem_cons_of_mem c hc', hc'P⟩
    · exact Or.inr ⟨c, List.mem_cons_self .., hc⟩

/-- **Non-zero-divisor test**: `u` is a non-zero-divisor mod `(P)`, or `c u ∈ (P)` with
`c ∉ (P)`. -/
theorem nzd_dec (h : HasPres A) (P : List A) (u : A) :
    NZDmod P u ∨ ∃ c, c ∉ lspan P ∧ c * u ∈ lspan P := by
  obtain ⟨L, hL⟩ := h.exists_colon P [u]
  have hu : u ∈ lspan [u] := by rw [lspan_singleton]; exact Ideal.mem_span_singleton_self u
  rcases list_search h P L with hall | ⟨c, hc, hcP⟩
  · refine Or.inl fun c hcu => ?_
    have hcL : c ∈ lspan L := (hL c).2 fun y hy => by
      rw [lspan_singleton] at hy
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      rw [mul_left_comm]; exact Ideal.mul_mem_left _ r hcu
    exact (Ideal.span_le.2 fun z hz => hall z hz) hcL
  · exact Or.inr ⟨c, hcP, (hL c).1 (Ideal.subset_span hc) u hu⟩

/-- If `g ∈ (P)` then `1 - g` is a non-zero-divisor mod `(P)`. -/
lemma nzdMod_of_add_eq_one {P : List A} {g g' : A} (hg : g + g' = 1) (hgP : g ∈ lspan P) :
    NZDmod P g' := fun c hc => by
  have : c = c * g' + c * g := by rw [← mul_add, add_comm g', hg, mul_one]
  rw [this]; exact add_mem hc (Ideal.mul_mem_left _ c hgP)

/-- **The graded ring is a domain, prime-or-split.** -/
theorem gr_dyn (h : HasPres A) {P : List A} (hP : IsRadL P) (F : ℕ → Ideal A)
    (hT : ∀ (j : ℕ) (u x : A), NZDmod P u → u * x ∈ F (j + 1) → x ∈ F j → x ∈ F (j + 1))
    {a b : ℕ} {x y g g' : A} (hx : x ∈ F a) (hx1 : x ∉ F (a + 1)) (hy : y ∈ F b)
    (hy1 : y ∉ F (b + 1)) (hg : g + g' = 1) (hgx : g * x ∈ F (a + 1))
    (hgy : g' * y ∈ F (b + 1)) : RadSplit P := by
  rcases nzd_dec h P g with hnzd | ⟨c, hcP, hcg⟩
  · exact absurd (hT a g x hnzd hgx hx) hx1
  rcases dynPrimeRad h hP hcg with hc | hgP | ⟨-, hgP, L₁, L₂, r₁, r₂, l₁, l₂, m₁, m₂, hsp⟩
  · exact absurd hc hcP
  · exact absurd (hT b g' y (nzdMod_of_add_eq_one hg hgP) hgy hy) hy1
  · exact ⟨L₁, L₂, r₁, r₂, l₁, l₂, ⟨g, m₁, hgP⟩, ⟨c, m₂, hcP⟩, hsp⟩

end BezoutCounterexample.Constructive
