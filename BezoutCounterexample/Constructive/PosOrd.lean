import BezoutCounterexample.Constructive.PosF2

/-!
# The order as a computed value (Task D, R6; roadmap `docs/invariant-constructive.md` §1.1, §1.6)

`MarkedCenter.ord` and `Invariant.ord_spec` take `sSup` of a set of naturals (`Nat.sSup_mem`,
`le_csSup`), with boundedness from `Submodule.exists_mem_ne_zero_of_ne_bot` and Krull's
intersection theorem. Here the order is produced by the Rees bar of `pos_F2` itself, with a
witness, so no search and no Markov principle is used.

* `pos_ord`: `h = 0`, or `h ∈ 𝔭ᵏ` together with a derivative `∂^α h` of degree `k` with `E`
  (`ExactOrd`). The escape of `rees_escape` is taken at the first level where a derivative
  escapes, so the level is recorded.
* `le_of_escape`, `ExactOrd.le`, `ExactOrd.unique`: if `E x` excludes `x ∈ 𝔭` (at an explicit
  point: `E x := z(x) ≠ 0`), the recorded `k` is the largest `b` with `h ∈ 𝔭ᵇ`.
* `pos_ordL`, `ExactOrdL`, `ExactOrdL.isOrd`: the same for an explicit ideal `(l)`: every
  generator is `0`, or `ord(l) = min ord(fᵢ)` is attained with a witness (`IsOrd`).
-/

namespace BezoutCounterexample.Constructive

/-- `k` is the order of `I` along `M`: `I ⊆ Mᵏ`, and `I ⊆ Mᵇ` gives `b ≤ k`. -/
def IsOrd {S : Type*} [CommRing S] (I M : Ideal S) (k : ℕ) : Prop :=
  I ≤ M ^ k ∧ ∀ b : ℕ, I ≤ M ^ b → b ≤ k

lemma IsOrd.unique {S : Type*} [CommRing S] {I M : Ideal S} {k k' : ℕ} (h : IsOrd I M k)
    (h' : IsOrd I M k') : k = k' :=
  le_antisymm (h'.2 k h.1) (h.2 k' h'.1)

section Chart

variable {S : Type*} [CommRing S] [Algebra ℚ S] {j : ℕ} (c : PChart S j)

/-- Finitely many decisions, keeping membership. -/
lemma forall_or_exists_mem_finset {P E : (Fin j → ℕ) → Prop} :
    ∀ s : Finset (Fin j → ℕ), (∀ α ∈ s, P α ∨ E α) → (∀ α ∈ s, P α) ∨ ∃ α ∈ s, E α := by
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun _ => Or.inl fun _ h => absurd h (Finset.notMem_empty _)
  | insert a s _ ih =>
    intro h
    rcases ih fun α hα => h α (Finset.mem_insert_of_mem hα) with hs | ⟨α, hα, he⟩
    · rcases h a (Finset.mem_insert_self a s) with ha | ha
      · refine Or.inl fun α hα => ?_
        rcases Finset.mem_insert.1 hα with rfl | hα
        · exact ha
        · exact hs α hα
      · exact Or.inr ⟨a, Finset.mem_insert_self a s, ha⟩
    · exact Or.inr ⟨α, Finset.mem_insert_of_mem hα, he⟩

/-- `h` has order `k` along `c`, witnessed by a derivative of degree `k` with `E`. -/
def ExactOrd (E : S → Prop) (h : S) (k : ℕ) : Prop :=
  h ∈ c.P ^ k ∧ ∃ α, deg α = k ∧ E (c.D α h)

/-- **Positive order**: `h = 0`, or `h` has an order with a witness. -/
theorem pos_ord (hR : IndNoeth (reesSubring c.P)) (hloc : ∀ a ∈ c.P, IsUnit (1 - a))
    {E : S → Prop} (hdec : ∀ x : S, x ∈ c.P ∨ E x) (h : S) :
    h = 0 ∨ ∃ k, ExactOrd c E h k := by
  have hstep : ∀ k, h ∈ c.P ^ k → h ∈ c.P ^ (k + 1) ∨ ∃ k, ExactOrd c E h k := by
    intro k hk
    have hlow := (c.mem_F_iff (fun _ => le_rfl) k h).1 (pow_le_F_one c k hk)
    rcases forall_or_exists_mem_finset (P := fun α => c.D α h ∈ c.P)
      (E := fun α => E (c.D α h)) (Finset.Nat.antidiagonalTuple j k)
      (fun α _ => hdec _) with hall | ⟨α, hα, he⟩
    · refine Or.inl (F_one_le_pow c (k + 1) ((c.mem_F_iff (fun _ => le_rfl) (k + 1) h).2 ?_))
      intro α hα
      rw [wt_one] at hα
      rcases Nat.lt_or_ge (deg α) k with hlt | hge
      · exact hlow α (by rw [wt_one]; exact hlt)
      · exact hall α (Finset.Nat.mem_antidiagonalTuple.2 (by
          show ∑ i, α i = k
          have : deg α = k := by omega
          exact this))
    · exact Or.inr ⟨k, hk, α, Finset.Nat.mem_antidiagonalTuple.1 hα, he⟩
  rcases rees_escape hR hstep with ⟨a, ha, hah⟩ | he
  · refine Or.inl ?_
    obtain ⟨u, hu⟩ := hloc a ha
    have h1 : (1 - a) * h = 0 := by rw [sub_mul, one_mul, ← hah, sub_self]
    rw [← hu] at h1
    exact (Units.mul_right_eq_zero u).1 h1
  · exact Or.inr he

variable {c}

/-- A derivative of degree `k` outside `𝔭` bounds every `b` with `h ∈ 𝔭ᵇ`. -/
lemma le_of_escape {h : S} {α : Fin j → ℕ} {k b : ℕ} (hα : deg α = k) (hP : c.D α h ∉ c.P)
    (hb : h ∈ c.P ^ b) : b ≤ k := by
  rcases Nat.lt_or_ge k b with hkb | hbk
  · have hF := pow_le_F_one c (k + 1) (Ideal.pow_le_pow_right hkb hb)
    exact absurd ((c.mem_F_iff (fun _ => le_rfl) (k + 1) h).1 hF α
      (by rw [wt_one, hα]; exact Nat.lt_succ_self k)) hP
  · exact hbk

variable {E : S → Prop} (hE : ∀ x, E x → x ∉ c.P)
include hE

lemma ExactOrd.le {h : S} {k : ℕ} (hk : ExactOrd c E h k) {b : ℕ} (hb : h ∈ c.P ^ b) : b ≤ k := by
  obtain ⟨-, α, hα, he⟩ := hk
  exact le_of_escape hα (hE _ he) hb

lemma ExactOrd.unique {h : S} {k k' : ℕ} (hk : ExactOrd c E h k) (hk' : ExactOrd c E h k') :
    k = k' :=
  le_antisymm (hk'.le hE hk.1) (hk.le hE hk'.1)

lemma ExactOrd.isOrd {h : S} {k : ℕ} (hk : ExactOrd c E h k) :
    IsOrd (Ideal.span {h}) c.P k :=
  ⟨(Ideal.span_singleton_le_iff_mem _).2 hk.1, fun _ hb =>
    hk.le hE ((Ideal.span_singleton_le_iff_mem _).1 hb)⟩

omit hE in
variable (c) in
/-- `(l)` has order `k` along `c`: every generator lies in `𝔭ᵏ`, and one has a derivative of
degree `k` with `E`. -/
def ExactOrdL (E : S → Prop) (l : List S) (k : ℕ) : Prop :=
  (∀ f ∈ l, f ∈ c.P ^ k) ∧ ∃ f ∈ l, ∃ α, deg α = k ∧ E (c.D α f)

lemma ExactOrdL.isOrd {l : List S} {k : ℕ} (hk : ExactOrdL c E l k) :
    IsOrd (lspan l) c.P k := by
  refine ⟨by rw [lspan, Ideal.span_le]; exact hk.1, fun b hb => ?_⟩
  obtain ⟨f, hf, α, hα, he⟩ := hk.2
  exact le_of_escape hα (hE _ he) (hb (Ideal.subset_span hf))

lemma ExactOrdL.unique {l : List S} {k k' : ℕ} (hk : ExactOrdL c E l k)
    (hk' : ExactOrdL c E l k') : k = k' :=
  (hk.isOrd hE).unique (hk'.isOrd hE)

/-- If the generators lie in `𝔭`, the order is positive. -/
lemma ExactOrdL.one_le {l : List S} {k : ℕ} (hk : ExactOrdL c E l k) (hl : ∀ f ∈ l, f ∈ c.P) :
    1 ≤ k := by
  obtain ⟨f, hf, -⟩ := hk.2
  exact (hk.isOrd hE).2 1 (by rw [pow_one, lspan, Ideal.span_le]; exact hl)

omit hE in
/-- **Positive order of an explicit ideal**: every generator is `0`, or `(l)` has an order
with a witness. -/
theorem pos_ordL (hR : IndNoeth (reesSubring c.P)) (hloc : ∀ a ∈ c.P, IsUnit (1 - a))
    (hdec : ∀ x : S, x ∈ c.P ∨ E x) :
    ∀ l : List S, (∀ f ∈ l, f = 0) ∨ ∃ k, ExactOrdL c E l k
  | [] => Or.inl fun _ h => absurd h List.not_mem_nil
  | f :: l => by
    have hz : ∀ k, (0 : S) ∈ c.P ^ k := fun _ => Ideal.zero_mem _
    rcases pos_ord c hR hloc hdec f with hf | ⟨k₁, hk₁, α, hα, he⟩ <;>
      rcases pos_ordL hR hloc hdec l with hl | ⟨k₂, hl₂, g, hg, β, hβ, he'⟩
    · refine Or.inl fun x hx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hf
      · exact hl x hx
    · refine Or.inr ⟨k₂, fun x hx => ?_, g, List.mem_cons_of_mem _ hg, β, hβ, he'⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hf]; exact hz _
      · exact hl₂ x hx
    · refine Or.inr ⟨k₁, fun x hx => ?_, f, List.mem_cons_self .., α, hα, he⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hk₁
      · rw [hl x hx]; exact hz _
    · rcases Nat.lt_or_ge k₂ k₁ with h21 | h12
      · refine Or.inr ⟨k₂, fun x hx => ?_, g, List.mem_cons_of_mem _ hg, β, hβ, he'⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Ideal.pow_le_pow_right h21.le hk₁
        · exact hl₂ x hx
      · refine Or.inr ⟨k₁, fun x hx => ?_, f, List.mem_cons_self .., α, hα, he⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hk₁
        · exact Ideal.pow_le_pow_right h12 (hl₂ x hx)

end Chart

end BezoutCounterexample.Constructive
