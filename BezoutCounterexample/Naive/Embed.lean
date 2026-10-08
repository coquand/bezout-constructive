import BezoutCounterexample.Naive.Tower

/-!
# Embedding `R_naive` into a Bézout domain with fresh units

A *fresh target* is a Bézout domain `T` with an exhaustive increasing chain of subrings `B n`
such that `B (n + 1)` contains a unit `c` (with `c⁻¹`) and an element `c'` that are algebraically
independent over `B n`. Given an injection `A₀ → T` with image in `B 0`, the Kronecker tower
embeds into `T` stage by stage (`Naive.exists_extension`), hence `R_naive → T`
(`FreshTarget.embed`). Consequently the five-element obstruction for `T` implies the one for
`R_naive`, and `R_naive` is not an elementary divisor domain (`RN.not_isElementaryDivisorDomain`).
-/

noncomputable section

namespace BezoutCounterexample

open Naive

/-- A Bézout domain with an exhaustive chain of subrings providing fresh units. -/
structure FreshTarget where
  /-- The ring. -/
  T : Type
  [commRing : CommRing T]
  [isDomain : IsDomain T]
  [isBezout : IsBezout T]
  /-- The chain of subrings. -/
  B : ℕ → Subring T
  mono : Monotone B
  exhaust : ∀ t, ∃ n, t ∈ B n
  fresh : ∀ n, ∃ (c : Tˣ) (c' : T), (c : T) ∈ B (n + 1) ∧ ((c⁻¹ : Tˣ) : T) ∈ B (n + 1) ∧
    c' ∈ B (n + 1) ∧ AlgebraicIndependent (B n) ![(c : T), c']
  /-- The map `A₀ → T`. -/
  ι : A₀ →+* T
  ι_injective : Function.Injective ι
  ι_mem : ∀ a, ι a ∈ B 0

attribute [instance] FreshTarget.commRing FreshTarget.isDomain FreshTarget.isBezout

namespace FreshTarget

variable (F : FreshTarget)

/-- Bézout data in a Bézout domain: `x = h₀ a'`, `y = h₀ b'`, `r₀ a' + s₀ b' = 1`. -/
theorem bezoutData (x y : F.T) :
    ∃ h₀ a' b' r₀ s₀ : F.T, x = h₀ * a' ∧ y = h₀ * b' ∧ r₀ * a' + s₀ * b' = 1 := by
  by_cases hxy : x = 0 ∧ y = 0
  · exact ⟨0, 1, 0, 1, 0, by simp [hxy.1], by simp [hxy.2], by ring⟩
  obtain ⟨h₀, hh0⟩ := (IsBezout.iff_span_pair_isPrincipal.1 inferInstance x y).principal
  have hh : (Ideal.span {x, y} : Ideal F.T) = Ideal.span {h₀} := hh0
  have hx : x ∈ Ideal.span {h₀} := hh ▸ Ideal.subset_span (by simp)
  have hy : y ∈ Ideal.span {h₀} := hh ▸ Ideal.subset_span (by simp)
  have hh₀ : h₀ ∈ (Ideal.span {x, y} : Ideal F.T) := hh ▸ Ideal.mem_span_singleton_self h₀
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨r₀, s₀, hrs⟩ := Ideal.mem_span_pair.1 hh₀
  have h₀ne : h₀ ≠ 0 := by
    rintro rfl
    exact hxy ⟨by simpa using ha'.symm, by simpa using hb'.symm⟩
  refine ⟨h₀, a', b', r₀, s₀, by rw [← ha', mul_comm], by rw [← hb', mul_comm], ?_⟩
  apply mul_left_cancel₀ h₀ne
  rw [← ha', ← hb'] at hrs
  linear_combination hrs

/-- The state of the embedding at stage `n`. -/
structure EState (n : ℕ) where
  φ : NA n →+* F.T
  injective : Function.Injective φ
  m : ℕ
  mem : ∀ x, φ x ∈ F.B m

/-- One step of the embedding. -/
theorem exists_next (n : ℕ) (E : F.EState n) :
    ∃ E' : F.EState (n + 1), ∀ x, E'.φ (incl n x) = E.φ x := by
  obtain ⟨h₀, a', b', r₀, s₀, ha, hb, hrs⟩ :=
    F.bezoutData (E.φ (pairAt n).1) (E.φ (pairAt n).2)
  obtain ⟨m', hm'⟩ := F.exhaust r₀
  obtain ⟨m₁, hm₁⟩ := F.exhaust s₀
  obtain ⟨m₂, hm₂⟩ := F.exhaust a'
  obtain ⟨m₃, hm₃⟩ := F.exhaust b'
  set N := max (max E.m m') (max m₁ (max m₂ m₃))
  have hle : ∀ k, k ≤ N → F.B k ≤ F.B N := fun k hk => F.mono hk
  obtain ⟨c, c', hc, hcinv, hc', hind⟩ := F.fresh N
  obtain ⟨ψ, hψ, hψφ, hψmem⟩ := exists_extension E.φ (F.B N)
    (fun x => hle _ (by omega) (E.mem x)) (hle _ (by omega) hm') (hle _ (by omega) hm₁)
    (hle _ (by omega) hm₂) (hle _ (by omega) hm₃) c c' E.injective (pairAt n).1 (pairAt n).2
    ha hb hrs hind
  have hNN : F.B N ≤ F.B (N + 1) := F.mono (Nat.le_succ N)
  refine ⟨⟨ψ, hψ, N + 1, fun u => ?_⟩, fun x => hψφ x⟩
  have hsub : imgRing E.φ r₀ s₀ a' b' c c' ≤ F.B (N + 1) := by
    rw [imgRing, Subring.closure_le]
    rintro t (⟨x, rfl⟩ | ht)
    · exact hNN (hle _ (by omega) (E.mem x))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      have hr : r₀ ∈ F.B (N + 1) := hNN (hle _ (by omega) hm')
      have hs : s₀ ∈ F.B (N + 1) := hNN (hle _ (by omega) hm₁)
      have ha'' : a' ∈ F.B (N + 1) := hNN (hle _ (by omega) hm₂)
      have hb'' : b' ∈ F.B (N + 1) := hNN (hle _ (by omega) hm₃)
      rcases ht with rfl | rfl | rfl | rfl
      · exact add_mem (mul_mem hc hr) (mul_mem hc' hb'')
      · exact sub_mem (mul_mem hc hs) (mul_mem hc' ha'')
      · exact mul_mem ha'' hcinv
      · exact mul_mem hb'' hcinv
  exact hsub (hψmem u)

/-- The initial state. -/
def initState : F.EState 0 := ⟨F.ι, F.ι_injective, 0, F.ι_mem⟩

/-- The states of the embedding. -/
def state (n : ℕ) : F.EState n :=
  Nat.rec (motive := fun n => F.EState n) F.initState
    (fun n E => (F.exists_next n E).choose) n

lemma state_succ (n : ℕ) (x : NA n) : (F.state (n + 1)).φ (incl n x) = (F.state n).φ x :=
  (F.exists_next n (F.state n)).choose_spec x

lemma state_inclLE {i j : ℕ} (h : i ≤ j) (x : NA i) :
    (F.state j).φ (inclLE h x) = (F.state i).φ x := by
  induction j, h using Nat.le_induction with
  | base => rw [inclLE_self]
  | succ k hik ih => rw [inclLE_succ hik, F.state_succ, ih]

/-- **The embedding** `R_naive → T`. -/
def embed : RN →+* F.T :=
  Ring.DirectLimit.lift (fun n => (NA n : Type)) (fun _ _ h => ⇑(inclLE h)) F.T
    (fun n => (F.state n).φ) (fun _ _ h x => F.state_inclLE h x)

lemma embed_of (n : ℕ) (x : NA n) : F.embed (RN.of n x) = (F.state n).φ x := by
  unfold embed RN.of
  apply Ring.DirectLimit.lift_of

lemma embed_ι : F.embed.comp RN.ι = F.ι := by
  apply RingHom.ext
  intro a
  exact (F.embed_of 0 a).trans rfl

end FreshTarget

open Matrix in
/-- **`R_naive` is not an elementary divisor domain**, provided some fresh target satisfies the
five-element obstruction. -/
theorem RN.not_isElementaryDivisorDomain (F : FreshTarget)
    (hobs : ¬ ∃ p q u v μ : F.T, μ * (![p, q] ᵥ* (M.map F.ι) ⬝ᵥ ![u, v]) = 1) :
    ¬ IsElementaryDivisorDomain RN := fun h =>
  not_hasSmithNormalForm_of_obstruction RN.ι
    (obstruction_of_hom RN.ι F.ι F.embed F.embed_ι hobs) (h.2 2 2 _)

end BezoutCounterexample
