import BezoutCounterexample.Constructive.PolyNoeth

/-!
# Divisible torsion vanishes in an inductively Noetherian ring

Let `P` be a property of elements of `A` such that every `y` with `P y` is `s`-divisible inside
`P` (`y = s * y'`, `P y'`) and killed by a power of `s`. If `A` is inductively Noetherian, then
`P y → y = 0`.

This replaces the Nakayama step of `ReesSmooth.reesPsi_ker` (where `P` is membership in the image
`K̄` of the kernel, and the classical proof needs `K̄` finitely generated). It is Perdry's argument
(`KrullP`) run along the bar: iterating divisibility gives `y = sⁿ hₙ`; the bar yields some
`hₙ₊₁ ∈ (h₀, …, hₙ)`, so `y ∈ (s y)`, i.e. `y = r s y = (r s)ᴺ y = 0`. The `hᵢ` are produced one
at a time inside the induction, so no choice is used.
-/

namespace BezoutCounterexample.Constructive

variable {A : Type*} [CommRing A]

/-- The bar invariant: the head `h` satisfies `y₀ = sⁿ h`, and `sⁿ` maps the older entries into
`(s y₀)`. -/
theorem NBar.mem_span_of_divisible {s y₀ : A} {P : A → Prop}
    (hdiv : ∀ y, P y → ∃ y', P y' ∧ y = s * y') {L : List A} (hL : NBar L) :
    ∀ (n : ℕ) (h : A) (t : List A), L = h :: t → P h → y₀ = s ^ n * h →
      (∀ x ∈ t, s ^ n * x ∈ Ideal.span {s * y₀}) → y₀ ∈ Ideal.span {s * y₀} := by
  induction hL with
  | @good a l ha =>
    intro n h t hL _ hy hx
    obtain ⟨hah, hlt⟩ := List.cons.inj hL
    rw [hah, hlt] at ha
    suffices hs : s ^ n * h ∈ Ideal.span {s * y₀} by rwa [← hy] at hs
    refine Submodule.span_induction (p := fun z _ => s ^ n * z ∈ Ideal.span {s * y₀}) ?_ ?_ ?_ ?_ ha
    · intro z hz; exact hx z hz
    · rw [mul_zero]; exact Ideal.zero_mem _
    · intro u v _ _ hu hv; rw [mul_add]; exact Ideal.add_mem _ hu hv
    · intro c z _ hz
      rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hz
  | @step l _ ih =>
    intro n h t hL hP hy hx
    obtain ⟨h', hP', hh'⟩ := hdiv h hP
    refine ih h' (n + 1) h' l rfl hP' ?_ ?_
    · rw [hy, hh']; ring
    · intro x hx'
      rw [hL] at hx'
      rcases List.mem_cons.1 hx' with rfl | hxt
      · rw [pow_succ', mul_assoc, ← hy]; exact Ideal.subset_span rfl
      · rw [pow_succ', mul_assoc]; exact Ideal.mul_mem_left _ _ (hx x hxt)

/-- **Divisible torsion vanishes** in an inductively Noetherian ring. -/
theorem IndNoeth.eq_zero_of_divisible_torsion (hA : IndNoeth A) {s : A} {P : A → Prop}
    (hdiv : ∀ y, P y → ∃ y', P y' ∧ y = s * y') (htor : ∀ y, P y → ∃ N : ℕ, s ^ N * y = 0)
    {y : A} (hy : P y) : y = 0 := by
  have h1 : NBar [y] := match hA with
    | .step h => h y
  have hmem := h1.mem_span_of_divisible hdiv 0 y [] rfl hy (by rw [pow_zero, one_mul])
    (fun x hx => absurd hx List.not_mem_nil)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨N, hN⟩ := htor y hy
  have hpow : ∀ m : ℕ, y = (r * s) ^ m * y := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_mul]
    | succ m ih => rw [pow_succ, mul_assoc, mul_assoc r s y, hr, ← ih]
  rw [hpow N, mul_pow, mul_assoc, hN, mul_zero]

end BezoutCounterexample.Constructive
