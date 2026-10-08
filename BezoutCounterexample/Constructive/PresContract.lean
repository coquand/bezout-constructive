import BezoutCounterexample.Constructive.IdealOps
import BezoutCounterexample.Constructive.Colon

/-!
# Intersection and contraction in presented rings (`docs/d5-plan.md`, step 4, O3)

The elimination results of `IdealOps.lean` live in `ℚ[Y]`; here they are transported to any
presented ring `A ≅ ℚ[Y]/(G)` by lifting generator lists (as in `HasPres.exists_colon`).

* `pres_pre`: for a surjection `φ` with kernel `(G)`, `φ z ∈ (φ L') ↔ z ∈ (L', G)`.
* `HasPres.exists_inter`: `(I) ∩ (J)` has an explicit generator list.
* `HasPres.exists_contract`: for `L = A[1/g]` and a list `M` in `L`, `{x | x/1 ∈ (M)}` has an
  explicit generator list (saturation, by elimination of `W` in `ℚ[W, Y]/(G, W p - 1)`).
* `HasPres.exists_inter_fin`: finite intersections.

Used for (O3): generators of `F_t = ⋂ₖ {x | x/1 ∈ (Lₖ)}` from the chart lists.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

section Pre

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

lemma exists_lift (hφ : Function.Surjective φ) (L : List S) : ∃ L' : List R, L'.map φ = L := by
  induction L with
  | nil => exact ⟨[], rfl⟩
  | cons a L ih =>
    obtain ⟨L', hL'⟩ := ih
    obtain ⟨a', rfl⟩ := hφ a
    exact ⟨a' :: L', by rw [List.map_cons, hL']⟩

/-- Preimages of explicitly generated ideals under a surjection with kernel `(G)`. -/
lemma pres_pre (hφ : Function.Surjective φ) (G : List R) (hker : ∀ z, φ z = 0 ↔ z ∈ lspan G)
    (L' : List R) (z : R) : φ z ∈ lspan (L'.map φ) ↔ z ∈ lspan (L' ++ G) := by
  have hmap : lspan (L'.map φ) = Ideal.map φ (lspan L') := by
    show Ideal.span _ = Ideal.map φ (Ideal.span _)
    rw [Ideal.map_span]; congr 1; ext y; simp
  rw [hmap, Ideal.mem_map_iff_of_surjective φ hφ, lspan_append_eq_sup, Submodule.mem_sup]
  constructor
  · rintro ⟨w, hw, hwz⟩
    exact ⟨w, hw, z - w, (hker _).1 (by rw [map_sub, hwz, sub_self]), add_sub_cancel _ _⟩
  · rintro ⟨w, hw, u, hu, rfl⟩
    exact ⟨w, hw, by rw [map_add, (hker u).2 hu, add_zero]⟩

end Pre

variable {A : Type*} [CommRing A]

/-- **Intersection** of two explicitly generated ideals of a presented ring. -/
theorem HasPres.exists_inter (h : HasPres A) (I J : List A) :
    ∃ L : List A, ∀ x, x ∈ lspan L ↔ x ∈ lspan I ∧ x ∈ lspan J := by
  obtain ⟨n, G, ⟨e⟩⟩ := h
  let φ : MvPolynomial (Fin n) ℚ →+* A := e.toRingHom.comp (Ideal.Quotient.mk _)
  have hφ : Function.Surjective φ := e.surjective.comp Ideal.Quotient.mk_surjective
  have hker : ∀ z, φ z = 0 ↔ z ∈ lspan G := fun z => by
    simp [φ, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨I', rfl⟩ := exists_lift φ hφ I
  obtain ⟨J', rfl⟩ := exists_lift φ hφ J
  obtain ⟨L', hL'⟩ := exists_inter_list (I' ++ G) (J' ++ G)
  refine ⟨L'.map φ, fun x => ?_⟩
  obtain ⟨x', rfl⟩ := hφ x
  have hG : lspan G ≤ lspan L' := by
    rw [hL']
    exact le_inf (Ideal.span_mono fun z hz => List.mem_append_right _ hz)
      (Ideal.span_mono fun z hz => List.mem_append_right _ hz)
  rw [pres_pre φ hφ G hker, pres_pre φ hφ G hker, pres_pre φ hφ G hker, lspan_append_eq_sup,
    sup_eq_left.2 hG, hL', Submodule.mem_inf]

/-- **Finite intersections**. -/
theorem HasPres.exists_inter_fin (h : HasPres A) :
    ∀ (m : ℕ) (I : Fin m → List A), ∃ L : List A, ∀ x, x ∈ lspan L ↔ ∀ k, x ∈ lspan (I k)
  | 0, _ => ⟨[1], fun x => ⟨fun _ k => k.elim0, fun _ => by
      rw [lspan_singleton, Ideal.span_singleton_one]; trivial⟩⟩
  | m + 1, I => by
    obtain ⟨L, hL⟩ := HasPres.exists_inter_fin h m (fun k => I k.succ)
    obtain ⟨L', hL'⟩ := h.exists_inter (I 0) L
    refine ⟨L', fun x => ?_⟩
    rw [hL', hL]
    exact ⟨fun ⟨h0, hs⟩ k => Fin.cases h0 hs k, fun hk => ⟨hk 0, fun k => hk k.succ⟩⟩

/-- **Contraction from `A[1/g]`** of an explicitly generated ideal. -/
theorem HasPres.exists_contract (h : HasPres A) (g : A) (L : Type*) [CommRing L] [Algebra A L]
    [IsLocalization.Away g L] (M : List L) :
    ∃ N : List A, ∀ x, algebraMap A L x ∈ lspan M ↔ x ∈ lspan N := by
  obtain ⟨n, G, ⟨e⟩⟩ := h
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (e.symm g)
  let A' := MvPolynomial (Fin (n + 1)) ℚ ⧸ lspan (awayList G p)
  letI := (awayHom G p).toAlgebra
  have := isLocalization_awayHom G p
  have hT : (Submonoid.powers (Ideal.Quotient.mk (lspan G) p)).map e.toMonoidHom =
      Submonoid.powers g := by
    rw [Submonoid.map_powers, hp]; simp
  let ψ : A' ≃+* L := IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers
    (Ideal.Quotient.mk (lspan G) p)) (T := Submonoid.powers g) A' L e hT
  have hψ : ∀ a, ψ (awayHom G p a) = algebraMap A L (e a) := fun a =>
    IsLocalization.ringEquivOfRingEquiv_eq hT a
  let χ : MvPolynomial (Fin (n + 1)) ℚ →+* L := ψ.toRingHom.comp (Ideal.Quotient.mk _)
  have hχ : Function.Surjective χ := ψ.surjective.comp Ideal.Quotient.mk_surjective
  have hkerχ : ∀ z, χ z = 0 ↔ z ∈ lspan (awayList G p) := fun z => by
    show ψ (Ideal.Quotient.mk _ z) = 0 ↔ _
    rw [map_eq_zero_iff ψ ψ.injective, Ideal.Quotient.eq_zero_iff_mem]
  let φ : MvPolynomial (Fin n) ℚ →+* A := e.toRingHom.comp (Ideal.Quotient.mk _)
  have hφ : Function.Surjective φ := e.surjective.comp Ideal.Quotient.mk_surjective
  have hkerφ : ∀ z, φ z = 0 ↔ z ∈ lspan G := fun z => by
    simp [φ, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨M', rfl⟩ := exists_lift χ hχ M
  obtain ⟨N', hN'⟩ := _root_.BezoutCounterexample.Constructive.exists_contract G p M'
  have hcomm : ∀ x', χ (jY x') = algebraMap A L (φ x') := fun x' => by
    show ψ (Ideal.Quotient.mk _ (jY x')) = _
    rw [← awayHom_mk, hψ]; rfl
  have hswap : ∀ z, z ∈ lspan (M' ++ awayList G p) ↔ z ∈ lspan (awayList G p ++ M') := fun z => by
    rw [lspan_append_eq_sup, lspan_append_eq_sup, sup_comm]
  have hG : lspan G ≤ lspan N' := by
    rw [lspan, Ideal.span_le]
    intro u hu
    refine (hN' u).1 (Ideal.subset_span (List.mem_append_left _ ?_))
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem hu)
  refine ⟨N'.map φ, fun x => ?_⟩
  obtain ⟨x', rfl⟩ := hφ x
  rw [← hcomm, pres_pre χ hχ _ hkerχ, hswap, hN', pres_pre φ hφ G hkerφ, lspan_append_eq_sup,
    sup_eq_left.2 hG]

/-- **(O3) Generators from chart lists**: for finitely many localizations `A[1/gₖ]` and lists
`Lₖ` there, `{x | ∀ k, x/1 ∈ (Lₖ)}` has an explicit generator list. -/
theorem HasPres.exists_gens_of_charts (h : HasPres A) :
    ∀ {m : ℕ} (g : Fin m → A) (L : ∀ k, List (Localization.Away (g k))),
    ∃ N : List A, ∀ x, x ∈ lspan N ↔
      ∀ k, algebraMap A (Localization.Away (g k)) x ∈ lspan (L k)
  | 0, _, _ => ⟨[1], fun x => ⟨fun _ k => k.elim0, fun _ => by
      rw [lspan_singleton, Ideal.span_singleton_one]; trivial⟩⟩
  | m + 1, g, L => by
    obtain ⟨N, hN⟩ := HasPres.exists_gens_of_charts h (fun k => g k.succ) (fun k => L k.succ)
    obtain ⟨N₀, hN₀⟩ := h.exists_contract (g 0) _ (L 0)
    obtain ⟨N', hN'⟩ := h.exists_inter N₀ N
    refine ⟨N', fun x => ?_⟩
    rw [hN', ← hN₀, hN]
    exact ⟨fun ⟨h0, hs⟩ k => Fin.cases h0 hs k, fun hk => ⟨hk 0, fun k => hk k.succ⟩⟩

end BezoutCounterexample.Constructive
