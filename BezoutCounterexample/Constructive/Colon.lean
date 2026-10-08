import BezoutCounterexample.Constructive.IdealOps
import BezoutCounterexample.Constructive.PresentedOps

/-!
# Colon ideals

Explicit generators of colon ideals of finitely generated ideals.

* `exists_colon_single`: in `ℚ[Y]`, `(I : g) = g⁻¹ (I ∩ (g))` (`exists_inter_list`, then exact
  division, finite choice);
* `exists_colon`: `(I : J) = ⋂_{g ∈ J} (I : g)`;
* `HasPres.exists_colon`: the same in any explicitly presented ring, through lifts.
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {n : ℕ}

/-- **Colon by one element** in `ℚ[Y]`. -/
theorem exists_colon_single (I : List (MvPolynomial (Fin n) ℚ)) (g : MvPolynomial (Fin n) ℚ) :
    ∃ L : List (MvPolynomial (Fin n) ℚ), ∀ x, x ∈ lspan L ↔ x * g ∈ lspan I := by
  rcases deq g 0 with rfl | hg
  · refine ⟨[1], fun x => ?_⟩
    simp only [mul_zero, zero_mem, iff_true]
    rw [lspan_singleton, Ideal.span_singleton_one]; trivial
  obtain ⟨K, hK⟩ := exists_inter_list I [g]
  have hdiv : ∀ i : Fin K.length, ∃ q : MvPolynomial (Fin n) ℚ, K.get i = q * g := by
    intro i
    have hi : K.get i ∈ lspan K := Ideal.subset_span (List.get_mem K i)
    rw [hK, Submodule.mem_inf, lspan_singleton] at hi
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 hi.2
    exact ⟨q, hq.symm⟩
  obtain ⟨q, hq⟩ := fin_choice hdiv
  refine ⟨List.ofFn q, fun x => ?_⟩
  have hKI : lspan K ≤ lspan I := by rw [hK]; exact inf_le_left
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := exists_rep_of_mem hx
    have hx' : x * g = ∑ i, a i * K.get (Fin.cast (List.length_ofFn) i) := by
      rw [ha, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hq, List.get_ofFn]
      ring
    rw [hx']
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hKI (Ideal.subset_span (List.get_mem K _)))
  · intro hx
    have hxK : x * g ∈ lspan K := by
      rw [hK, Submodule.mem_inf, lspan_singleton]
      exact ⟨hx, Ideal.mem_span_singleton.2 (dvd_mul_left g x)⟩
    obtain ⟨a, ha⟩ := exists_rep_of_mem hxK
    have hx' : x * g = (∑ i, a i * q i) * g := by
      rw [ha, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hq]; ring
    rw [mul_right_cancel₀ hg hx']
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
      (Ideal.subset_span (List.mem_ofFn.2 ⟨i, rfl⟩))

/-- **Colon of finitely generated ideals** in `ℚ[Y]`. -/
theorem exists_colon (I : List (MvPolynomial (Fin n) ℚ)) :
    ∀ J : List (MvPolynomial (Fin n) ℚ), ∃ L : List (MvPolynomial (Fin n) ℚ),
      ∀ x, x ∈ lspan L ↔ ∀ g ∈ J, x * g ∈ lspan I
  | [] => ⟨[1], fun x => ⟨fun _ g hg => absurd hg List.not_mem_nil, fun _ => by
      rw [lspan_singleton, Ideal.span_singleton_one]; trivial⟩⟩
  | g :: J => by
    obtain ⟨L₁, h₁⟩ := exists_colon_single I g
    obtain ⟨L₂, h₂⟩ := exists_colon I J
    obtain ⟨L, hL⟩ := exists_inter_list L₁ L₂
    refine ⟨L, fun x => ?_⟩
    rw [hL, Submodule.mem_inf, h₁, h₂]
    simp only [List.mem_cons, forall_eq_or_imp]

/-- Membership for all of `(J)` reduces to the generators. -/
lemma forall_span_of_forall {R : Type*} [CommRing R] {I : Ideal R} {x : R} {J : List R}
    (h : ∀ g ∈ J, x * g ∈ I) : ∀ y ∈ lspan J, x * y ∈ I := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul c z _ hz => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hz

/-- **Colon ideals in presented rings.** -/
theorem HasPres.exists_colon {A : Type*} [CommRing A] (h : HasPres A) (I J : List A) :
    ∃ L : List A, ∀ x, x ∈ lspan L ↔ ∀ y ∈ lspan J, x * y ∈ lspan I := by
  obtain ⟨n, G, ⟨e⟩⟩ := h
  let φ : MvPolynomial (Fin n) ℚ →+* A := e.toRingHom.comp (Ideal.Quotient.mk _)
  have hφ : Function.Surjective φ := e.surjective.comp Ideal.Quotient.mk_surjective
  -- lifts
  have hlift : ∀ L : List A, ∃ L' : List (MvPolynomial (Fin n) ℚ), L'.map φ = L := by
    intro L
    induction L with
    | nil => exact ⟨[], rfl⟩
    | cons a L ih =>
      obtain ⟨L', hL'⟩ := ih
      obtain ⟨a', rfl⟩ := hφ a
      exact ⟨a' :: L', by rw [List.map_cons, hL']⟩
  obtain ⟨I', rfl⟩ := hlift I
  obtain ⟨J', rfl⟩ := hlift J
  have hker : ∀ z, φ z = 0 ↔ z ∈ lspan G := fun z => by
    simp [φ, Ideal.Quotient.eq_zero_iff_mem]
  -- `φ⁻¹ (lspan (I'.map φ)) = lspan (I' ++ G)`
  have hpre : ∀ (L' : List (MvPolynomial (Fin n) ℚ)) z, φ z ∈ lspan (L'.map φ) ↔ z ∈ lspan (L' ++ G) := by
    intro L' z
    have hmap : lspan (L'.map φ) = Ideal.map φ (lspan L') := by
      show Ideal.span _ = Ideal.map φ (Ideal.span _)
      rw [Ideal.map_span]; congr 1; ext y; simp
    rw [hmap, Ideal.mem_map_iff_of_surjective φ hφ, lspan_append_eq_sup, Submodule.mem_sup]
    constructor
    · rintro ⟨w, hw, hwz⟩
      refine ⟨w, hw, z - w, (hker _).1 (by rw [map_sub, hwz, sub_self]), add_sub_cancel _ _⟩
    · rintro ⟨w, hw, u, hu, rfl⟩
      exact ⟨w, hw, by rw [map_add, (hker u).2 hu, add_zero]⟩
  obtain ⟨L', hL'⟩ := _root_.BezoutCounterexample.Constructive.exists_colon (I' ++ G) J'
  refine ⟨L'.map φ, fun x => ?_⟩
  obtain ⟨x', rfl⟩ := hφ x
  have hGL : ∀ u ∈ lspan G, u ∈ lspan L' := fun u hu => (hL' u).2 fun g _ =>
    Ideal.mul_mem_right _ _ (Ideal.span_mono (fun z hz => List.mem_append_right _ hz) hu)
  rw [hpre, lspan_append_eq_sup, sup_eq_left.2 (fun u hu => hGL u hu), hL']
  constructor
  · intro hx y hy
    obtain ⟨y', rfl⟩ := hφ y
    rw [← map_mul, hpre]
    have hy' : y' ∈ lspan (J' ++ G) := (hpre J' y').1 hy
    rw [lspan_append_eq_sup, Submodule.mem_sup] at hy'
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    rw [mul_add]
    refine add_mem (forall_span_of_forall hx a ha) (Ideal.mul_mem_left _ _ ?_)
    exact Ideal.span_mono (fun z hz => List.mem_append_right _ hz) hb
  · intro hx g hg
    rw [← hpre, map_mul]
    exact hx _ (Ideal.subset_span (List.mem_map_of_mem hg))

end BezoutCounterexample.Constructive
