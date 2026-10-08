import BezoutCounterexample.Constructive.Kernel
import BezoutCounterexample.Constructive.GCDPoly

/-!
# Explicitly presented `ℚ`-algebras

`HasPres A`: `A ≅ ℚ[Y₁, …, Yₙ] ⧸ (G)` for an explicit finite list `G`. Such rings have decidable
membership in finitely generated ideals, a zero test and decidable divisibility (Gröbner bases,
`HasPres.mem_dec`, `HasPres.zeroTest`, `HasPres.dvdDec`).

`HasPres.away`: if `A` is presented, so is `A[1/g]`, by `ℚ[W, Y] ⧸ (G, W p - 1)` (`W` first,
`p` a lift of `g`). The localisation property is checked directly: `p` becomes a unit; every
element is `Q(Y) / pᴺ` (`exists_pow_mul_sub_mem`); and if `a - b ∈ (G, W p - 1)` then
`pᴺ (a - b) ∈ (G)` (evaluate `W ↦ 1/p` in `(ℚ[Y]/(G))[1/p]`).
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

/-- `A` is explicitly presented. -/
def HasPres (A : Type*) [CommRing A] : Prop :=
  ∃ (n : ℕ) (G : List (MvPolynomial (Fin n) ℚ)),
    Nonempty ((MvPolynomial (Fin n) ℚ ⧸ lspan G) ≃+* A)

namespace HasPres

variable {A : Type*} [CommRing A]

theorem of_ringEquiv {B : Type*} [CommRing B] (h : HasPres A) (e : A ≃+* B) : HasPres B := by
  obtain ⟨n, G, ⟨f⟩⟩ := h
  exact ⟨n, G, ⟨f.trans e⟩⟩

/-- **Decidable membership** in finitely generated ideals. -/
theorem mem_dec (h : HasPres A) (L : List A) (x : A) : x ∈ lspan L ∨ x ∉ lspan L := by
  obtain ⟨n, G, ⟨f⟩⟩ := h
  exact mem_lspan_dec_of_ringEquiv f.symm (quot_mem_lspan_dec G) L x

theorem zeroTest (h : HasPres A) (x : A) : x = 0 ∨ x ≠ 0 := by
  obtain ⟨n, G, ⟨f⟩⟩ := h
  exact eq_zero_or_of_ringEquiv f.symm (quot_eq_zero_or G) x

theorem dvdDec (h : HasPres A) : DvdDec A := by
  obtain ⟨n, G, ⟨f⟩⟩ := h
  exact DvdDec.of_ringEquiv f.symm (quot_dvdDec G)

end HasPres

theorem hasPres_mvPolynomial (n : ℕ) : HasPres (MvPolynomial (Fin n) ℚ) :=
  ⟨n, [], ⟨(Ideal.quotEquivOfEq (by simp [lspan])).trans (RingEquiv.quotientBot _)⟩⟩

section Away

variable {n : ℕ} (G : List (MvPolynomial (Fin n) ℚ)) (p : MvPolynomial (Fin n) ℚ)

/-- The `Y`-variables of `ℚ[W, Y]` (`W` is variable `0`). -/
noncomputable abbrev jY : MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin (n + 1)) ℚ :=
  rename Fin.succ

/-- The relations `(G, W p - 1)`. -/
noncomputable def awayList : List (MvPolynomial (Fin (n + 1)) ℚ) :=
  (X 0 * jY p - 1) :: G.map jY

/-- The structure map `ℚ[Y]/(G) → ℚ[W, Y]/(G, W p - 1)`. -/
noncomputable def awayHom :
    (MvPolynomial (Fin n) ℚ ⧸ lspan G) →+* (MvPolynomial (Fin (n + 1)) ℚ ⧸ lspan (awayList G p)) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (jY (n := n)).toRingHom) fun a ha => by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.map (jY (n := n)).toRingHom (lspan G) ≤ lspan (awayList G p) := by
      rw [lspan, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact Ideal.subset_span (List.mem_cons_of_mem _ (List.mem_map_of_mem hx))
    exact this (Ideal.mem_map_of_mem _ ha)

lemma awayHom_mk (a : MvPolynomial (Fin n) ℚ) :
    awayHom G p (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (jY a) := rfl

/-- Clearing the powers of `W`: `pᴺ P ≡ Q(Y)` modulo `W p - 1`. -/
lemma exists_pow_mul_sub_mem (P : MvPolynomial (Fin (n + 1)) ℚ) :
    ∃ (N : ℕ) (Q : MvPolynomial (Fin n) ℚ), jY p ^ N * P - jY Q ∈ lspan (awayList G p) := by
  have hW : X 0 * jY p - 1 ∈ lspan (awayList G p) := Ideal.subset_span List.mem_cons_self
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp⟩
  | add P₁ P₂ h₁ h₂ =>
    obtain ⟨N₁, Q₁, hQ₁⟩ := h₁
    obtain ⟨N₂, Q₂, hQ₂⟩ := h₂
    refine ⟨N₁ + N₂, p ^ N₂ * Q₁ + p ^ N₁ * Q₂, ?_⟩
    have : jY p ^ (N₁ + N₂) * (P₁ + P₂) - jY (p ^ N₂ * Q₁ + p ^ N₁ * Q₂) =
        jY p ^ N₂ * (jY p ^ N₁ * P₁ - jY Q₁) + jY p ^ N₁ * (jY p ^ N₂ * P₂ - jY Q₂) := by
      simp only [map_add, map_mul, map_pow]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hQ₁) (Ideal.mul_mem_left _ _ hQ₂)
  | mul_X P k hP =>
    obtain ⟨N, Q, hQ⟩ := hP
    refine Fin.cases ?_ (fun i => ?_) k
    · refine ⟨N + 1, Q, ?_⟩
      have : jY p ^ (N + 1) * (P * X 0) - jY Q =
          (jY p ^ N * P - jY Q) + jY p ^ N * P * (X 0 * jY p - 1) := by ring
      rw [this]
      exact add_mem hQ (Ideal.mul_mem_left _ _ hW)
    · refine ⟨N, Q * X i, ?_⟩
      have : jY p ^ N * (P * X i.succ) - jY (Q * X i) = (jY p ^ N * P - jY Q) * X i.succ := by
        simp only [map_mul, jY, rename_X]; ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hQ

/-- **`ℚ[W, Y]/(G, W p - 1)` is `(ℚ[Y]/(G))[1/p]`.** -/
theorem isLocalization_awayHom :
    @IsLocalization.Away _ _ (Ideal.Quotient.mk (lspan G) p)
      (MvPolynomial (Fin (n + 1)) ℚ ⧸ lspan (awayList G p)) _ (awayHom G p).toAlgebra := by
  let _ := (awayHom G p).toAlgebra
  have hW : X 0 * jY p - 1 ∈ lspan (awayList G p) := Ideal.subset_span List.mem_cons_self
  have hunit : IsUnit (algebraMap (MvPolynomial (Fin n) ℚ ⧸ lspan G)
      (MvPolynomial (Fin (n + 1)) ℚ ⧸ lspan (awayList G p)) (Ideal.Quotient.mk _ p)) := by
    refine IsUnit.of_mul_eq_one (b := Ideal.Quotient.mk _ (X 0)) ?_
    show Ideal.Quotient.mk _ (jY p) * Ideal.Quotient.mk _ (X 0) = 1
    rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem, mul_comm]
    exact hW
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [map_pow]; exact hunit.pow k
  · intro z
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨N, Q, hQ⟩ := exists_pow_mul_sub_mem G p P
    refine ⟨⟨Ideal.Quotient.mk _ Q, ⟨_, N, rfl⟩⟩, ?_⟩
    show Ideal.Quotient.mk _ P * awayHom G p (Ideal.Quotient.mk _ p ^ N) =
      awayHom G p (Ideal.Quotient.mk _ Q)
    rw [map_pow, awayHom_mk, awayHom_mk, ← map_pow, ← map_mul, Ideal.Quotient.eq, mul_comm]
    exact hQ
  · intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change awayHom G p _ = awayHom G p _ at hab
    rw [awayHom_mk, awayHom_mk, Ideal.Quotient.eq, ← map_sub] at hab
    -- evaluate `W ↦ 1/p` in `(ℚ[Y]/(G))[1/p]`
    set R := MvPolynomial (Fin n) ℚ ⧸ lspan G
    set L := Localization.Away (Ideal.Quotient.mk (lspan G) p)
    have hu : IsUnit (algebraMap R L (Ideal.Quotient.mk _ p)) :=
      IsLocalization.Away.algebraMap_isUnit _
    let ev : MvPolynomial (Fin (n + 1)) ℚ →+* L :=
      eval₂Hom ((algebraMap R L).comp ((Ideal.Quotient.mk (lspan G)).comp C))
        (Fin.cons (↑hu.unit⁻¹ : L) fun i => algebraMap R L (Ideal.Quotient.mk _ (X i)))
    have hcomp : ev.comp (jY (n := n)).toRingHom = (algebraMap R L).comp (Ideal.Quotient.mk _) :=
      MvPolynomial.ringHom_ext (fun c => by simp [ev]) (fun i => by simp [ev])
    have hevY : ∀ q, ev (jY q) = algebraMap R L (Ideal.Quotient.mk _ q) := fun q =>
      congrArg (fun φ : MvPolynomial (Fin n) ℚ →+* L => φ q) hcomp
    have hker : lspan (awayList G p) ≤ RingHom.ker ev := by
      rw [lspan, Ideal.span_le]
      intro x hx
      have hx' : x ∈ awayList G p := hx
      simp only [awayList, List.mem_cons, List.mem_map] at hx'
      rcases hx' with rfl | ⟨g, hg, rfl⟩
      · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, hevY, map_one, sub_eq_zero]
        simp only [ev, eval₂Hom_X', Fin.cons_zero]
        exact hu.val_inv_mul
      · have hg' : g ∈ lspan G := Ideal.subset_span hg
        rw [SetLike.mem_coe, RingHom.mem_ker, hevY, Ideal.Quotient.eq_zero_iff_mem.2 hg', map_zero]
    have h0 := hker hab
    rw [RingHom.mem_ker, hevY, map_sub, map_sub, sub_eq_zero] at h0
    obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (Ideal.Quotient.mk (lspan G) p)) L).1 h0
    exact ⟨⟨_, N, rfl⟩, hN⟩

end Away

/-- **Presentations pass to `A[1/g]`.** -/
theorem HasPres.away {A : Type*} [CommRing A] (h : HasPres A) (g : A) (L : Type*) [CommRing L]
    [Algebra A L] [IsLocalization.Away g L] : HasPres L := by
  obtain ⟨n, G, ⟨e⟩⟩ := h
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (e.symm g)
  refine ⟨n + 1, awayList G p, ⟨?_⟩⟩
  letI := (awayHom G p).toAlgebra
  have := isLocalization_awayHom G p
  exact IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (Ideal.Quotient.mk (lspan G) p))
    (T := Submonoid.powers g) _ _ e (by rw [Submonoid.map_powers, hp]; simp)

end BezoutCounterexample.Constructive
