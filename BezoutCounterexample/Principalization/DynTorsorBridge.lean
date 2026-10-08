import BezoutCounterexample.Principalization.DynReesBridge
import BezoutCounterexample.Constructive.DynJou

/-!
# `s` in the torsor, prime-or-split (`docs/d5-plan.md`, step 3)

* `rel_eq_relC`, `mk_mem_map_iff`: `u = mk p ∈ 𝔞 J_B(c)` iff `p ∈ KJ 𝔞 c`.
* `jou_map_dyn`: `Constructive.jou_dyn_l` on `J_B(c)`: `𝔞 J_B(c)` is prime up to `Q` when `𝔞` is
  (with decidable membership) and `c_l ∉ 𝔞`.
* `span_s_dec`: membership in `(s)` of the Rees algebra is decidable when the `F_j` are.
* `torsor_s_dyn`: in `U = J_R(y)` over the Rees algebra, `(s)` is prime or `(P)` splits; prime-free
  (the hypotheses of `span_s_dyn_split`, plus a generator `y_l ∉ (s)`).
* `torsor_s_isPrime_of_dyn`: for the prime component, `(s) U` is prime (cf. `torsor_s_prime`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open LaurentPolynomial Constructive

section Jou

variable {B : Type*} [CommRing B] {r : ℕ}

lemma rel_eq_relC (c : Fin (r + 1) → B) : Jou.rel c = relC c := Jou.rel_eq c

lemma mk_mem_map_iff (𝔞 : Ideal B) (c : Fin (r + 1) → B) (p : MvPolynomial (Fin (r + 1)) B) :
    Ideal.Quotient.mk (Ideal.span {Jou.rel c}) p ∈ 𝔞.map (algebraMap B (Jou.J c)) ↔
      p ∈ KJ 𝔞 c := by
  rw [Jou.algebraMap_eq_mk_comp_C, ← Ideal.map_map, Ideal.mem_quotient_iff_mem_sup, KJ,
    rel_eq_relC]

/-- **`𝔞 J_B(c)` is prime up to `Q`.** -/
theorem jou_map_dyn {𝔞 : Ideal B} (hdec : ∀ x, x ∈ 𝔞 ∨ x ∉ 𝔞) {Q : Prop}
    (hpr : ∀ x y, x * y ∈ 𝔞 → x ∈ 𝔞 ∨ y ∈ 𝔞 ∨ Q) (c : Fin (r + 1) → B) (l : Fin (r + 1))
    (hcl : c l ∉ 𝔞) {u v : Jou.J c} (huv : u * v ∈ 𝔞.map (algebraMap B (Jou.J c))) :
    u ∈ 𝔞.map (algebraMap B (Jou.J c)) ∨ v ∈ 𝔞.map (algebraMap B (Jou.J c)) ∨ Q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← map_mul, mk_mem_map_iff] at huv
  rw [mk_mem_map_iff, mk_mem_map_iff]
  exact jou_dyn_l hdec hpr c l hcl huv

end Jou

section Rees

variable {B : Type*} [CommRing B] [Algebra ℚ B] (Φ : WFil B) (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
include hneg

omit [Algebra ℚ B] in
/-- **Membership in `(s)` is decidable** when the `F_j` are. -/
theorem span_s_dec (hdec : ∀ (j : ℤ) (x : B), x ∈ Φ.F j ∨ x ∉ Φ.F j) (p : ReesAlg Φ) :
    p ∈ Ideal.span {reesS Φ hneg} ∨ p ∉ Ideal.span {reesS Φ hneg} := by
  rw [mem_span_s_iff]
  rcases finset_search (p : B[T;T⁻¹]).coeff.support
      (fun j => (p : B[T;T⁻¹]).coeff j ∈ Φ.F (j + 1)) (fun j => hdec _ _) with hall | ⟨j, -, hj⟩
  · refine Or.inl fun j => ?_
    rcases Finset.decidableMem j (p : B[T;T⁻¹]).coeff.support with h | h
    · rw [Finsupp.notMem_support_iff.1 h]; exact zero_mem _
    · exact hall j h
  · exact Or.inr fun h => hj (h j)

omit [Algebra ℚ B] in
/-- **`s` in the torsor: prime, or `(P)` splits.** -/
theorem torsor_s_dyn (hpres : HasPres B) {P : List B} (hP : IsRadL P)
    (hdec : ∀ (j : ℤ) (x : B), x ∈ Φ.F j ∨ x ∉ Φ.F j)
    (hT : ∀ (j : ℕ) (u x : B), NZDmod P u → u * x ∈ Φ.F ((j + 1 : ℕ) : ℤ) → x ∈ Φ.F (j : ℤ) →
      x ∈ Φ.F ((j + 1 : ℕ) : ℤ))
    (hpart : ∀ (a b : ℕ) (x y : B), x ∈ Φ.F a → y ∈ Φ.F b → x * y ∈ Φ.F ((a + b + 1 : ℕ) : ℤ) →
      ∃ g g' : B, g + g' = 1 ∧ g * x ∈ Φ.F ((a + 1 : ℕ) : ℤ) ∧ g' * y ∈ Φ.F ((b + 1 : ℕ) : ℤ))
    {r : ℕ} (c : Fin (r + 1) → ReesAlg Φ) (l : Fin (r + 1))
    (hcl : c l ∉ Ideal.span {reesS Φ hneg}) {u v : Jou.J c}
    (huv : u * v ∈ Ideal.span {algebraMap _ (Jou.J c) (reesS Φ hneg)}) :
    u ∈ Ideal.span {algebraMap _ (Jou.J c) (reesS Φ hneg)} ∨
      v ∈ Ideal.span {algebraMap _ (Jou.J c) (reesS Φ hneg)} ∨ RadSplit P := by
  have hspan : Ideal.span {algebraMap _ (Jou.J c) (reesS Φ hneg)} =
      (Ideal.span {reesS Φ hneg}).map (algebraMap _ (Jou.J c)) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspan] at huv ⊢
  exact jou_map_dyn (span_s_dec Φ hneg hdec)
    (fun x y hxy => span_s_dyn_split Φ hneg hpres hP hdec hT hpart hxy) c l hcl huv

end Rees

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

include hI hmax h𝔭 hd hw in
/-- For the prime component, `(s) U` is prime: `torsor_s_dyn` with the classical decisions. -/
theorem torsor_s_isPrime_of_dyn (hpres : HasPres A) (P : List A) (hP : lspan P = 𝔭)
    (hne : Ideal.span {algebraMap _ (Torsor hI hmax h𝔭 d hπ)
      (reesS (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj))} ≠ ⊤) :
    (Ideal.span {algebraMap _ (Torsor hI hmax h𝔭 d hπ)
      (reesS (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj))}).IsPrime := by
  classical
  have hpr : (lspan P).IsPrime := hP ▸ h𝔭.1.1
  have hrad : IsRadL P := fun z n hz => hpr.mem_of_pow_mem n hz
  set s := reesS (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj)
  -- a generator `y_l ∉ (s)` (as in `torsor_s_prime`)
  obtain ⟨j, hj1, hjd, g, hg, hgF⟩ := exists_gen_not_mem hI hmax h𝔭 hd hw
  obtain ⟨l, hl1, hl2⟩ := exists_index hI hmax h𝔭 (π := π) hj1 hjd hg
  have hl : torsorY hI hmax h𝔭 d hπ l ∉ Ideal.span {s} := by
    rw [mem_span_s_iff]
    intro hall
    apply hgF
    have := hall j
    simp only [torsorY, hl1, hl2, coeff_C_mul_T] at this
    exact this
  refine ⟨hne, fun {u v} huv => ?_⟩
  rcases torsor_s_dyn (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj)
      hpres hrad (fun j x => em _) (compFil_torsionFree hI hmax h𝔭 hd hw P hP)
      (fun a b x y hx hy hxy => compFil_partition hI hmax h𝔭 hd hw hx hy hxy)
      (torsorY hI hmax h𝔭 d hπ) l hl huv with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (not_radSplit_of_isPrime hpr)

end BezoutCounterexample.Principalization
