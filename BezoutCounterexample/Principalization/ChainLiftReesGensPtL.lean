import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesGens
import BezoutCounterexample.Principalization.ReesI4

/-!
# Integer Rees generators at points (D3.8, leaf)

`exists_reesGensZ` (ChainLiftReesGens) takes its generators from `canonGenPairs`, whose proofs go
through `LocusComp.exists_lspan_compFPt` and `C_mul_T_mem_adjoin_of`, hence through the Method-1
engine at maximal ideals (`cRF_eq`, `local_inv`). Here the same conclusion is proved from generators
at points:

* `genPairsOf`: the pairs `(j, g)`, `1 ≤ j ≤ d`, `g ∈ gens j`, of any list family;
* `exists_reesGensZ_of`: the conclusion of `exists_reesGensZ` for any list family `gens` with
  `lspan (gens j) = F_j`, through `C_mul_T_mem_adjoin_of_ptL` (CompFilGenPtL);
* `exists_reesGensZ_ptL`: with the generators of the steps from `exists_lspan_compFPt_ptL`
  (as in `reesAlg_finiteType_ptL`).

Leaf module; `canonGensF`/`canonGenPairs` are untouched.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

/-- The pairs `(j, g)` with `1 ≤ j ≤ d` and `g ∈ gens j`. -/
def genPairsOf {A : Type} (d : ℕ) (gens : ℤ → List A) : List (ℤ × A) :=
  (List.range d).flatMap fun k : ℕ => (gens ((k : ℤ) + 1)).map fun g => ((k : ℤ) + 1, g)

lemma mem_genPairsOf {A : Type} (d : ℕ) (gens : ℤ → List A) {q : ℤ × A} :
    q ∈ genPairsOf d gens ↔ 1 ≤ q.1 ∧ q.1 ≤ d ∧ q.2 ∈ gens q.1 := by
  obtain ⟨j, g⟩ := q
  rw [genPairsOf, List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, hq⟩
    obtain ⟨g', hg', he⟩ := List.mem_map.1 hq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have := List.mem_range.1 hk
    exact ⟨by omega, by omega, hg'⟩
  · rintro ⟨h1, hd, hg⟩
    refine ⟨(j - 1).toNat, List.mem_range.2 (by omega), List.mem_map.2 ⟨g, ?_, ?_⟩⟩
    · rwa [show ((j - 1).toNat : ℤ) + 1 = j by omega]
    · rw [show ((j - 1).toNat : ℤ) + 1 = j by omega]

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ}
  (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {dim : ℕ}
  (hchartn : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) dim))
  {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ)) (e : SmoothCert.QB G ≃+* A)

include hI l hl hmax h𝔭 hd hw hchartn in
/-- **Integer Rees generators** from any list family of generators of the steps. -/
theorem exists_reesGensZ_of [Fact (HasPres A)] (gens : ℤ → List A)
    (hgens : ∀ j : ℤ, 1 ≤ j → j ≤ d → lspan (gens j) = (compFil hI hmax h𝔭 d).F j) :
    ∃ (r : ℕ) (gZ : Fin r → MvPolynomial (Fin (m + n)) ℤ) (δ : Fin r → ℕ),
      (∀ i, 1 ≤ δ i ∧ δ i ≤ d) ∧
      (∀ i, toAq G e (toQZ (gZ i)) ∈ (compFil hI hmax h𝔭 d).F (δ i)) ∧
      (∀ (j : ℤ) (f : A), f ∈ (compFil hI hmax h𝔭 d).F j →
        LaurentPolynomial.C f * T j ∈
          Algebra.adjoin A (insert (T (-1)) (Set.range (reesYL G e gZ δ)))) := by
  set L := genPairsOf d gens
  obtain ⟨Dg, hDg⟩ := finite_choice_dep (ι := Fin L.length)
    (P := fun i (x : ℕ × MvPolynomial (Fin (m + n)) ℤ) =>
      0 < x.1 ∧ toAq G e (toQZ x.2) = (x.1 : A) * (L.get i).2)
    fun i => by
      obtain ⟨D, pZ, hD, h⟩ := exists_toAq_int G e (L.get i).2
      exact ⟨(D, pZ), hD, h⟩
  have hmem : ∀ i, 1 ≤ (L.get i).1 ∧ (L.get i).1 ≤ d ∧ (L.get i).2 ∈ gens (L.get i).1 := fun i =>
    (mem_genPairsOf d gens).1 (List.get_mem L i)
  have hδ : ∀ i, (((L.get i).1.toNat : ℕ) : ℤ) = (L.get i).1 := fun i => by
    have := (hmem i).1; omega
  refine ⟨L.length, fun i => (Dg i).2, fun i => (L.get i).1.toNat, fun i => ?_, fun i => ?_, ?_⟩
  · have h1 := (hmem i).1
    have h2 := (hmem i).2.1
    show 1 ≤ (L.get i).1.toNat ∧ (L.get i).1.toNat ≤ d
    exact ⟨by omega, by omega⟩
  · rw [(hDg i).2, hδ i]
    refine Ideal.mul_mem_left _ _ ?_
    rw [← hgens _ (hmem i).1 (hmem i).2.1]
    exact Ideal.subset_span (hmem i).2.2
  · intro j f hf
    refine Algebra.adjoin_le ?_ (C_mul_T_mem_adjoin_of_ptL hI l hl hmax h𝔭 hchartn hd hw gens
      hgens j f hf)
    intro x hx
    rcases hx with hx | hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq] at hx
      obtain ⟨j, hj, g, hg, rfl⟩ := hx
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
      obtain ⟨i, hi⟩ := List.mem_iff_get.1
        ((mem_genPairsOf d gens (q := (j, g))).2 ⟨h1, h2, hg⟩)
      -- `C g Tʲ = C(D⁻¹) · yᵢ`, with `D` a unit of `A`
      have hD : (((Dg i).1 : ℚ)) ≠ 0 := by exact_mod_cast (hDg i).1.ne'
      have hy : reesYL G e (fun i => (Dg i).2) (fun i => (L.get i).1.toNat) i =
          LaurentPolynomial.C (((Dg i).1 : A) * g) * T j := by
        rw [reesYL, (hDg i).2, hδ i, hi]
      have hx : LaurentPolynomial.C g * T j =
          LaurentPolynomial.C (algebraMap ℚ A ((Dg i).1 : ℚ)⁻¹) *
            reesYL G e (fun i => (Dg i).2) (fun i => (L.get i).1.toNat) i := by
        rw [hy, ← mul_assoc, ← map_mul, ← mul_assoc]
        congr 2
        rw [show ((Dg i).1 : A) = algebraMap ℚ A ((Dg i).1 : ℚ) by simp, ← map_mul,
          inv_mul_cancel₀ hD, map_one, one_mul]
      rw [hx, LaurentPolynomial.C_eq_algebraMap]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
        (Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩))

include hI l hl hmax h𝔭 hd hw hchartn in
/-- **Integer Rees generators at points**: `exists_reesGensZ` with the generators of the steps from
`exists_lspan_compFPt_ptL` (no `canonGensF`, no engine at maximal ideals). -/
theorem exists_reesGensZ_ptL [Fact (HasPres A)] :
    ∃ (r : ℕ) (gZ : Fin r → MvPolynomial (Fin (m + n)) ℤ) (δ : Fin r → ℕ),
      (∀ i, 1 ≤ δ i ∧ δ i ≤ d) ∧
      (∀ i, toAq G e (toQZ (gZ i)) ∈ (compFil hI hmax h𝔭 d).F (δ i)) ∧
      (∀ (j : ℤ) (f : A), f ∈ (compFil hI hmax h𝔭 d).F j →
        LaurentPolynomial.C f * T j ∈
          Algebra.adjoin A (insert (T (-1)) (Set.range (reesYL G e gZ δ)))) := by
  have hex : ∀ k : Fin d, ∃ L : List A,
      lspan L = (compFil hI hmax h𝔭 d).F ((k : ℕ) + 1 : ℕ) := fun k => by
    obtain ⟨L, hL⟩ := h𝔭.exists_lspan_compFPt_ptL hI l hl hmax hchartn ((((k : ℕ) + 1 : ℕ) : ℤ) / d)
    exact ⟨L, by rw [compFil_F, hL]⟩
  obtain ⟨L, hL⟩ := finite_choice_dep hex
  let gens : ℤ → List A := fun j =>
    if h : 1 ≤ j ∧ j ≤ d then L ⟨(j - 1).toNat, by omega⟩ else []
  have hgens : ∀ j : ℤ, 1 ≤ j → j ≤ d → lspan (gens j) = (compFil hI hmax h𝔭 d).F j := by
    intro j h1 h2
    simp only [gens, dif_pos (And.intro h1 h2)]
    rw [hL]
    congr 1
    simp only [Fin.val_mk]
    omega
  exact exists_reesGensZ_of hI l hl hmax h𝔭 hd hw hchartn G e gens hgens

end BezoutCounterexample.Principalization
