import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesLocal
import BezoutCounterexample.Principalization.ChainLiftReesPres

/-!
# The rows of the weighted-chart model through the presentation (Task B, Rees layer S5b)

On a chart `Cp.D k` of a `ChartCoverPt`, with the presentation of `ReesAlg Φ` in `(Y, s, y)`
(`ChainLiftReesPres`, R2 as `hgen`) and R1 as `hΦ`, L1 and L2 (`ChainLiftReesLocal`) in polynomial
form over `ℚ`:

* `exists_heads_poly`: `gᴺ` has a lift `pγ ∈ ℚ[Y]`, and each `uₗ = C(gᴺ aₗ) T^{wₗ}` is the image of
  some `Pₗ ∈ ℚ[Y, s, y]` (head row `γ x̃ₗ − s^{wₗ} u'ₗ` with `u'ₗ ↦ Pₗ`);
* `exists_yrow_poly`: for a generator `yⱼ`, `C(gˢ) yⱼ = Σᵢ C(bᵢ) s^{eᵢ} ∏ₗ uₗ^{αᵢₗ}` with lifts
  `pβ` of `gˢ` and `pbᵢ` of `bᵢ` (`y`-row `β yⱼ − Qⱼ(s, u', Y)`).

Clearing to `ℤ` happens in the assembly (S6), where the layout of the model is fixed: rows that are
exact relations over `ℚ` with integer coefficients are appended to the global relations
(`exists_reesKer_ext`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} {𝔭 : Ideal A}
  (hZp : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀)
  (Cp : ChartCoverPt I v₀ 𝔭) (Φ : WFil A) {d : ℕ}
  (hΦ : ∀ j : ℤ, Φ.F j = compFPt I 𝔭 ((j : ℚ) / d)) (hd : 0 < d)
  {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ)) (e : SmoothCert.QB G ≃+* A)
  {r : ℕ} (gZ : Fin r → MvPolynomial (Fin (m + n)) ℤ) (δ : Fin r → ℕ)
  (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
  (hgF : ∀ i, toAq G e (toQZ (gZ i)) ∈ Φ.F (δ i))
  (hgen : ∀ (j : ℤ) (f : A), f ∈ Φ.F j →
    LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (insert (T (-1)) (Set.range (reesYL G e gZ δ))))

include hI hZp hΦ hd hneg hgF hgen in
/-- **L1 through the presentation**: a lift of `gᴺ` and preimages of the `uₗ = C(gᴺ aₗ) T^{wₗ}`. -/
theorem exists_heads_poly [Fact (HasPres A)] (k : Fin Cp.n) (s : ℕ) (a : Fin (Cp.D k).n → A)
    (ha : ∀ i, (Cp.D k).cB.x i * algebraMap A (Cp.D k).B (Cp.D k).g ^ s =
      algebraMap A (Cp.D k).B (a i))
    (w : Fin (Cp.D k).n → ℕ) (hw : ∀ l, (w l : ℚ) = d * (Cp.D k).ek l) :
    ∃ (N : ℕ) (pγ : MvPolynomial (Fin (m + n)) ℚ)
      (P : Fin (Cp.D k).n → MvPolynomial (Fin ((m + n) + (1 + r))) ℚ),
      toAq G e pγ = (Cp.D k).g ^ N ∧
      ∀ l, aeval (reesVec G e gZ δ) (P l) = LaurentPolynomial.C ((Cp.D k).g ^ N * a l) * T (w l : ℤ) := by
  obtain ⟨N, hN⟩ := exists_heads_rees hI hZp Cp Φ hΦ hd k s a ha w hw
  obtain ⟨pγ, hpγ⟩ := toAq_surjective G e ((Cp.D k).g ^ N)
  obtain ⟨P, hP⟩ := Constructive.finite_choice_dep fun l =>
    reesAlg_le_range G e gZ δ Φ hneg hgF hgen (hN l)
  exact ⟨N, pγ, P, hpγ, hP⟩

include hI hZp hΦ hd hgF in
/-- **L2 through the presentation**: the `y`-row of a generator, with lifts of the coefficients. -/
theorem exists_yrow_poly [Fact (HasPres A)] (k : Fin Cp.n) (s : ℕ) (a : Fin (Cp.D k).n → A)
    (ha : ∀ i, (Cp.D k).cB.x i * algebraMap A (Cp.D k).B (Cp.D k).g ^ s =
      algebraMap A (Cp.D k).B (a i))
    (w : Fin (Cp.D k).n → ℕ) (hw : ∀ l, (w l : ℚ) = d * (Cp.D k).ek l) (N : ℕ) (j : Fin r) :
    ∃ (S K : ℕ) (pβ : MvPolynomial (Fin (m + n)) ℚ) (pb : Fin K → MvPolynomial (Fin (m + n)) ℚ)
      (α : Fin K → (Fin (Cp.D k).n →₀ ℕ)) (ex : Fin K → ℕ),
      toAq G e pβ = (Cp.D k).g ^ S ∧
      (∀ i l, (Cp.D k).ek l = 0 → α i l = 0) ∧
      (∀ i, (ex i : ℤ) + δ j = ((∑ l, α i l * w l : ℕ) : ℤ)) ∧
      LaurentPolynomial.C (toAq G e pβ) * reesYL G e gZ δ j =
        ∑ i, LaurentPolynomial.C (toAq G e (pb i)) * T (-(ex i : ℤ)) *
          ∏ l, (LaurentPolynomial.C ((Cp.D k).g ^ N * a l) * T (w l : ℤ)) ^ α i l := by
  obtain ⟨S, K, b, α, ex, hα0, hex, hS⟩ :=
    exists_rees_expansion hI hZp Cp Φ hΦ hd k s a ha w hw N (hgF j)
  obtain ⟨pβ, hpβ⟩ := toAq_surjective G e ((Cp.D k).g ^ S)
  obtain ⟨pb, hpb⟩ := Constructive.finite_choice_dep fun i => toAq_surjective G e (b i)
  refine ⟨S, K, pβ, pb, α, ex, hpβ, hα0, hex, ?_⟩
  rw [hpβ, reesYL, ← mul_assoc, ← map_mul, hS]
  simp only [hpb]

end BezoutCounterexample.Principalization
