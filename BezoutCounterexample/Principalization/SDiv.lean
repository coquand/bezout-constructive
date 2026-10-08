import BezoutCounterexample.Principalization.GCDStep

/-!
# Divisibility by `s` from membership in the filtration (`~/COLL/bezout-gcd.tex`, §6)

The last decision of the GCD form of the torsor step (`torsor_dec`, hypothesis `hs`) is
divisibility by `s` in `U`. It reduces to membership in the filtration ideals `F_j = 𝓕_j` of `A`:

* `sdvd_dec_rees`: in `R = ⊕ F_j T^j`, `x ∈ sR` iff every coefficient `x_j ∈ F_{j+1}`
  (`mem_span_s_iff`), a finite check over the support of `x`;
* `sdvd_dec_torsor`: `U / sU ≅ J_{R/sR}(h̄)` (`Jou.ker_redHom`), whose zero test is `zeroTest_jou` on
  the domain `R/sR` (`rees_s_prime`), with a row entry nonzero modulo `s` (`exists_gen_not_mem`);
* `torsor_dec_F`: gcds, zero test and decidable divisibility of `U` from those of `A` and the
  decision of membership in the `F_j`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open LaurentPolynomial Constructive

/-- Finite search over a `Finset`. -/
lemma finset_forall_or_not {α : Type*} [DecidableEq α] {P : α → Prop} (s : Finset α)
    (h : ∀ a ∈ s, P a ∨ ¬ P a) : (∀ a ∈ s, P a) ∨ ¬ ∀ a ∈ s, P a := by
  induction s using Finset.induction_on with
  | empty => exact Or.inl fun a ha => absurd ha (Finset.notMem_empty a)
  | insert a s ha ih =>
    rcases h a (Finset.mem_insert_self a s) with h1 | h1
    · rcases ih fun b hb => h b (Finset.mem_insert_of_mem hb) with h2 | h2
      · exact Or.inl fun b hb => (Finset.mem_insert.1 hb).elim (fun h => h ▸ h1) (h2 b)
      · exact Or.inr fun h3 => h2 fun b hb => h3 b (Finset.mem_insert_of_mem hb)
    · exact Or.inr fun h3 => h1 (h3 a (Finset.mem_insert_self a s))

section Rees

variable {B : Type*} [CommRing B] {Φ : WFil B} (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)

/-- **Divisibility by `s` in the Rees algebra** from membership in the filtration. -/
theorem sdvd_dec_rees (hF : ∀ (j : ℤ) (g : B), g ∈ Φ.F j ∨ g ∉ Φ.F j) (p : ReesAlg Φ) :
    p ∈ Ideal.span {reesS Φ hneg} ∨ p ∉ Ideal.span {reesS Φ hneg} := by
  rw [mem_span_s_iff]
  rcases finset_forall_or_not (P := fun j => (p : B[T;T⁻¹]).coeff j ∈ Φ.F (j + 1))
      (p : B[T;T⁻¹]).coeff.support (fun j _ => hF (j + 1) _) with h | h
  · refine Or.inl fun j => ?_
    by_cases hj : j ∈ (p : B[T;T⁻¹]).coeff.support
    · exact h j hj
    · rw [Finsupp.notMem_support_iff.1 hj]; exact zero_mem _
  · exact Or.inr fun h' => h fun j _ => h' j

end Rees

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)

include hd hw in
/-- **Divisibility by `s` in `U`** from membership in the filtration: `U/sU = J_{R/sR}(h̄)`. -/
theorem sdvd_dec_torsor [Constructive.Enum A] [Fact (Constructive.HasPres A)] [Fact (∃ k, ChartDim A k)]
    (hF : ∀ (j : ℤ) (g : A), g ∈ (compFil hI hmax h𝔭 d).F j ∨ g ∉ (compFil hI hmax h𝔭 d).F j)
    (x : Torsor hI hmax h𝔭 d hπ) :
    algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)
        (reesS (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj)) ∣ x ∨
      ¬ algebraMap (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ)
        (reesS (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos hI hmax h𝔭 d hj)) ∣ x := by
  set R := ReesAlg (compFil hI hmax h𝔭 d)
  set s := reesS (compFil hI hmax h𝔭 d) (fun j hj => compFil_F_nonpos hI hmax h𝔭 d hj)
  have : (Ideal.span {s}).IsPrime := rees_s_prime hI hmax h𝔭 hd hw
  have : IsDomain (R ⧸ Ideal.span {s}) := (Ideal.Quotient.isDomain_iff_prime _).2 inferInstance
  have hzQ : ∀ q : R ⧸ Ideal.span {s}, q = 0 ∨ q ≠ 0 := by
    intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact sdvd_dec_rees _ hF p
  obtain ⟨j, hj1, hjd, g, hg, hgF⟩ := exists_gen_not_mem hI hmax h𝔭 hd hw
  obtain ⟨l, hl1, hl2⟩ := exists_index hI hmax h𝔭 (π := π) hj1 hjd hg
  have hl : (Ideal.Quotient.mk (Ideal.span {s}) ∘ torsorY hI hmax h𝔭 d hπ) l ≠ 0 := by
    simp only [Function.comp_apply, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    rw [mem_span_s_iff]
    intro hall
    apply hgF
    have := hall j
    simp only [torsorY, hl1, hl2, coeff_C_mul_T] at this
    exact this
  have hiff : algebraMap R (Torsor hI hmax h𝔭 d hπ) s ∣ x ↔
      Jou.redHom (torsorY hI hmax h𝔭 d hπ) s x = 0 := by
    rw [← RingHom.mem_ker, Jou.ker_redHom, Ideal.mem_span_singleton]
  rw [hiff]
  exact zeroTest_jou hzQ hl _

include hd hw in
/-- **The torsor with all decisions computed**, from those of `A` and membership in the `F_j`. -/
theorem torsor_dec_F [Constructive.Enum A] [Fact (HasPres A)] [Fact (∃ k, ChartDim A k)] (hG : HasGcd A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) (hdA : DvdDec A)
    (hk2 : v₀ 1 ≠ 0) (hπ0 : π ≠ 0)
    (hF : ∀ (j : ℤ) (g : A), g ∈ (compFil hI hmax h𝔭 d).F j ∨ g ∉ (compFil hI hmax h𝔭 d).F j) :
    HasGcd (Torsor hI hmax h𝔭 d hπ) ∧ (∀ x : Torsor hI hmax h𝔭 d hπ, x = 0 ∨ x ≠ 0) ∧
      DvdDec (Torsor hI hmax h𝔭 d hπ) :=
  torsor_dec hI hmax h𝔭 hd hw hπ hG hz hdA hk2 hπ0 (sdvd_dec_torsor hI hmax h𝔭 hd hw hπ hF)

end BezoutCounterexample.Principalization
