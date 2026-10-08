import Mathlib
import BezoutCounterexample.Torsor
import BezoutCounterexample.Principalization.TorsorInv
import BezoutCounterexample.Principalization.ChainLiftSmoothCertK

/-!
# Chart size of the torsor (`chartDim_U`, Task A C5(b))

`chartDim_U`: if `A` has chart size `k` (`ChartDim A k`) and a zero test, the torsor `U` of a
principalization step has chart size `k + 1 + ℓ`. This replaces `ringKrullDim_U` (Krull dimension,
R5) on the constructive path; it feeds the `ChartDim` form of `Star.dim_le` (D3.5).

The chart pinning the dimension is built at the generic point `Q = ⊥` of `U`:
* `ChartDim.exists_chart`: a chart of `A` at a prime meeting `A` in `0`, from a piece of the
  certificate of `A` with `h ≠ 0` (found by the zero test along the cover `C = Σ uₖhₖ`);
* `reesChart`: a chart of the Rees algebra `R` at `PP = Q ∩ R` of size `k + 1`: `R_PP` is a
  localization of `A_{PA}[X]` by `X ↦ s = T⁻¹` (`reesθ`; injective by Laurent coefficients,
  every element a fraction because `r · s^M` is a polynomial in `s`);
* `U_Q` is a localization of `R_PP[σ_{≠l}]` (`theta2`, with `y₀ = πT ≠ 0`), adding `ℓ`.
Then the K primitive `exists_smoothCert_of_smooth` gives the certificate.
-/

noncomputable section

open MvPolynomial LaurentPolynomial BezoutCounterexample.Constructive

namespace BezoutCounterexample.Principalization

/-! ### A chart of `A` from its certificate -/

/-- Decided predicates on `Fin K`: one holds or none does. -/
lemma fin_exists_or_forall {K : ℕ} (p : Fin K → Prop) (hp : ∀ k, p k ∨ ¬ p k) :
    (∃ k, p k) ∨ ∀ k, ¬ p k := by
  induction K with
  | zero => exact Or.inr fun k => k.elim0
  | succ K ih =>
    rcases hp 0 with h | h
    · exact Or.inl ⟨0, h⟩
    · rcases ih (fun k => p k.succ) (fun k => hp k.succ) with ⟨k, hk⟩ | hk
      · exact Or.inl ⟨k.succ, hk⟩
      · exact Or.inr fun k => Fin.cases h hk k

/-- **A chart of `A` at a prime meeting `A` in `0`**, from a certificate and a zero test. -/
theorem ChartDim.exists_chart {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] {k : ℕ}
    (hA : ChartDim A k) (hz : ∀ a : A, a = 0 ∨ a ≠ 0) (𝔭 : Ideal A) [𝔭.IsPrime]
    (h𝔭 : ∀ a ∈ 𝔭, a = 0) : Nonempty (Chart (Localization.AtPrime 𝔭) k) := by
  obtain ⟨m, G, ⟨e⟩, ⟨hG⟩⟩ := hA
  have := Ideal.comap_isPrime (e : SmoothCert.QB G →+* A) 𝔭
  rcases fin_exists_or_forall (fun i => e (SquarePiece.mkQ G (hG.P i).h) ≠ 0)
      (fun i => (hz _).elim (fun h => Or.inr fun h' => h' h) Or.inl) with ⟨i, hi⟩ | hall
  · refine ⟨(hG.chartAt i (𝔭.comap (e : SmoothCert.QB G →+* A)) fun hmem => hi (h𝔭 _ hmem)).ofRingEquiv
      (ChartDim.locEquiv e 𝔭)⟩
  · exfalso
    have hcov := SmoothCert.ψ_eq_zero hG.cover
    rw [map_sub, map_natCast, map_sum, sub_eq_zero] at hcov
    have h0 : ((hG.C : ℕ) : SmoothCert.QB G) = 0 := by
      rw [hcov]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : SquarePiece.mkQ G (hG.P i).h = 0 := by
        rcases hz (e (SquarePiece.mkQ G (hG.P i).h)) with h | h
        · exact e.injective (by rw [h, map_zero])
        · exact absurd h (hall i)
      rw [map_mul, show SmoothCert.ψ G (hG.P i).h = SquarePiece.mkQ G (hG.P i).h from rfl, this,
        mul_zero]
    have hu : IsUnit ((hG.C : ℕ) : SmoothCert.QB G) := by
      rw [← map_natCast (algebraMap ℚ (SmoothCert.QB G))]
      exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hG.hC.ne')).map _
    haveI : Nontrivial (SmoothCert.QB G) := e.symm.injective.nontrivial
    exact hu.ne_zero h0

/-! ### The Rees chart -/

section Rees

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] (Φ : WFil B)
  (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)

lemma eval_reesS_val (p : Polynomial B) :
    ((Polynomial.eval₂ (algebraMap B (ReesAlg Φ)) (reesS Φ hneg) p : ReesAlg Φ) : B[T;T⁻¹]) =
      invert (Polynomial.toLaurent p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add, Subalgebra.coe_add, hp, hq, map_add, map_add]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, Subalgebra.coe_mul, SubmonoidClass.coe_pow,
      Polynomial.toLaurent_C_mul_T]
    simp only [Subalgebra.coe_algebraMap, ← LaurentPolynomial.C_eq_algebraMap, map_mul, invert_C,
      invert_T]
    rw [show ((reesS Φ hneg : ReesAlg Φ) : B[T;T⁻¹]) = T (-1) from rfl, T_pow]
    congr 2; ring

lemma exists_mul_pow_reesS (r : ReesAlg Φ) :
    ∃ (M : ℕ) (p : Polynomial B),
      r * reesS Φ hneg ^ M = Polynomial.eval₂ (algebraMap B (ReesAlg Φ)) (reesS Φ hneg) p := by
  obtain ⟨n, f', hf'⟩ := exists_T_pow (invert (r : B[T;T⁻¹]))
  refine ⟨n, f', Subtype.ext ?_⟩
  rw [eval_reesS_val, hf', map_mul, invert_T, involutive_invert]
  simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow]
  rw [show ((reesS Φ hneg : ReesAlg Φ) : B[T;T⁻¹]) = T (-1) from rfl, T_pow]
  congr 2; ring

variable [IsDomain (ReesAlg Φ)] (PP : Ideal (ReesAlg Φ)) [PP.IsPrime] (L : Type) [CommRing L]
  [Algebra (ReesAlg Φ) L] [IsLocalization.AtPrime L PP]

/-- `A_{PA}[X] → R_PP`, `X ↦ s = T⁻¹`. -/
def reesθ : Polynomial (Localization.AtPrime (PP.comap (algebraMap B (ReesAlg Φ)))) →+* L :=
  Polynomial.eval₂RingHom
    (IsLocalization.map (M := (PP.comap (algebraMap B (ReesAlg Φ))).primeCompl) L
      (algebraMap B (ReesAlg Φ)) (T := PP.primeCompl) fun _ hx => hx)
    (algebraMap (ReesAlg Φ) L (reesS Φ hneg))

lemma reesθ_map (p : Polynomial B) :
    reesθ Φ hneg PP L (p.map (algebraMap B (Localization.AtPrime (PP.comap (algebraMap B (ReesAlg Φ)))))) =
      algebraMap (ReesAlg Φ) L (Polynomial.eval₂ (algebraMap B (ReesAlg Φ)) (reesS Φ hneg) p) := by
  rw [reesθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  ext b
  simp only [RingHom.comp_apply]
  exact IsLocalization.map_eq _ b

lemma reesθ_injective : Function.Injective (reesθ Φ hneg PP L) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨b, hbmem, hb⟩ := IsLocalization.integerNormalization_spec
    (PP.comap (algebraMap B (ReesAlg Φ))).primeCompl p
  set p₀ := IsLocalization.integerNormalization (PP.comap (algebraMap B (ReesAlg Φ))).primeCompl p
  have hmap : p₀.map (algebraMap B _) = Polynomial.C (algebraMap B
      (Localization.AtPrime (PP.comap (algebraMap B (ReesAlg Φ)))) b) * p := by
    rw [hb, Algebra.smul_def, Polynomial.algebraMap_apply]
  have h1 : reesθ Φ hneg PP L (p₀.map (algebraMap B _)) = 0 := by
    rw [hmap, map_mul, hp, mul_zero]
  rw [reesθ_map] at h1
  have h2 := IsLocalization.injective L
    (Ideal.primeCompl_le_nonZeroDivisors PP) (h1.trans (map_zero _).symm)
  have h3 : Polynomial.toLaurent p₀ = 0 := by
    have := congrArg Subtype.val h2
    rw [eval_reesS_val] at this
    have h4 := congrArg invert this
    rwa [involutive_invert, ZeroMemClass.coe_zero, map_zero] at h4
  rw [Polynomial.toLaurent_eq_zero] at h3
  rw [h3, Polynomial.map_zero] at hmap
  have hu : IsUnit (algebraMap B (Localization.AtPrime (PP.comap (algebraMap B (ReesAlg Φ)))) b) :=
    IsLocalization.map_units _ (⟨b, hbmem⟩ : (PP.comap (algebraMap B (ReesAlg Φ))).primeCompl)
  exact ((hu.map Polynomial.C).mul_right_eq_zero).1 hmap.symm

lemma reesθ_surj (hs : reesS Φ hneg ∉ PP) (z : L) :
    ∃ a b, IsUnit (reesθ Φ hneg PP L b) ∧ z * reesθ Φ hneg PP L b = reesθ Φ hneg PP L a := by
  obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective PP.primeCompl z
  obtain ⟨M, p, hp⟩ := exists_mul_pow_reesS Φ hneg r
  obtain ⟨M', q, hq⟩ := exists_mul_pow_reesS Φ hneg (t : ReesAlg Φ)
  have hev : ∀ (f : Polynomial B) (n : ℕ),
      Polynomial.eval₂ (algebraMap B (ReesAlg Φ)) (reesS Φ hneg) (f * Polynomial.X ^ n) =
        Polynomial.eval₂ (algebraMap B (ReesAlg Φ)) (reesS Φ hneg) f * reesS Φ hneg ^ n := by
    intro f n; rw [Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]
  refine ⟨(p * Polynomial.X ^ M').map (algebraMap B _), (q * Polynomial.X ^ M).map (algebraMap B _),
    ?_, ?_⟩
  · rw [reesθ_map, hev, ← hq]
    refine IsLocalization.map_units _ (⟨_, ?_⟩ : PP.primeCompl)
    intro hmem
    rcases ‹PP.IsPrime›.mem_or_mem hmem with h | h
    · rcases ‹PP.IsPrime›.mem_or_mem h with h' | h'
      · exact t.2 h'
      · exact hs (‹PP.IsPrime›.mem_of_pow_mem _ h')
    · exact hs (‹PP.IsPrime›.mem_of_pow_mem _ h)
  · rw [reesθ_map, reesθ_map, hev, hev, ← hp, ← hq,
      show (t : ReesAlg Φ) * reesS Φ hneg ^ M' * reesS Φ hneg ^ M =
        (t : ReesAlg Φ) * (reesS Φ hneg ^ M' * reesS Φ hneg ^ M) by ring,
      map_mul, ← mul_assoc, IsLocalization.mk'_spec, ← map_mul]
    congr 1; ring

end Rees

/-! ### The torsor -/

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- A chart of `U` at `Q` from one of `R` at `Q ∩ R` (`theta2`). -/
lemma chartU_of [Constructive.Enum A] [Fact (Constructive.HasPres A)] (S : PrincipalizationData A) [IsDomain S.𝓡] (Q : Ideal S.U) [Q.IsPrime]
    {l : Fin (S.ℓ + 1)} (hyl : S.h l ∉ Q.comap (algebraMap S.𝓡 S.U)) {n : ℕ}
    (cR : Chart (Localization.AtPrime (Q.comap (algebraMap S.𝓡 S.U))) n) :
    Nonempty (Chart (Localization.AtPrime Q) (n + S.ℓ)) :=
  chart_of_mvLoc (theta2 S.h Q hyl) (theta2_injective _ Q hyl) (theta2_surj _ Q hyl) cR

/-- **The torsor has chart size `k + 1 + ℓ`** (replaces `ringKrullDim_U`). -/
theorem chartDim_U [Constructive.Enum A] [Fact (Constructive.HasPres A)] (S : PrincipalizationData A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0)
    (hU : HasPres S.U) {k : ℕ} (hA : ChartDim A k) : ChartDim S.U (k + 1 + S.ℓ) := by
  haveI : IsDomain S.𝓡 := S.rees_smooth_domain.1
  haveI : (⊥ : Ideal S.U).IsPrime := Ideal.isPrime_bot
  have hh0 : S.h 0 ≠ 0 := by
    intro h0
    have := congrArg Subtype.val h0
    rw [(S.h_spec 0).1, S.h_zero.1, ZeroMemClass.coe_zero] at this
    have h2 := congrArg (fun f : A[T;T⁻¹] => f.coeff (S.jdeg 0)) this
    rw [coeff_C_mul_T, if_pos rfl] at h2
    exact S.π_ne_zero (by simpa using h2)
  have hinjRU : Function.Injective (algebraMap S.𝓡 S.U) := Jou.algebraMap_injective hh0
  set PP := (⊥ : Ideal S.U).comap (algebraMap S.𝓡 S.U) with hPPdef
  have hPP : ∀ x ∈ PP, x = 0 := fun x hx =>
    hinjRU ((Ideal.mem_bot.1 (Ideal.mem_comap.1 hx)).trans (map_zero _).symm)
  have hs : S.s ∉ PP := fun h => by
    have := congrArg Subtype.val (hPP _ h)
    rw [S.s_coe, ZeroMemClass.coe_zero] at this
    exact (isUnit_T (-1 : ℤ)).ne_zero this
  have hyl : S.h 0 ∉ PP := fun h => hh0 (hPP _ h)
  have hinjAR : Function.Injective (algebraMap A S.𝓡) := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [Subalgebra.coe_algebraMap, ← LaurentPolynomial.C_eq_algebraMap] at this
    have h2 := congrArg (fun f : A[T;T⁻¹] => f.coeff 0) this
    simpa [LaurentPolynomial.C_apply] using h2
  obtain ⟨cA⟩ := hA.exists_chart hz (PP.comap (algebraMap A S.𝓡)) fun a ha =>
    hinjAR ((hPP _ ha).trans (map_zero _).symm)
  have hneg : ∀ j : ℤ, j ≤ 0 → S.fil.F j = ⊤ :=
    fun _j hj => compFil_F_nonpos S.ne_bot S.hmax S.h𝔭c S.d hj
  obtain ⟨cR⟩ := chart_of_polyLoc (reesθ S.fil hneg PP (Localization.AtPrime PP))
    (reesθ_injective S.fil hneg PP _) (reesθ_surj S.fil hneg PP _ hs) cA
  obtain ⟨cU⟩ := chartU_of S ⊥ hyl cR
  exact exists_smoothCert_of_smooth hU ⊥ (by omega) cU

end BezoutCounterexample.Principalization
