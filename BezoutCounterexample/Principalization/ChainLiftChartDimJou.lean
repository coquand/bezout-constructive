import Mathlib
import BezoutCounterexample.Jouanolou
import BezoutCounterexample.Constructive.ChainLiftJouCert
import BezoutCounterexample.Principalization.ChartDim
import BezoutCounterexample.Principalization.ChainLiftBridgePres
import BezoutCounterexample.Constructive.PresentedOps

/-!
# Chart size of a Jouanolou ring (Task B, S6: the `U`-layer of `chartDim_U` by certificates)

`ChartDim.jou`: if `B` has chart size `n`, then `J_B(c) = B[σ₀ … σ_r]/(Σ cₖσₖ − 1)` has chart size
`n + r`. The certificate is `SmoothCert.jou` (ChainLiftJouCert), in the presentation `jouG G p`;
here only the ring isomorphism `QB (jouG G p) ≃ J_B(c)` is built.

* The coefficients `cₖ ∈ B` have integer lifts only up to a common denominator: `pₖ ↦ D cₖ`
  (`exists_int_mul_fin`). The isomorphism rescales `σₖ ↦ D⁻¹ σₖ` (`jouEquiv`), so the equation
  `Σ pₖσₖ − 1` goes to `Σ cₖσₖ − 1`.
* `ChartDim` is existential in the presentation, so no transport of the certificate to another
  presentation of `J_B(c)` is needed.

Used for the torsor `U = J_𝓡(h)` once the Rees algebra `𝓡` has a certificate (S6).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive BezoutCounterexample.Constructive.JouCert

namespace JouDim

variable {m n r : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ))
  (p : Fin (r + 1) → MvPolynomial (Fin (m + n)) ℤ) (D : ℕ)
  (c : Fin (r + 1) → SmoothCert.QB G)

/-- The quotient map onto `B = ℚ[Y]/(G)`. -/
abbrev mkB : MvPolynomial (Fin (m + n)) ℚ →+* SmoothCert.QB G := Ideal.Quotient.mk _

/-- The quotient map onto `ℚ[Y, σ]/(G, Σ pₖσₖ − 1)`. -/
abbrev mkJ : MvPolynomial (Fin ((m + 1) + (n + r))) ℚ →+* SmoothCert.QB (jouG G p) :=
  Ideal.Quotient.mk _

/-- The old variables among the new ones. -/
abbrev fY (m n r : ℕ) : Fin (m + n) → Fin ((m + 1) + (n + r)) := fun i => colE m n r (Sum.inl i)

/-- The images of the variables in `J_B(c)`: `Yᵢ ↦ Yᵢ`, `σₖ ↦ D⁻¹ σₖ`. -/
def phiVar (j : Fin ((m + 1) + (n + r))) : Jou.J c :=
  Sum.elim (fun i => Jou.mk c (C (mkB G (X i))))
    (fun k => algebraMap ℚ (Jou.J c) (D : ℚ)⁻¹ * Jou.σ c k) ((colE m n r).symm j)

/-- `ℚ[Y, σ] → J_B(c)`. -/
def phi0 : MvPolynomial (Fin ((m + 1) + (n + r))) ℚ →+* Jou.J c :=
  eval₂Hom (algebraMap ℚ (Jou.J c)) (phiVar G D c)

lemma phi0_rename (q : MvPolynomial (Fin (m + n)) ℚ) :
    phi0 G D c (rename (fY m n r) q) = Jou.mk c (C (mkB G q)) := by
  have : (phi0 G D c).comp (rename (fY m n r)).toRingHom =
      ((Jou.mk c).toRingHom.comp C).comp (mkB G) := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_rat _ _) fun i => ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, phi0,
      coe_eval₂Hom, eval₂_X, phiVar, Equiv.symm_apply_apply, Sum.elim_inl]
  exact congrArg (fun f => f q) this

lemma phi0_σ (k : Fin (r + 1)) :
    phi0 G D c (X (σv m n k)) = algebraMap ℚ (Jou.J c) (D : ℚ)⁻¹ * Jou.σ c k := by
  simp only [phi0, coe_eval₂Hom, eval₂_X, phiVar, σv, Equiv.symm_apply_apply, Sum.elim_inr]

variable {G p D c}

lemma phi0_ker (hD : 0 < D) (hc : ∀ k, mkB G (toQZ (p k)) = D * c k) :
    lspan ((jouG G p).map toQZ) ≤ RingHom.ker (phi0 G D c) := by
  rw [lspan, Ideal.span_le]
  intro g₀ hg₀
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg₀
  rcases List.mem_append.1 hg with hg' | hg'
  · obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg'
    change phi0 G D c (toQZ (rename (fY m n r) g1)) = 0
    rw [map_rename, phi0_rename]
    have : mkB G (toQZ g1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (List.mem_map_of_mem hg1))
    rw [this, map_zero, map_zero]
  · rw [List.mem_singleton.1 hg']
    change phi0 G D c (toQZ (eqn p)) = 0
    have hD' : ((D : ℚ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
    have hrel : Jou.mk c (∑ i, C (c i) * X i - 1) = 0 := by rw [← Jou.rel_eq]; exact Jou.mk_rel c
    simp only [eqn, map_sub, map_sum, map_mul, map_one, Y, map_rename, phi0_rename, hc]
    rw [← hrel, map_sub, map_sum, map_one]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_X, phi0_σ, map_natCast C, map_natCast (Jou.mk c), Jou.σ]
    have h1 : ((D : Jou.J c)) * algebraMap ℚ (Jou.J c) (D : ℚ)⁻¹ = 1 := by
      rw [← map_natCast (algebraMap ℚ (Jou.J c)), ← map_mul, mul_inv_cancel₀ hD', map_one]
    calc (D : Jou.J c) * Jou.mk c (C (c k)) * (algebraMap ℚ (Jou.J c) (D : ℚ)⁻¹ * Jou.mk c (X k))
        = ((D : Jou.J c) * algebraMap ℚ (Jou.J c) (D : ℚ)⁻¹) * Jou.mk c (C (c k)) *
            Jou.mk c (X k) := by ring
      _ = _ := by rw [h1, one_mul, map_mul]

variable (G p D c)

/-- `B → ℚ[Y, σ]/(G, Σ pₖσₖ − 1)`. -/
def psiB : SmoothCert.QB G →+* SmoothCert.QB (jouG G p) :=
  Ideal.Quotient.lift _ ((mkJ G p).comp (rename (fY m n r)).toRingHom) (by
    intro a ha
    have hle : (lspan (G.map toQZ)).map (rename (fY m n r)) ≤ lspan ((jouG G p).map toQZ) := by
      rw [lspan, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨g₀, hg₀, rfl⟩
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg₀
      refine Ideal.subset_span (List.mem_map.2 ⟨Y r g, ?_, ?_⟩)
      · exact List.mem_append_left _ (List.mem_map_of_mem hg)
      · exact map_rename _ _ _
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.mem_map_of_mem _ ha)))

lemma psiB_mk (q : MvPolynomial (Fin (m + n)) ℚ) :
    psiB G p (mkB G q) = mkJ G p (rename (fY m n r) q) := rfl

/-- `B[σ] → ℚ[Y, σ]/(G, Σ pₖσₖ − 1)`, `σₖ ↦ D σₖ`. -/
def psi0 : MvPolynomial (Fin (r + 1)) (SmoothCert.QB G) →+* SmoothCert.QB (jouG G p) :=
  eval₂Hom (psiB G p) fun k => (D : SmoothCert.QB (jouG G p)) * mkJ G p (X (σv m n k))

variable {G p D c}

lemma psi0_rel (hc : ∀ k, mkB G (toQZ (p k)) = D * c k) : psi0 G p D (Jou.rel c) = 0 := by
  have h0 : mkJ G p (toQZ (eqn p)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (List.mem_map_of_mem
      (List.mem_append_right _ (List.mem_singleton_self _))))
  rw [← h0]
  simp only [Jou.rel, psi0, map_sub, map_sum, map_mul, coe_eval₂Hom, eval₂_X, eval₂_C, map_one,
    eqn, Y, map_rename]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← psiB_mk, hc k, map_mul, map_natCast, map_X]
  ring

variable (G p D c)

/-- `J_B(c) → ℚ[Y, σ]/(G, Σ pₖσₖ − 1)`. -/
def psi (hc : ∀ k, mkB G (toQZ (p k)) = D * c k) : Jou.J c →+* SmoothCert.QB (jouG G p) :=
  Ideal.Quotient.lift _ (psi0 G p D) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, psi0_rel hc, mul_zero])

/-- `ℚ[Y, σ]/(G, Σ pₖσₖ − 1) → J_B(c)`. -/
def phi (hD : 0 < D) (hc : ∀ k, mkB G (toQZ (p k)) = D * c k) :
    SmoothCert.QB (jouG G p) →+* Jou.J c :=
  Ideal.Quotient.lift _ (phi0 G D c) fun _ ha => phi0_ker hD hc ha

/-- **`ℚ[Y, σ]/(G, Σ pₖσₖ − 1) ≃ J_B(c)`** when `pₖ ↦ D cₖ`. -/
def jouEquiv (hD : 0 < D) (hc : ∀ k, mkB G (toQZ (p k)) = D * c k) :
    SmoothCert.QB (jouG G p) ≃+* Jou.J c :=
  RingEquiv.ofRingHom (phi G p D c hD hc) (psi G p D c hc)
    (by
      have hD' : ((D : ℚ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
      refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun b => ?_) fun k => ?_)
      · obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
        have : ((phi G p D c hD hc).comp (psi G p D c hc)).comp ((Jou.mk c).toRingHom.comp
            ((C : SmoothCert.QB G →+* _).comp (mkB G))) =
            ((Jou.mk c).toRingHom.comp ((C : SmoothCert.QB G →+* _).comp (mkB G))) := by
          refine MvPolynomial.ringHom_ext' (RingHom.ext_rat _ _) fun i => ?_
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
          change phi G p D c hD hc (psi0 G p D (C (mkB G (X i)))) = _
          rw [psi0, coe_eval₂Hom, eval₂_C, psiB_mk]
          exact phi0_rename G D c (X i)
        exact congrArg (fun f => f q) this
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        change phi G p D c hD hc (psi0 G p D (X k)) = Jou.mk c (X k)
        rw [psi0, coe_eval₂Hom, eval₂_X, map_mul, map_natCast]
        change (D : Jou.J c) * phi0 G D c (X (σv m n k)) = _
        rw [phi0_σ, ← mul_assoc, ← map_natCast (algebraMap ℚ (Jou.J c)), ← map_mul,
          mul_inv_cancel₀ hD', map_one, one_mul]
        rfl)
    (by
      have hD' : ((D : ℚ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
      refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext' (RingHom.ext_rat _ _) fun j => ?_)
      obtain ⟨s, rfl⟩ := (colE m n r).surjective j
      rcases s with i | k
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        change psi G p D c hc (phi0 G D c (X (fY m n r i))) = _
        rw [← rename_X (fY m n r) i, phi0_rename]
        change psi0 G p D (C (mkB G (X i))) = _
        rw [psi0, coe_eval₂Hom, eval₂_C, psiB_mk, rename_X]
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        change psi G p D c hc (phi0 G D c (X (σv m n k))) = _
        rw [phi0_σ, map_mul, RingHom.map_rat_algebraMap]
        change algebraMap ℚ _ (D : ℚ)⁻¹ * psi0 G p D (X k) = _
        rw [psi0, coe_eval₂Hom, eval₂_X, ← mul_assoc,
          ← map_natCast (algebraMap ℚ (SmoothCert.QB (jouG G p))), ← map_mul,
          inv_mul_cancel₀ hD', map_one, one_mul])

end JouDim

/-- `J_B(c) ≃ J_{B'}(e c)` along `e : B ≃ B'`. -/
def Jou.mapEquiv {B B' : Type*} [CommRing B] [CommRing B'] {r : ℕ} (e : B ≃+* B')
    (c : Fin r → B) (c' : Fin r → B') (h : ∀ k, e (c k) = c' k) : Jou.J c ≃+* Jou.J c' :=
  Ideal.quotientEquiv _ _ (MvPolynomial.mapEquiv (Fin r) e) (by
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
    simp [Jou.rel, map_sum, h])

/-- **Chart size of a Jouanolou ring**: `ChartDim B n → ChartDim (J_B(c)) (n + r)`. -/
theorem ChartDim.jou {B : Type} [CommRing B] [Algebra ℚ B] {n r : ℕ} (hB : ChartDim B n)
    (c : Fin (r + 1) → B) : ChartDim (Jou.J c) (n + r) := by
  obtain ⟨m, G, ⟨e⟩, ⟨hG⟩⟩ := hB
  have hq : ∀ k, ∃ q : MvPolynomial (Fin (m + n)) ℚ, JouDim.mkB G q = e.symm (c k) :=
    fun k => Ideal.Quotient.mk_surjective _
  obtain ⟨q, hq⟩ := fin_choice hq
  obtain ⟨D, p, hD, hp⟩ := exists_int_mul_fin q
  have hc : ∀ k, JouDim.mkB G (toQZ (p k)) = D * e.symm (c k) := fun k => by
    change JouDim.mkB G (toQ (p k)) = _
    rw [hp k, map_mul, map_natCast, hq k]
  refine ⟨m + 1, jouG G p, ⟨?_⟩, ⟨hG.jou p⟩⟩
  exact (JouDim.jouEquiv G p D _ hD hc).trans
    (Jou.mapEquiv e _ c fun k => e.apply_symm_apply (c k))

end BezoutCounterexample.Principalization
