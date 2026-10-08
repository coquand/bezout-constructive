import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesPres
import BezoutCounterexample.Principalization.ChartDim
import BezoutCounterexample.Constructive.ChainLiftReesModel

/-!
# The Rees algebra presented by any kernel list (Task B, Rees layer S6, §13 step 2)

`exists_reesPres` builds `ℚ[Y, s, y] ⧸ (GR) ≃+* ReesAlg Φ` for the list `GR` of `exists_reesKer`; the
proof uses only the kernel property of `GR`. The assembly appends the rows of all opens to the kernel
(`exists_reesKer_ext`), so the isomorphism is restated here for any `GR` with that property.

* `reesPresEquiv`: `ℚ[Y, s, y] ⧸ (GR) ≃+* ReesAlg Φ` from `hGR`;
* `chartDim_rees_of_cert`: a certificate of `GR` renamed along `ε` gives `ChartDim (ReesAlg Φ)`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

variable {A : Type} [CommRing A] [Algebra ℚ A] {m n r : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ))
  (e : SmoothCert.QB G ≃+* A)
  (gZ : Fin r → MvPolynomial (Fin (m + n)) ℤ) (δ : Fin r → ℕ)
  (Φ : WFil A) (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
  (hgF : ∀ i, toAq G e (toQZ (gZ i)) ∈ Φ.F (δ i))
  (hgen : ∀ (j : ℤ) (f : A), f ∈ Φ.F j →
    LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (insert (T (-1)) (Set.range (reesYL G e gZ δ))))
  (GR : List (MvPolynomial (Fin ((m + n) + (1 + r))) ℤ))
  (hGR : ∀ h, aeval (reesVec G e gZ δ) h = 0 ↔ h ∈ lspan (GR.map toQZ))

include hneg hgF hgen hGR in
/-- **The Rees algebra is presented by any kernel list** (the proof of `exists_reesPres`). -/
def reesPresEquiv :
    MvPolynomial (Fin ((m + n) + (1 + r))) ℚ ⧸ lspan (GR.map toQZ) ≃+* ReesAlg Φ :=
  have hker : RingHom.ker (reesPresMap G e gZ δ Φ hneg hgF) = lspan (GR.map toQZ) := by
    ext h
    rw [RingHom.mem_ker, ← hGR, ← Subtype.val_injective.eq_iff]
    rfl
  have hsurj : Function.Surjective (reesPresMap G e gZ δ Φ hneg hgF) := by
    rintro ⟨p, hp⟩
    obtain ⟨h, hh⟩ := reesAlg_le_range G e gZ δ Φ hneg hgF hgen hp
    exact ⟨h, Subtype.ext hh⟩
  (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

lemma reesPresEquiv_mk (h : MvPolynomial (Fin ((m + n) + (1 + r))) ℚ) :
    (reesPresEquiv G e gZ δ Φ hneg hgF hgen GR hGR (Ideal.Quotient.mk _ h) : A[T;T⁻¹]) =
      aeval (reesVec G e gZ δ) h := rfl

include hneg hgF hgen hGR in
/-- **Chart size of the Rees algebra** from a certificate of its kernel list in another layout. -/
theorem chartDim_rees_of_cert {m' n' : ℕ} (ε : Fin ((m + n) + (1 + r)) ≃ Fin (m' + n'))
    (hcert : Nonempty (SmoothCert m' n' (GR.map (rename ε)))) : ChartDim (ReesAlg Φ) n' :=
  ⟨m', GR.map (rename ε),
    ⟨(quotRenameEquiv GR ε).symm.trans (reesPresEquiv G e gZ δ Φ hneg hgF hgen GR hGR)⟩, hcert⟩

end BezoutCounterexample.Principalization
