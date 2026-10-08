import BezoutCounterexample.Principalization.Centre
import BezoutCounterexample.Constructive.KrullP

/-!
# (F1) and (F2) from one chain condition (Perdry / Kuroki)

Variants of `Chart.IsCentred.tau_injective` (F1) and `Chart.IsCentred.mem_span_iff` (F2) in
which the Krull intersection theorem `Ideal.iInf_pow_eq_bot_of_isLocalRing` is replaced by
`Constructive.eq_zero_of_iInf`. The Noetherian hypothesis is replaced by the single named chain
condition `SeqCond` on the Rees ring of the maximal ideal (of `R`, resp. of `R ⧸ J`).
-/

namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing Constructive

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] {n : ℕ}

lemma isUnit_one_sub_of_mem_max {A : Type*} [CommRing A] [IsLocalRing A] {a : A}
    (ha : a ∈ maximalIdeal A) : IsUnit (1 - a) :=
  notMem_maximalIdeal.1 fun h => (maximalIdeal.isMaximal A).ne_top
    ((Ideal.eq_top_iff_one _).2 (by simpa using add_mem h ha))

namespace Chart

variable {c : Chart R n}

/-- **(F1)** The residual Taylor map of a centred chart is injective, from the chain condition on
the Rees ring of `𝔪` (no Noetherian hypothesis). -/
lemma IsCentred.tau_injective_of_seqCond (hc : c.IsCentred)
    (hN : SeqCond (reesSubring (maximalIdeal R))) : Function.Injective c.tau := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hmem : ∀ N : ℕ, f ∈ maximalIdeal R ^ N := fun N =>
    hc.RF_one_le_pow N ((hc.mem_RF_iff_of_ne (fun _ => zero_le_one) (fun _ => one_ne_zero) N
      f).2 fun β _ => by rw [hf, map_zero])
  exact eq_zero_of_iInf _ hN (fun _ ha => isUnit_one_sub_of_mem_max ha) hmem

/-- **(F2)** Relative order duality, from the chain condition on the Rees ring of the maximal
ideal of `R ⧸ (xᵢ : i ∈ S)` (no Noetherian hypothesis). -/
theorem IsCentred.mem_span_iff_of_seqCond (hc : c.IsCentred) (S : Set (Fin n)) (g : R)
    (hN : ∀ [IsLocalRing (R ⧸ Ideal.span (c.x '' S))],
      SeqCond (reesSubring (maximalIdeal (R ⧸ Ideal.span (c.x '' S))))) :
    g ∈ Ideal.span (c.x '' S) ↔
      ∀ δ : Fin n →₀ ℕ, (∀ i ∈ S, δ i = 0) → coeff δ (c.tau g) = 0 := by
  refine ⟨fun hg δ hδ => hc.coeff_tau_eq_zero_of_mem hg δ hδ, fun h0 => ?_⟩
  set J := Ideal.span (c.x '' S)
  have hN' : ∀ N, g ∈ J ⊔ maximalIdeal R ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => exact hc.mem_sup_pow_succ S N ih h0
  by_cases hJ : J = ⊤
  · rw [hJ]; trivial
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine eq_zero_of_iInf _ hN (fun _ ha => isUnit_one_sub_of_mem_max ha) fun N => ?_
  have hle : Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R) ≤ maximalIdeal (R ⧸ J) :=
    Ideal.map_le_iff_le_comap.2 fun r hr => by
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : R ⧸ J)
      have h1 : Ideal.Quotient.mk J (r * s) = 1 := by rw [map_mul, hs, ← hu, Units.mul_inv]
      have h2 : r * s - 1 ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
      have h3 : r * s - 1 ∈ maximalIdeal R := le_maximalIdeal hJ h2
      have h4 : r * s ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hr
      exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2
        (by simpa using sub_mem h4 h3))
  have := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) (hN' N)
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow] at this
  exact Ideal.pow_right_mono hle N this

end Chart

end BezoutCounterexample.Principalization
