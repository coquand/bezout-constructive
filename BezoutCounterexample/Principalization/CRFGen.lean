import BezoutCounterexample.Principalization.MaxLocus

/-!
# `cRF` is multiplicative and trivial in non-positive degree, unconditionally (leaf)

`cRF I 𝔪 t` is an infimum of weighted ideals `J.RF t` of centres. Each term is multiplicative
(`Chart.RF_mul_le`) and is `⊤` for `t ≤ 0` (`Chart.RF_of_nonpos`), so the infimum is too, with no
hypothesis on `𝔪` and without `cRF_eq` (hence without `MC.exists_max_FT`). These are the proof
fields of `compFil` (ReesGlobal), which then need neither `LocusComp.mem` nor `cRF_eq`; likewise
`Iloc_le_cRF_one` for `I_le_compFil` (each centre in the infimum is admissible).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

variable {A : Type} [CommRing A] [Algebra ℚ A]

/-- `cRF` is multiplicative (no hypothesis). -/
lemma cRF_mul_le_gen (I 𝔪 : Ideal A) [𝔪.IsPrime] (s t : ℚ) :
    cRF I 𝔪 s * cRF I 𝔪 t ≤ cRF I 𝔪 (s + t) := by
  refine le_iInf fun n => le_iInf fun J => le_iInf fun hJ => le_iInf fun hJi => ?_
  refine (Ideal.mul_mono (iInf_le_of_le n (iInf_le_of_le J (iInf_le_of_le hJ (iInf_le _ hJi))))
    (iInf_le_of_le n (iInf_le_of_le J (iInf_le_of_le hJ (iInf_le _ hJi))))).trans ?_
  exact J.c.RF_mul_le J.e s t

/-- `cRF` is `⊤` in non-positive degree (no hypothesis). -/
lemma cRF_of_nonpos_gen (I 𝔪 : Ideal A) [𝔪.IsPrime] {t : ℚ} (ht : t ≤ 0) : cRF I 𝔪 t = ⊤ :=
  eq_top_iff.2 <| le_iInf fun _ => le_iInf fun J => le_iInf fun _ => le_iInf fun _ =>
    (J.c.RF_of_nonpos J.nonneg ht).ge

/-- The ideal lies in `cRF` at weight `1` (each centre is admissible; no hypothesis). -/
lemma Iloc_le_cRF_one (I 𝔪 : Ideal A) [𝔪.IsPrime] : Iloc I 𝔪 ≤ cRF I 𝔪 1 :=
  le_iInf fun _ => le_iInf fun _ => le_iInf fun hJ => le_iInf fun _ => hJ

end BezoutCounterexample.Principalization
