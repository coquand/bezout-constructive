import BezoutCounterexample.Constructive.PosOrd
import BezoutCounterexample.Constructive.ChartP
import BezoutCounterexample.Constructive.KrullBar
import BezoutCounterexample.MarkedCenter

/-!
# The order at a centred chart, computed (Task D, R6; roadmap §1.1, §1.6)

* `Chart.pos_ord_local`: in a local ring `R` with `[Fact (PolyIndNoeth R)]`, a centred chart `c`
  and a decided residue field (`x ∈ 𝔪 ∨ IsUnit x`; at an explicit point `z`: `z(x) = 0` or
  `z(x) ≠ 0` in `L`), every explicit ideal `(l)` is `0` generator by generator, or has an order
  `k` (`IsOrd`) with a witness: a generator and a chart derivative of degree `k` which is a unit.
  The Rees bar of `𝔪 = (x)` comes from `PolyIndNoeth` (`indNoeth_rees_lspan`); no `sSup`, no
  `Submodule.exists_mem_ne_zero_of_ne_bot`, no Krull intersection, no Markov.
* `ord_eq_of_isOrd` (comparison, off the constructive path): the classical
  `MarkedCenter.ord` (`sSup`) is this computed value.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing Constructive

section Local

variable {R : Type*} [CommRing R] [IsLocalRing R] [Algebra ℚ R] {n : ℕ}

/-- The chart `c` as a `PChart` (all coordinates). -/
def Chart.toP (c : Chart R n) : PChart R n := subP c id Function.injective_id

omit [IsLocalRing R] in
lemma Chart.toP_P (c : Chart R n) : c.toP.P = Ideal.span (Set.range c.x) := rfl

/-- **Positive order at a centred chart.** -/
theorem Chart.pos_ord_local [h : Fact (PolyIndNoeth R)] (c : Chart R n) (hc : c.IsCentred)
    (hdec : ∀ x : R, x ∈ maximalIdeal R ∨ IsUnit x) (l : List R) :
    (∀ f ∈ l, f = 0) ∨ ∃ k, IsOrd (lspan l) (maximalIdeal R) k ∧
      ∃ f ∈ l, ∃ α, deg α = k ∧ IsUnit (c.toP.D α f) := by
  have hP : c.toP.P = maximalIdeal R := by rw [Chart.toP_P, hc]
  have hR : IndNoeth (reesSubring c.toP.P) := by
    have hl := PolyIndNoeth.indNoeth_rees_lspan h.out (List.ofFn c.x)
    have he : lspan (List.ofFn c.x) = c.toP.P := by
      rw [Chart.toP_P, lspan]
      congr 1
      ext y
      simp [List.mem_ofFn]
    rwa [he] at hl
  have hloc : ∀ a ∈ c.toP.P, IsUnit (1 - a) := fun a ha => by
    rw [hP] at ha
    rcases hdec (1 - a) with h1 | hu
    · have h1' : (1 : R) ∈ maximalIdeal R := by simpa using Ideal.add_mem _ h1 ha
      exact absurd ((Ideal.eq_top_iff_one _).2 h1') (maximalIdeal.isMaximal R).ne_top
    · exact hu
  have hE : ∀ x, IsUnit x → x ∉ c.toP.P := fun x hx hm => by
    rw [hP] at hm; exact (mem_maximalIdeal x).1 hm hx
  rcases pos_ordL hR hloc (E := IsUnit) (fun x => by rw [hP]; exact hdec x) l with h0 | ⟨k, hk⟩
  · exact Or.inl h0
  · refine Or.inr ⟨k, ?_, hk.2⟩
    rw [← hP]; exact hk.isOrd hE

end Local

/-- **Comparison**: the classical `ord` (`sSup`) is the computed order. -/
theorem ord_eq_of_isOrd {A : Type*} [CommRing A] {I 𝔪 : Ideal A} [𝔪.IsPrime] {k : ℕ}
    (hk : IsOrd (I.map (algebraMap A (Localization.AtPrime 𝔪)))
      (maximalIdeal (Localization.AtPrime 𝔪)) k) : ord I 𝔪 = k :=
  IsGreatest.csSup_eq ⟨hk.1, fun b hb => hk.2 b hb⟩

end BezoutCounterexample.Principalization
