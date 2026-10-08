import BezoutCounterexample.Principalization.MaxLocus

/-!
# Chart facts at primes (D3.3d)

Generic facts about charts, moved from `Principalization/{Torsor, TorsorDer}.lean` so that
`MarkedCenter` need not import the torsor layer (`docs/d3-design.md` §4: import order). With this,
`PosCover`/`ChartDim` → `MarkedCenter` no longer reach `Principalization/{Torsor, …, Divisorial}`,
and the Rees/torsor layer can import the point forms (`MaxLocusPt`, `ComponentFilPt`).

* `Chart.IsCentred.x_not_mem_RF`: a chart coordinate is not in the next weighted ideal.
* `chart_card_eq_of_domain`, `exists_chart_atPrime`: chart sizes on a domain.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization MvPowerSeries

/-- A chart coordinate is not in the next weighted ideal. -/
lemma Chart.IsCentred.x_not_mem_RF {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S]
    {n : ℕ} {c : Chart S n} (hc : c.IsCentred) {e : Fin n → ℚ}
    (he : ∀ i, 0 ≤ e i) (i : Fin n) {t : ℚ} (ht : e i < t) : c.x i ∉ c.RF e t := by
  intro hmem
  have := hc.coeff_tau_eq_zero_of_mem_RF he hmem (Finsupp.single i 1)
    (by rw [lam_single]; simpa using ht)
  rw [Chart.coeff_tau, Chart.Dv_single_one, c.d_x_self, map_one] at this
  exact one_ne_zero this

/-- **Chart sizes are constant on a domain.** -/
lemma chart_card_eq_of_domain {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] (𝔭 𝔮 : Ideal B)
    [𝔭.IsPrime] [𝔮.IsPrime] {n n' : ℕ} (c : Chart (Localization.AtPrime 𝔭) n)
    (c' : Chart (Localization.AtPrime 𝔮) n') : n = n' :=
  Chart.card_eq (Loc.transport (Ideal.primeCompl_le_nonZeroDivisors 𝔭) c)
    (Loc.transport (Ideal.primeCompl_le_nonZeroDivisors 𝔮) c')

lemma exists_chart_atPrime {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B]
    (p : Ideal B) [p.IsPrime] : ∃ n, Nonempty (Chart (Localization.AtPrime p) n) := by
  obtain ⟨f, hf, n, ⟨c⟩⟩ := exists_chart_away p
  have h : Submonoid.powers f ≤ p.primeCompl := (Submonoid.powers_le).2 hf
  exact ⟨n, ⟨Loc.transport h c⟩⟩

end BezoutCounterexample.Principalization
