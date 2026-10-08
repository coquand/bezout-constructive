import BezoutCounterexample.Principalization.ChainLiftSmoothChart
import BezoutCounterexample.MarkedCenter

/-!
# Chart size from a smoothness certificate (D3.1; Task C plan C0/C3, `docs/d3-design.md`)

`ringKrullDim A = N` is replaced on the constructive path by `ChartDim A N`: `A` is isomorphic to
a presented ring `ℚ[Y_{m+N}]/(G)` with a smoothness certificate of dimension `N` (`SmoothCert`,
Task B). Every chart of every localization `A_𝔭` then has `N` functions (`ChartDim.card_eq`).

* `Chart.ofRingEquiv`: transport of a chart along a ring isomorphism (a localization at `⊥`).
* `SmoothCert.not_not_chart`: `¬¬` a chart of size `n` at every prime. There is no case split on
  `h_k ∈ 𝔭` (undecidable for an arbitrary prime): if no piece gives a chart, every `h_k` is
  `¬¬`-in `𝔭`, `¬¬` commutes with the finite conjunction (`not_not_forall_fin`), and the cover
  `C ≡ Σ u_k h_k` puts the unit `C` in `𝔭`.
* `ChartDim.card_eq`: `m = n` for a chart of size `m` at any prime; the `¬¬` is removed because
  `m = n` is decidable. `ChartDim.unique` (domains, the prime `⊥`).
* **`n ≥ 1`.** A `SquarePiece` has `0 < n`, so `SmoothCert m 0 G` has no pieces, its cover puts
  the unit `C` in `(G)`, and `QB G = 0`: `ChartDim A 0` is false for every nontrivial `A`. The
  lemmas here are uniform in `n` (none instantiates `n = 0`); users start from `N ≥ 1`
  (`A₀ = ℚ[x,y]`: `N = 2`).
* Off path, comparison only: `ChartDim.ringKrullDim_eq`, `chartDim_iff_ringKrullDim` and
  `chartDim_iff_forall_chart`. The converse directions need some certificate of `A`
  (`∃ k, ChartDim A k`), which is Task B's input, not a consequence of the classical statement.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

section Equiv

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] {n : ℕ}

/-- **Transport of a chart along a ring isomorphism**: `S` is the localization of `R` at `⊥`
through `e`, and ring maps between `ℚ`-algebras are `ℚ`-linear. -/
def Chart.ofRingEquiv (e : R ≃+* S) (c : Chart R n) : Chart S n :=
  letI : Algebra R S := e.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ R S := IsScalarTower.of_algebraMap_eq fun q =>
    congrArg (fun f : ℚ →+* S => f q)
      (RingHom.ext_rat (algebraMap ℚ S) (e.toRingHom.comp (algebraMap ℚ R)))
  haveI : IsLocalization (⊥ : Submonoid R) S := (isLocalization_iff_isLocalizationMap _ _).2
    { map_units := fun ⟨y, hy⟩ => by
        rw [Submonoid.mem_bot] at hy
        subst hy
        exact (map_one (algebraMap R S)).symm ▸ isUnit_one
      surj := fun z => ⟨(e.symm z, 1), by
        change z * e 1 = e (e.symm z)
        rw [map_one, mul_one, RingEquiv.apply_symm_apply]⟩
      exists_of_eq := fun {x y} h => ⟨1, by
        rw [OneMemClass.coe_one, one_mul, one_mul]
        exact e.injective h⟩ }
  c.localization (⊥ : Submonoid R)

end Equiv

/-- `¬¬` commutes with a finite conjunction. -/
lemma not_not_forall_fin : ∀ {K : ℕ} {P : Fin K → Prop}, (∀ k, ¬¬ P k) → ¬¬ ∀ k, P k
  | 0, _, _ => fun hn => hn fun k => k.elim0
  | _ + 1, P, h => fun hn =>
    h 0 fun h0 => not_not_forall_fin (P := fun k => P k.succ) (fun k => h k.succ) fun hs =>
      hn fun k => Fin.cases (motive := P) h0 hs k

end BezoutCounterexample.Principalization

namespace BezoutCounterexample.Constructive.SmoothCert

open BezoutCounterexample.Principalization

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}

/-- The image of `ℤ[Y]` in `ℚ[Y]/(G)`. -/
abbrev ψ (G : List (MvPolynomial (Fin (m + n)) ℤ)) : MvPolynomial (Fin (m + n)) ℤ →+* QB G :=
  (Ideal.Quotient.mk _).comp toQZ

lemma ψ_eq_zero {p : MvPolynomial (Fin (m + n)) ℤ} (hp : p ∈ lspan G) : ψ G p = 0 := by
  have h1 : (lspan G).map toQZ ≤ lspan (G.map toQZ) := by
    rw [lspan, lspan, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact Ideal.subset_span (List.mem_map_of_mem hg)
  exact Ideal.Quotient.eq_zero_iff_mem.2 (h1 (Ideal.mem_map_of_mem _ hp))

/-- **`¬¬` a chart of size `n` at every prime** of a certified ring. -/
theorem not_not_chart (hG : SmoothCert m n G) (𝔭 : Ideal (QB G)) [𝔭.IsPrime] :
    ¬¬ Nonempty (Principalization.Chart (Localization.AtPrime 𝔭) n) := fun hno =>
  not_not_forall_fin (P := fun k => SquarePiece.mkQ G (hG.P k).h ∈ 𝔭)
    (fun k hk => hno ⟨hG.chartAt k 𝔭 hk⟩) fun hall => by
      have hcov := ψ_eq_zero hG.cover
      rw [map_sub, map_natCast, map_sum, sub_eq_zero] at hcov
      have hC : ((hG.C : ℕ) : QB G) ∈ 𝔭 := hcov ▸ Ideal.sum_mem _ fun k _ => by
        rw [map_mul]; exact Ideal.mul_mem_left _ _ (hall k)
      have hu : IsUnit ((hG.C : ℕ) : QB G) := by
        rw [← map_natCast (algebraMap ℚ (QB G))]
        exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hG.hC.ne')).map _
      exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ hC hu)

end BezoutCounterexample.Constructive.SmoothCert

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive

/-- **Chart size `n`**: `A` is isomorphic to a presented ring with a smoothness certificate of
dimension `n` (Task B, `SmoothCert`). Replaces `ringKrullDim A = n` on the constructive path. -/
def ChartDim (A : Type) [CommRing A] [Algebra ℚ A] (n : ℕ) : Prop :=
  ∃ (m : ℕ) (G : List (MvPolynomial (Fin (m + n)) ℤ)),
    Nonempty (SmoothCert.QB G ≃+* A) ∧ Nonempty (SmoothCert m n G)

namespace ChartDim

variable {A : Type} [CommRing A] [Algebra ℚ A] {n : ℕ}

/-- The localizations at `𝔭.comap e` and `𝔭` along a ring isomorphism `e`. -/
def locEquiv {B : Type} [CommRing B] (e : B ≃+* A) (𝔭 : Ideal A) [𝔭.IsPrime]
    [(𝔭.comap (e : B →+* A)).IsPrime] :
    Localization.AtPrime (𝔭.comap (e : B →+* A)) ≃+* Localization.AtPrime 𝔭 :=
  IsLocalization.ringEquivOfRingEquiv (M := (𝔭.comap (e : B →+* A)).primeCompl)
    (T := 𝔭.primeCompl) _ _ e (by
    ext x
    refine ⟨?_, fun hx => ⟨e.symm x, ?_, e.apply_symm_apply x⟩⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · change e (e.symm x) ∉ 𝔭
      rw [e.apply_symm_apply]; exact hx)

/-- **`¬¬` a chart of size `n` at every prime.** -/
theorem not_not_chart (hn : ChartDim A n) (𝔭 : Ideal A) [𝔭.IsPrime] :
    ¬¬ Nonempty (Chart (Localization.AtPrime 𝔭) n) := fun hno => by
  obtain ⟨m, G, ⟨e⟩, ⟨hG⟩⟩ := hn
  have := Ideal.comap_isPrime (e : SmoothCert.QB G →+* A) 𝔭
  exact hG.not_not_chart _ fun ⟨c⟩ => hno ⟨c.ofRingEquiv (locEquiv e 𝔭)⟩

/-- **Every chart at a prime has size `n`.** Constructive: `m = n` is decidable. -/
theorem card_eq (hn : ChartDim A n) {𝔭 : Ideal A} [𝔭.IsPrime] {m : ℕ}
    (c : Chart (Localization.AtPrime 𝔭) m) : m = n :=
  Decidable.byContradiction fun hne => hn.not_not_chart 𝔭 fun ⟨c'⟩ => hne (Chart.card_eq c c')

/-- The chart size of a domain is unique. -/
theorem unique [IsDomain A] {n' : ℕ} (hn : ChartDim A n) (hn' : ChartDim A n') : n = n' :=
  letI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  Decidable.byContradiction fun hne =>
    hn.not_not_chart ⊥ fun ⟨c⟩ => hne (hn'.card_eq c)

/-! ### Comparison (off the constructive path) -/

section Comparison

variable [IsDomain A] [Algebra.Smooth ℚ A]

/-- The chart size is the Krull dimension. -/
theorem ringKrullDim_eq (hn : ChartDim A n) : ringKrullDim A = n :=
  letI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  Classical.byContradiction fun hne =>
    hn.not_not_chart ⊥ fun ⟨c⟩ => hne (chart_size_eq_ringKrullDim c)

end Comparison

end ChartDim

section Comparison

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A]

/-- For a certified ring, `ChartDim` is `ringKrullDim`. -/
theorem chartDim_iff_ringKrullDim [Algebra.Smooth ℚ A] (hA : ∃ k, ChartDim A k) (n : ℕ) :
    ChartDim A n ↔ ringKrullDim A = n := by
  refine ⟨ChartDim.ringKrullDim_eq, fun h => ?_⟩
  obtain ⟨k, hk⟩ := hA
  have hkn : (k : WithBot ℕ∞) = n := hk.ringKrullDim_eq.symm.trans h
  obtain rfl : k = n := by exact_mod_cast hkn
  exact hk

/-- For a certified ring, `ChartDim` is the size of every chart at every prime. -/
theorem chartDim_iff_forall_chart (hA : ∃ k, ChartDim A k) (n : ℕ) :
    ChartDim A n ↔
      ∀ (𝔭 : Ideal A) [𝔭.IsPrime] (m : ℕ), Chart (Localization.AtPrime 𝔭) m → m = n := by
  refine ⟨fun hn 𝔭 _ m c => hn.card_eq c, fun h => ?_⟩
  obtain ⟨k, hk⟩ := hA
  have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  obtain rfl : k = n := Decidable.byContradiction fun hne =>
    hk.not_not_chart ⊥ fun ⟨c⟩ => hne (h ⊥ k c)
  exact hk

end Comparison

end BezoutCounterexample.Principalization
