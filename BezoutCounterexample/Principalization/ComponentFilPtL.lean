import BezoutCounterexample.Principalization.ComponentFilPt
import BezoutCounterexample.Principalization.LocDataPtProd

/-!
# I3 at explicit points without the maximal centre (leaf)

`cRF_eq` (MaxLocus) identifies `cRF I 𝔪 t`, the infimum over admissible centres with the invariant
as weights, with the weighted ideal of one of them; it uses `MC.exists_max_FT` (a maximal
admissible centre, classical) to see that all of them have the same weighted ideals. The field
`rf` of `LocDataPt` already says this at every explicit point `p ∌ g`, so:

* `cRF_eq_of_rf`: an invariant `ek` and one ideal `R` that every admissible centre with weights
  `ek` has as weighted ideal give `cRF I 𝔪 t = R` (`IsInv.card_eq`, `IsInv.unique`).
* `LocDataPt.cRF_eq_pt`, `P_le_cRF_pt`, `P_pow_le_pt`: twins of `LocData.cRF_eq_transport`,
  `P_le_cRF`, `P_pow_le`.
* `LocusComp.pow_le_compFPt_ptL`, `LocusComp.exists_pow_mem_compFPt_ptL` (I3): over `mem_ptL`,
  `LocDataPt.nonempty`, `eq_p_ptL` (no `LocData.nonempty`, no `cRF_eq`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- **`cRF` without the maximal centre**: if every admissible centre with weights `ek` has
weighted ideal `R`, and `ek` is the invariant, then `cRF I 𝔪 t = R`. -/
lemma cRF_eq_of_rf {I 𝔪 : Ideal A} [𝔪.IsMaximal] {n : ℕ} {ek : Fin n → ℚ}
    (hinv : IsInv (Iloc I 𝔪) n ek) {t : ℚ} {R : Ideal (Localization.AtPrime 𝔪)}
    (hrf : ∀ J' : MC (Localization.AtPrime 𝔪) n, J'.Adm (Iloc I 𝔪) → J'.e = ek → J'.RF t = R) :
    cRF I 𝔪 t = R := by
  obtain ⟨⟨J, hJ, hJe⟩, hmin⟩ := hinv
  have hJi : IsInv (Iloc I 𝔪) n J.e := ⟨⟨J, hJ, rfl⟩, by rw [hJe]; exact hmin⟩
  refine le_antisymm ?_ ?_
  · rw [← hrf J hJ hJe]
    exact iInf_le_of_le n (iInf_le_of_le J (iInf_le_of_le hJ (iInf_le _ hJi)))
  · refine le_iInf fun n' => le_iInf fun J' => le_iInf fun hJ' => le_iInf fun hJi' => ?_
    obtain rfl := hJi.card_eq J'.c
    rw [hrf J' hJ' ((hJi'.unique hJi).trans hJe)]

namespace LocDataPt

variable {I : Ideal A} {v₀ : ℕ → ℚ}

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- `cRF` at the point of local data is the chart's weighted ideal (twin of
`LocData.cRF_eq_transport`, without `cRF_eq`). -/
lemma cRF_eq_pt {p : Pt A} (D : LocDataPt I v₀ p.ker) (t : ℚ) :
    cRF I p.ker t = (Loc.transport (D.ctrl p.ker D.hg) D.ck).RF D.ek t :=
  cRF_eq_of_rf D.inv fun J' hJ' hJe => D.rf p D.hg J' hJ' hJe t

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma le_pt {p : Pt A} (D : LocDataPt I v₀ p.ker) : I ≤ p.ker := by
  obtain ⟨⟨J, hJ, -⟩, -⟩ := D.inv
  exact le_of_Iloc_le (hJ.trans (J.centred.RF_le_maximalIdeal one_pos))

variable {d : ℕ} (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hd hw

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma le_ek_pt {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocDataPt I v₀ 𝔪) {i : Fin D.n}
    (hi : D.ek i ≠ 0) : 1 / (d : ℚ) ≤ D.ek i := by
  obtain ⟨w, hw'⟩ := hw i
  have hv : v₀ i = D.ek i := by
    have := congrFun D.hv (i : ℕ); rw [ext0_apply] at this; exact this.symm
  rw [hv] at hw'
  have hpos : 0 < D.ek i := lt_of_le_of_ne (D.inv.nonneg i) (Ne.symm hi)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hw0 : (0 : ℚ) < w := by rw [hw']; positivity
  have hw1 : (1 : ℚ) ≤ w := by
    have : 0 < w := by exact_mod_cast hw0
    exact_mod_cast this
  rw [div_le_iff₀ hdq]
  linarith [hw']

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma P_le_cRF_pt {p : Pt A} (D : LocDataPt I v₀ p.ker) : D.P ≤ cRF I p.ker (1 / d) := by
  rw [D.cRF_eq_pt, LocDataPt.P, Ideal.span_le]
  rintro _ ⟨i, hi, rfl⟩
  have hne : D.ek i ≠ 0 := (D.supp i).2 hi
  exact (Loc.transport _ D.ck).RF_antitone D.ek (D.le_ek_pt hd hw hne)
    ((Loc.transport _ D.ck).x_mem_RF D.ek i hne)

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma P_pow_le_pt {p : Pt A} (D : LocDataPt I v₀ p.ker) (N : ℕ) :
    D.P ^ N ≤ cRF I p.ker (N / d) := by
  induction N with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_div, D.cRF_eq_pt,
      (Loc.transport _ D.ck).RF_of_nonpos D.inv.nonneg le_rfl]
    exact le_top
  | succ N ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono ih (D.P_le_cRF_pt hd hw)).trans ?_
    rw [D.cRF_eq_pt, D.cRF_eq_pt, D.cRF_eq_pt, Nat.cast_succ, add_div]
    exact (Loc.transport _ D.ck).RF_mul_le D.ek _ _

end LocDataPt

section Locus

variable {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l)
  (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
  {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hl hchart hmax h𝔭 hd hw

namespace LocusComp

/-- **Powers of a component lie in its filtration**, at points (twin of `pow_le_compFPt`). -/
theorem pow_le_compFPt_ptL [Fact (HasPres A)] (N : ℕ) : 𝔭 ^ N ≤ compFPt I 𝔭 (N / d) := by
  intro f hf
  rw [mem_compFPt]
  intro p h𝔭p
  obtain ⟨hIp, hv⟩ := h𝔭.mem_ptL hI l hl hchart hmax p h𝔭p
  obtain ⟨f₀, hf₀, n₀, ⟨c₀⟩⟩ := hchart p
  obtain ⟨D⟩ := LocDataPt.nonempty hI l hl p hIp hv hf₀ c₀
  have hp : 𝔭 = D.p := h𝔭.eq_p_ptL D h𝔭p
  have h1 : algebraMap A (Localization.AtPrime p.ker) f ∈ (𝔭 ^ N).map (algebraMap A _) :=
    Ideal.mem_map_of_mem _ hf
  rw [Ideal.map_pow, hp, D.map_p] at h1
  exact D.P_pow_le_pt hd hw N h1

/-- **I3 at points**: an element of the component has a power in each step of the filtration
(twin of `exists_pow_mem_compFPt`). -/
theorem exists_pow_mem_compFPt_ptL [Fact (HasPres A)] {i : A} (hi : i ∈ 𝔭) (t : ℚ) :
    ∃ b : ℕ, i ^ b ∈ compFPt I 𝔭 t := by
  obtain ⟨b, hb⟩ := exists_nat_ge (t * d)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  refine ⟨b, ?_⟩
  have h := h𝔭.pow_le_compFPt_ptL hI l hl hchart hmax hd hw b (Ideal.pow_mem_pow hi b)
  refine mem_compFPt.2 fun p h𝔭p => ?_
  have h' := mem_compFPt.1 h p h𝔭p
  obtain ⟨hIp, hv⟩ := h𝔭.mem_ptL hI l hl hchart hmax p h𝔭p
  obtain ⟨f₀, hf₀, n₀, ⟨c₀⟩⟩ := hchart p
  obtain ⟨D⟩ := LocDataPt.nonempty hI l hl p hIp hv hf₀ c₀
  rw [D.cRF_eq_pt] at h' ⊢
  exact (Loc.transport _ D.ck).RF_antitone D.ek
    (by rw [le_div_iff₀ hdq]; exact_mod_cast hb) h'

end LocusComp

end Locus

/-! ### I3 and `F_{1/d} = 𝔭` at points, with the data of `LocusComp` (signatures of the
classical ones) -/

section P

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭)

namespace LocusComp

include hI hmax h𝔭

/-- `compFPt_antitone'` at points (`LocDataPt.cRF_eq_pt` in place of `cRF_eq`). -/
theorem compFPt_antitoneP' {s t : ℚ} (hst : s ≤ t) : compFPt I 𝔭 t ≤ compFPt I 𝔭 s := by
  obtain ⟨l, hl⟩ := h𝔭.gensI
  intro f hf
  rw [mem_compFPt] at hf ⊢
  intro p h𝔭p
  obtain ⟨hIp, hv⟩ := h𝔭.mem_ptL hI l hl h𝔭.hchart hmax p h𝔭p
  obtain ⟨f₀, hf₀, n₀, ⟨c₀⟩⟩ := h𝔭.hchart p
  obtain ⟨D⟩ := LocDataPt.nonempty hI l hl p hIp hv hf₀ c₀
  have := hf p h𝔭p
  rw [D.cRF_eq_pt] at this ⊢
  exact (Loc.transport _ D.ck).RF_antitone D.ek hst this

variable {d : ℕ} (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hd hw

/-- `pow_le_compFPt` through `pow_le_compFPt_ptL`, with the data carried by `h𝔭`. -/
theorem pow_le_compFPtP [Fact (HasPres A)] (N : ℕ) : 𝔭 ^ N ≤ compFPt I 𝔭 (N / d) := by
  obtain ⟨l, hl⟩ := h𝔭.gensI
  exact h𝔭.pow_le_compFPt_ptL hI l hl h𝔭.hchart hmax hd hw N

/-- `exists_pow_mem_compFPt` through `exists_pow_mem_compFPt_ptL`. -/
theorem exists_pow_mem_compFPtP [Fact (HasPres A)] {i : A} (hi : i ∈ 𝔭) (t : ℚ) :
    ∃ b : ℕ, i ^ b ∈ compFPt I 𝔭 t := by
  obtain ⟨l, hl⟩ := h𝔭.gensI
  exact h𝔭.exists_pow_mem_compFPt_ptL hI l hl h𝔭.hchart hmax hd hw hi t

/-- **The first step of the filtration is the component**, at points (`compFPt_one_div` with
`LocDataPt.nonempty`, `eq_p_ptL` and `cRF_eq_pt`). -/
theorem compFPt_one_divP [hpA : Fact (HasPres A)] : compFPt I 𝔭 (1 / d) = 𝔭 := by
  obtain ⟨l, hl⟩ := h𝔭.gensI
  have hchart := h𝔭.hchart
  apply le_antisymm
  · intro f hf
    have := h𝔭.isPrime
    obtain ⟨C, hC, -⟩ := h𝔭.gens
    obtain ⟨p, hp⟩ := HasPres.exists_pt hpA.out C fun h =>
      (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 (hC ▸ h))
    rw [← hC] at hp
    obtain ⟨hIp, hv⟩ := h𝔭.mem_ptL hI l hl hchart hmax p hp
    obtain ⟨f₀, hf₀, n₀, ⟨c₀⟩⟩ := hchart p
    obtain ⟨D⟩ := LocDataPt.nonempty hI l hl p hIp hv hf₀ c₀
    have hpD : 𝔭 = D.p := h𝔭.eq_p_ptL D hp
    have h1 := mem_compFPt.1 hf p hp
    rw [D.cRF_eq_pt] at h1
    have h2 := Chart.RF_le_span _ D.ek (by positivity) h1
    have hset : {i | D.ek i ≠ 0} = {i : Fin D.n | (i : ℕ) < D.k} := by
      ext i; exact D.supp i
    rw [hset, ← LocDataPt.P, ← D.map_p, ← hpD] at h2
    rw [← under_map_atPrime hp]
    exact h2
  · have := h𝔭.pow_le_compFPt_ptL hI l hl hchart hmax hd hw 1
    rwa [pow_one, Nat.cast_one] at this

end LocusComp

end P

end BezoutCounterexample.Principalization
