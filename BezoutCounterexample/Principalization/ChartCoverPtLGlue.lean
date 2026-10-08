import BezoutCounterexample.Principalization.ChartCoverPtL

/-!
# The filtration on a `ChartCoverPtL` (D3.4 (e), leaf)

The chart-ideal lemmas of `LocData` (MaxLocus, ChartCover, MaxLocusPt, ComponentFilPt) at explicit
points, for `LocDataPt` (same proofs; `D.iff p`/`D.rf p` for `D.iff p.ker`/`D.rf p.ker`), and the
gluing over a `ChartCoverPtL`:

* `LocDataPt.RFB_map_of_mem`, `RFB_map_eq_top_of_isUnit`, `locus_dec_pt`, `map_algebraMap_B`,
  `exists_of_mem_map`, `RFB_map_eq_pt`, `exists_pow_mul_mem_pt`, `mem_RFB_of_forall_pts`;
* `mem_cRF_of_cover_ptL` (gluing at a point; the local data at the point from
  `LocDataPt.nonempty`, hence the inputs `l`, `hl`, `hchart`);
* `ChartCoverPtL.mem_compFPt_iff`, `ChartCoverPtL.mem_RFB_of_mem` (`hloc`: the `→` direction,
  chart by chart), `ChartCoverPtL.global_of_RFB_pt` (`hglob`: a chart membership spreads to `F_t`
  up to a power of the chart element).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

namespace LocDataPt

variable {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocDataPt I v₀ 𝔪)

lemma transport_cB (p : Pt A) (hg' : D.g ∉ p.ker) :
    Loc.transport (D.ctrlN p.ker hg') D.cB = Loc.transport (D.ctrl p.ker hg') D.ck := by
  rw [cB, Loc.transport_trans]

lemma map_algebraMap_B (p : Pt A) (hg' : D.g ∉ p.ker) (x : A) :
    Loc.map (D.ctrlN p.ker hg') (algebraMap A D.B x) =
      algebraMap A (Localization.AtPrime p.ker) x :=
  Loc.map_algebraMap _ x

/-- Pulling membership back from a point of `D(g)` to `D(g)`. -/
lemma exists_of_mem_map (p : Pt A) (hg' : D.g ∉ p.ker) (J : Ideal D.B) {x : A}
    (hx : algebraMap A (Localization.AtPrime p.ker) x ∈ J.map (Loc.map (D.ctrlN p.ker hg'))) :
    ∃ y : A, y ∉ p.ker ∧ algebraMap A D.B (y * x) ∈ J := by
  have hN' := D.ctrlN p.ker hg'
  let := Loc.alg hN'
  have := Loc.tower hN'
  have := Loc.isLoc hN'
  have halg : ∀ y : D.B, Loc.map hN' y = algebraMap D.B (Localization.AtPrime p.ker) y :=
    fun _ => rfl
  have hJ : J.map (Loc.map hN') = J.map (algebraMap D.B (Localization.AtPrime p.ker)) := rfl
  rw [← D.map_algebraMap_B p hg', halg, hJ,
    IsLocalization.mem_map_algebraMap_iff (p.ker.primeCompl.map (algebraMap A D.B))] at hx
  obtain ⟨⟨j, ⟨_, s, hs, rfl⟩⟩, hj⟩ := hx
  simp only at hj
  have hinj : Function.Injective (Loc.map hN') :=
    Loc.map_injective hN' (Ideal.primeCompl_le_nonZeroDivisors p.ker)
  rw [← halg, ← halg, ← map_mul] at hj
  refine ⟨s, hs, ?_⟩
  rw [map_mul, mul_comm, hinj hj]
  exact j.2

/-- At a point of `D(g)` where one of the first `k` chart functions is a unit, the chart ideals
are trivial. -/
lemma RFB_map_eq_top_of_isUnit (p : Pt A) (hg' : D.g ∉ p.ker) (i : Fin D.n) (hi : (i : ℕ) < D.k)
    (hunit : IsUnit ((Loc.transport (D.ctrl p.ker hg') D.ck).x i)) (t : ℚ) :
    (D.RFB t).map (Loc.map (D.ctrlN p.ker hg')) = ⊤ := by
  set c₁ := Loc.transport (D.ctrl p.ker hg') D.ck
  have hpos : 0 < D.ek i := lt_of_le_of_ne (D.inv.nonneg i) (Ne.symm ((D.supp i).2 hi))
  obtain ⟨N, hN⟩ := exists_nat_ge (t / D.ek i)
  have hmem : c₁.x i ^ N ∈ c₁.RF D.ek t := by
    have h1 := c₁.pow_mem_RF D.ek (c₁.x_mem_RF D.ek i ((D.supp i).2 hi)) N
    refine c₁.RF_antitone D.ek ?_ h1
    rw [div_le_iff₀ hpos] at hN
    exact hN
  rw [RFB, Loc.map_RF, D.transport_cB p hg']
  exact Ideal.eq_top_of_isUnit_mem _ hmem (hunit.pow N)

/-- **The maximal locus is decided at an explicit point of `D(g)`.** -/
lemma locus_dec_pt (p : Pt A) (hg' : D.g ∉ p.ker) :
    (I ≤ p.ker ∧ InvAt I p.ker v₀) ∨ ∃ i : Fin D.n, (i : ℕ) < D.k ∧
      IsUnit ((Loc.transport (D.ctrl p.ker hg') D.ck).x i) := by
  rw [D.iff p hg']
  exact Constructive.fin_forall_or_exists fun i => by
    rcases Nat.lt_or_ge (i : ℕ) D.k with hi | hi
    · exact (p.dec_local _).imp (fun h _ => h) fun h => ⟨hi, h⟩
    · exact Or.inl fun h => absurd h (Nat.not_lt.2 hi)

variable (hI : I ≠ ⊥)
include hI

/-- At points of the maximal locus in `D(g)`, the chart ideals are the maximal centre. -/
lemma RFB_map_of_mem (p : Pt A) (hg' : D.g ∉ p.ker) (hI' : I ≤ p.ker)
    (hv' : InvAt I p.ker v₀) (t : ℚ) :
    (D.RFB t).map (Loc.map (D.ctrlN p.ker hg')) = cRF I p.ker t := by
  obtain ⟨n', e', he', hev⟩ := hv'
  obtain rfl := he'.card_eq (Loc.transport (D.ctrl p.ker hg') D.ck)
  have hee : e' = D.ek := ext0_injective (hev.trans D.hv.symm)
  subst hee
  -- D3.6: without `cRF_eq` (the argument of `cRF_eq_of_rf`, ComponentFilPtL)
  have hgen : ∀ {R : Ideal (Localization.AtPrime p.ker)}, (∀ J' : MC (Localization.AtPrime p.ker) D.n,
      J'.Adm (Iloc I p.ker) → J'.e = D.ek → J'.RF t = R) → cRF I p.ker t = R := by
    intro R hrf
    obtain ⟨⟨J, hJ, hJe⟩, hmin⟩ := he'
    have hJi : IsInv (Iloc I p.ker) D.n J.e := ⟨⟨J, hJ, rfl⟩, by rw [hJe]; exact hmin⟩
    refine le_antisymm ?_ ?_
    · rw [← hrf J hJ hJe]
      exact iInf_le_of_le D.n (iInf_le_of_le J (iInf_le_of_le hJ (iInf_le _ hJi)))
    · refine le_iInf fun n' => le_iInf fun J' => le_iInf fun hJ' => le_iInf fun hJi' => ?_
      obtain rfl := hJi.card_eq J'.c
      rw [hrf J' hJ' ((hJi'.unique hJi).trans hJe)]
  rw [hgen fun J' hJ' hJe => D.rf p hg' J' hJ' hJe t, RFB, Loc.map_RF, D.transport_cB p hg']

/-- **Two charts give the same ideals at a common explicit point.** -/
lemma RFB_map_eq_pt {𝔪₁ : Ideal A} [𝔪₁.IsMaximal] (D₁ : LocDataPt I v₀ 𝔪₁)
    (p : Pt A) (hg : D.g ∉ p.ker) (hg₁ : D₁.g ∉ p.ker) (t : ℚ) :
    (D.RFB t).map (Loc.map (D.ctrlN p.ker hg)) =
      (D₁.RFB t).map (Loc.map (D₁.ctrlN p.ker hg₁)) := by
  rcases D.locus_dec_pt p hg with ⟨hI', hv'⟩ | ⟨i, hi, hu⟩
  · rw [D.RFB_map_of_mem hI p hg hI' hv', D₁.RFB_map_of_mem hI p hg₁ hI' hv']
  · have hZ : ¬ (I ≤ p.ker ∧ InvAt I p.ker v₀) := fun hZ =>
      (IsLocalRing.notMem_maximalIdeal.2 hu) ((D.iff p hg).1 hZ i hi)
    rw [D.RFB_map_eq_top_of_isUnit p hg i hi hu t]
    rcases D₁.locus_dec_pt p hg₁ with hZ₁ | ⟨i₁, hi₁, hu₁⟩
    · exact absurd hZ₁ hZ
    · rw [D₁.RFB_map_eq_top_of_isUnit p hg₁ i₁ hi₁ hu₁ t]

/-- **Spreading a membership** from one chart to another, up to a power of `g`, at explicit
points. -/
lemma exists_pow_mul_mem_pt [hpA : Fact (HasPres A)] {𝔪₁ : Ideal A} [𝔪₁.IsMaximal]
    (D₁ : LocDataPt I v₀ 𝔪₁) (b : A) (t : ℚ) (hb : algebraMap A D.B b ∈ D.RFB t) :
    ∃ N : ℕ, algebraMap A D₁.B (D.g ^ N * b) ∈ D₁.RFB t := by
  have hp : HasPres A := hpA.out
  obtain ⟨l, hl⟩ := D₁.cB.RF_eq_lspan D₁.ek D₁.inv.nonneg t
  obtain ⟨N₁, hN₁⟩ := HasPres.exists_contract hp D₁.g D₁.B l
  have hRFB : ∀ y : A, algebraMap A D₁.B y ∈ D₁.RFB t ↔ y ∈ lspan N₁ := fun y => by
    rw [LocDataPt.RFB, hl]; exact hN₁ y
  obtain ⟨C, hC⟩ := HasPres.exists_colon hp N₁ [b]
  have hb1 : lspan [b] = Ideal.span {b} := by rw [lspan]; congr 1; ext z; simp
  have hCb : ∀ y, y ∈ lspan C ↔ y * b ∈ lspan N₁ := fun y => by
    rw [hC y]
    constructor
    · exact fun h => h b (hb1 ▸ Ideal.mem_span_singleton_self b)
    · intro hy z hz
      rw [hb1] at hz
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      rw [mul_left_comm]
      exact Ideal.mul_mem_left _ _ hy
  obtain ⟨R, hR⟩ := hp.exists_radical C
  rcases hp.mem_dec R (D.g * D₁.g) with h | h
  · rw [hR] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have h1 := (hRFB _).2 ((hCb _).1 hk)
    have he : (D.g * D₁.g) ^ k * b = D₁.g ^ k * (D.g ^ k * b) := by ring
    rw [he, map_mul, map_pow] at h1
    exact (Ideal.unit_mul_mem_iff_mem _
      ((IsLocalization.Away.algebraMap_isUnit D₁.g).pow k)).1 h1
  · exfalso
    have hk : ∀ k : ℕ, (D.g * D₁.g) ^ k ∉ lspan C := fun k hk => h (hR ▸ ⟨k, hk⟩)
    obtain ⟨p, hCp, hgg⟩ := HasPres.exists_pt_away hp C (D.g * D₁.g) hk
    have hg : D.g ∉ p.ker := fun h => hgg (Ideal.mul_mem_right _ _ h)
    have hg₁ : D₁.g ∉ p.ker := fun h => hgg (Ideal.mul_mem_left _ _ h)
    have h1 : algebraMap A (Localization.AtPrime p.ker) b ∈
        (D₁.RFB t).map (Loc.map (D₁.ctrlN p.ker hg₁)) := by
      rw [← D.RFB_map_eq_pt hI D₁ p hg hg₁, ← D.map_algebraMap_B p hg]
      exact Ideal.mem_map_of_mem _ hb
    obtain ⟨y, hy, hyb⟩ := D₁.exists_of_mem_map p hg₁ _ h1
    exact hy (hCp ((hCb y).2 ((hRFB _).1 hyb)))

/-- **Local–global for one chart, hypotheses at points.** -/
theorem mem_RFB_of_forall_pts [hpA : Fact (HasPres A)] (t : ℚ) {x : A}
    (hx : ∀ p : Pt A, D.g ∉ p.ker → I ≤ p.ker → InvAt I p.ker v₀ →
      algebraMap A (Localization.AtPrime p.ker) x ∈ cRF I p.ker t) :
    algebraMap A D.B x ∈ D.RFB t := by
  have hp : HasPres A := hpA.out
  obtain ⟨l, hl⟩ := D.cB.RF_eq_lspan D.ek D.inv.nonneg t
  obtain ⟨N, hN⟩ := HasPres.exists_contract hp D.g D.B l
  have hRFB : ∀ y : A, algebraMap A D.B y ∈ D.RFB t ↔ y ∈ lspan N := fun y => by
    rw [LocDataPt.RFB, hl]; exact hN y
  rw [hRFB]
  rcases hp.mem_dec N x with h | hxN
  · exact h
  exfalso
  obtain ⟨C, hC⟩ := HasPres.exists_colon hp N [x]
  have hx1 : lspan [x] = Ideal.span {x} := by rw [lspan]; congr 1; ext z; simp
  have hCx : ∀ y, y * x ∈ lspan N → y ∈ lspan C := fun y hy =>
    (hC y).2 fun z hz => by
      rw [hx1] at hz
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      rw [mul_left_comm]
      exact Ideal.mul_mem_left _ _ hy
  have hpow : ∀ k : ℕ, D.g ^ k ∉ lspan C := fun k hk => hxN (by
    have h1 := (hC _).1 hk x (hx1 ▸ Ideal.mem_span_singleton_self x)
    rw [← hRFB, map_mul, map_pow] at h1
    rw [← hRFB]
    exact (Ideal.unit_mul_mem_iff_mem _ ((IsLocalization.Away.algebraMap_isUnit D.g).pow k)).1 h1)
  obtain ⟨p, hCp, hgp⟩ := HasPres.exists_pt_away hp C D.g hpow
  have hloc : algebraMap A (Localization.AtPrime p.ker) x ∈
      (D.RFB t).map (Loc.map (D.ctrlN p.ker hgp)) := by
    rcases D.locus_dec_pt p hgp with ⟨hI', hv'⟩ | ⟨i, hi, hu⟩
    · rw [D.RFB_map_of_mem hI p hgp hI' hv']; exact hx p hgp hI' hv'
    · rw [D.RFB_map_eq_top_of_isUnit p hgp i hi hu t]; trivial
  obtain ⟨y, hy, hyx⟩ := D.exists_of_mem_map p hgp _ hloc
  exact hy (hCp (hCx y ((hRFB _).1 hyx)))

end LocDataPt

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} (l : List A) (hl : I = lspan l)
  (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))

include hI l hl hchart in
/-- **Gluing at a point** (`mem_cRF_of_cover_pt` over `LocDataPt`). -/
theorem mem_cRF_of_cover_ptL [Fact (HasPres A)] {𝔭 : Ideal A}
    (hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀)
    {n : ℕ} (f : Fin n → A) (g : Fin n → A) {i : A} (hi : i ∈ 𝔭)
    (hone : i + ∑ k, f k * g k = 1) (t : ℚ) {x : A}
    (hx : ∀ k, ∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal) (D : LocDataPt I v₀ 𝔪), D.g = g k ∧
      algebraMap A D.B x ∈ D.RFB t)
    (p : Pt A) (h𝔭p : 𝔭 ≤ p.ker) :
    algebraMap A (Localization.AtPrime p.ker) x ∈ cRF I p.ker t := by
  set φ := algebraMap A (Localization.AtPrime p.ker)
  have hZ' := hZ p h𝔭p
  obtain ⟨f₀, hf₀, n₀, ⟨c₀⟩⟩ := hchart p
  obtain ⟨D'⟩ := LocDataPt.nonempty hI l hl p hZ'.1 hZ'.2 hf₀ c₀
  let 𝔠 : Ideal A :=
    { carrier := {y | φ (y * x) ∈ cRF I p.ker t}
      add_mem' := fun {y z} hy hz => by
        simp only [Set.mem_ofPred_eq, add_mul, map_add] at hy hz ⊢; exact add_mem hy hz
      zero_mem' := by simp only [Set.mem_ofPred_eq, zero_mul, map_zero]; exact zero_mem _
      smul_mem' := fun c y hy => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, mul_assoc, map_mul] at hy ⊢
        exact Ideal.mul_mem_left _ _ hy }
  have hc : ∀ y, φ (y * x) ∈ cRF I p.ker t → y ∈ 𝔠 := fun _ hy => hy
  have hg : ∀ k, g k ∈ 𝔠.radical := by
    intro k
    obtain ⟨𝔪, _, D, hDg, hxD⟩ := hx k
    obtain ⟨N, hN⟩ := D.exists_pow_mul_mem_pt hI D' x t hxD
    have h4 := Ideal.mem_map_of_mem (Loc.map (D'.ctrlN p.ker D'.hg)) hN
    rw [D'.RFB_map_of_mem hI p D'.hg hZ'.1 hZ'.2, D'.map_algebraMap_B p D'.hg] at h4
    rw [hDg] at h4
    exact ⟨N, hc _ h4⟩
  have hr : ∑ k, f k * g k ∈ 𝔠.radical :=
    Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hg k)
  obtain ⟨K, hK⟩ := hr
  have hsum : ∑ k, f k * g k = 1 - i := by rw [← hone]; ring
  rw [hsum] at hK
  have hout : (1 - i) ^ K ∉ p.ker := fun h =>
    (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 (by
      have h1 := Ideal.IsPrime.mem_of_pow_mem inferInstance K h
      have h2 := Ideal.add_mem _ h1 (h𝔭p hi)
      rwa [sub_add_cancel] at h2))
  have hunit : IsUnit (φ ((1 - i) ^ K)) :=
    IsLocalization.map_units _ (⟨(1 - i) ^ K, hout⟩ : p.ker.primeCompl)
  have h5 : φ ((1 - i) ^ K * x) ∈ cRF I p.ker t := hK
  rw [map_mul] at h5
  exact (Ideal.unit_mul_mem_iff_mem _ hunit).1 h5

namespace ChartCoverPtL

variable {𝔭 : Ideal A} (C : ChartCoverPtL I v₀ 𝔭)

include hI in
/-- **`hloc`**: an element of `F_t` lies in the chart ideal of each chart of the cover. -/
theorem mem_RFB_of_mem [Fact (HasPres A)] (k : Fin C.n) {t : ℚ} {z : A}
    (hz : z ∈ compFPt I 𝔭 t) : algebraMap A (C.D k).B z ∈ (C.D k).RFB t :=
  (C.D k).mem_RFB_of_forall_pts hI t fun p hg hI' hv' => mem_compFPt.1 hz p (C.sep k p hg hI' hv')

variable (hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀)
include hI l hl hchart hZ

/-- **`F_t` of a component is the intersection of the chart ideals of the cover.** -/
theorem mem_compFPt_iff [Fact (HasPres A)] (t : ℚ) (x : A) :
    x ∈ compFPt I 𝔭 t ↔ ∀ k, algebraMap A (C.D k).B x ∈ (C.D k).RFB t := by
  constructor
  · exact fun hx k => C.mem_RFB_of_mem hI k hx
  · intro hx
    exact mem_compFPt.2 fun p h => mem_cRF_of_cover_ptL hI l hl hchart hZ C.f (fun k => (C.D k).g)
      C.hi C.one t (fun k => ⟨(C.pt k).ker, inferInstance, C.D k, rfl, hx k⟩) p h

/-- **`hglob`**: a chart membership spreads to `F_t`, up to a power of the chart element. -/
theorem global_of_RFB_pt [Fact (HasPres A)] (k : Fin C.n) {b : A} {t : ℚ}
    (hb : algebraMap A (C.D k).B b ∈ (C.D k).RFB t) :
    ∃ N : ℕ, (C.D k).g ^ N * b ∈ compFPt I 𝔭 t := by
  obtain ⟨N, hN⟩ := exists_uniform_list
    (P := fun j m => algebraMap A (C.D j).B ((C.D k).g ^ m * b) ∈ (C.D j).RFB t)
    (fun j m n hmn hm => by
      rw [← Nat.sub_add_cancel hmn, pow_add, mul_assoc, map_mul]
      exact Ideal.mul_mem_left _ _ hm)
    (List.finRange C.n) fun j _ => (C.D k).exists_pow_mul_mem_pt hI (C.D j) b t hb
  exact ⟨N, (C.mem_compFPt_iff hI l hl hchart hZ t _).2 fun j => hN j (List.mem_finRange j)⟩

end ChartCoverPtL

end BezoutCounterexample.Principalization
