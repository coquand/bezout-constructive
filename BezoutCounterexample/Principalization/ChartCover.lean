import BezoutCounterexample.Principalization.PosCover
import BezoutCounterexample.Principalization.Points
import BezoutCounterexample.Constructive.ChainLiftChoice
import BezoutCounterexample.Constructive.PresContract
import BezoutCounterexample.Principalization.MaxInvPtDef

/-!
# The filtration of a component as an intersection of chart ideals (leaf)

A `ChartCover I v₀ 𝔭` is a finite family of local data `Dₖ` at points of `V(𝔭)`, with a partition
of unity `i + Σ fₖ gₖ = 1` (`i ∈ 𝔭`), and *separated*: every point of the maximal locus in
`D(gₖ)` lies on `V(𝔭)` (`sep`). Separation is needed because `V(x_head) ∩ D(gₖ)` may also meet
other components of the maximal locus.

`mem_compF_iff_chart`: `x ∈ F_t(𝔭) ↔ ∀ k, x/1 ∈ RF_t(Dₖ)`, the explicit weighted monomial ideal
of the `k`-th chart. So membership in `F_t` is decidable as soon as membership in the chart ideals
is (Gröbner, given presentations of the chart rings). The "if" direction is `mem_cRF_of_cover`
(partition of unity). The "only if" direction is local-global on `D(gₖ)`. On the maximal locus,
which is contained in `V(𝔭)` by `sep`, the chart ideal localises to the maximal centre
(`RFB_map_of_mem`); elsewhere it localises to `(1)` (`RFB_map_of_not_mem`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

section FiniteRF

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

/-- **The chart ideals are finitely generated, explicitly**: monomials can be truncated at
exponent `⌈t / eᵢ⌉` in each head coordinate (weights are nonnegative). All decisions are on `ℚ`
and `ℕ` (no `classical`). -/
theorem Chart.RF_eq_span_image (c : Chart R n) (e : Fin n → ℚ) (he : ∀ i, 0 ≤ e i) (t : ℚ) :
    ∃ s : Finset (Fin n →₀ ℕ), c.RF e t = Ideal.span
      ((fun α : Fin n →₀ ℕ => ∏ i, c.x i ^ α i) '' (s : Set (Fin n →₀ ℕ))) := by
  let b : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => if e i = 0 then 0 else ⌈t / e i⌉₊
  let cand := (Finset.Iic b).filter fun α => (∀ i, e i = 0 → α i = 0) ∧ t ≤ lam e α
  refine ⟨cand, le_antisymm ?_ ?_⟩
  · rw [Chart.RF, Ideal.span_le]
    rintro _ ⟨α, h0, ht, rfl⟩
    set α' := α ⊓ b
    have hα'α : α' ≤ α := inf_le_left
    have hmem : (∏ i, c.x i ^ α' i) ∈
        Ideal.span ((fun α : Fin n →₀ ℕ => ∏ i, c.x i ^ α i) '' (cand : Set (Fin n →₀ ℕ))) := by
      refine Ideal.subset_span ⟨α', ?_, rfl⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_Iic.2 inf_le_right, fun i hi => ?_, ?_⟩
      · exact Nat.eq_zero_of_le_zero ((hα'α i).trans (h0 i hi).le)
      · rcases Constructive.fin_forall_or_exists (A := fun i => α i ≤ b i) (B := fun i => b i < α i)
          (fun i => (Nat.lt_or_ge (b i) (α i)).symm) with hle | ⟨i, hi⟩
        · rwa [show α' = α from inf_eq_left.2 fun i => hle i]
        · rcases le_or_gt t 0 with htn | htp
          · exact htn.trans (lam_nonneg he α')
          have hei : e i ≠ 0 := fun h => by
            have : b i = 0 := by simp [b, h]
            rw [h0 i h] at hi; omega
          have hbi : b i = ⌈t / e i⌉₊ := by simp [b, hei]
          have hα'i : α' i = b i := by
            simp only [α', Finsupp.inf_apply]; exact min_eq_right hi.le
          have hepos : 0 < e i := lt_of_le_of_ne (he i) (Ne.symm hei)
          calc t ≤ (⌈t / e i⌉₊ : ℚ) * e i := by
                rw [← div_le_iff₀ hepos]; exact Nat.le_ceil _
            _ = (α' i : ℚ) * e i := by rw [hα'i, hbi]
            _ ≤ lam e α' := by
                unfold lam
                exact Finset.single_le_sum (f := fun j => (α' j : ℚ) * e j)
                  (fun j _ => mul_nonneg (Nat.cast_nonneg _) (he j)) (Finset.mem_univ i)
    have hsplit : (∏ i, c.x i ^ α i) = (∏ i, c.x i ^ α' i) * ∏ i, c.x i ^ (α - α') i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, Finsupp.tsub_apply, Nat.add_sub_cancel' (hα'α i)]
    rw [SetLike.mem_coe, hsplit]
    exact Ideal.mul_mem_right _ _ hmem
  · rw [Ideal.span_le]
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨-, h0, ht⟩ := Finset.mem_filter.1 hα
    exact Ideal.subset_span ⟨α, h0, ht, rfl⟩

/-- The same, as a `Finset` of generators (classical `Finset.image`). -/
theorem Chart.RF_eq_span_finset (c : Chart R n) (e : Fin n → ℚ) (he : ∀ i, 0 ≤ e i) (t : ℚ) :
    ∃ s : Finset R, c.RF e t = Ideal.span (s : Set R) := by
  classical
  obtain ⟨s, hs⟩ := c.RF_eq_span_image e he t
  exact ⟨s.image fun α => ∏ i, c.x i ^ α i, by rw [hs, Finset.coe_image]⟩

/-- The same, as a list of generators (a representative of the underlying multiset). -/
theorem Chart.RF_eq_lspan (c : Chart R n) (e : Fin n → ℚ) (he : ∀ i, 0 ≤ e i) (t : ℚ) :
    ∃ l : List R, c.RF e t = Constructive.lspan l := by
  obtain ⟨s, hs⟩ := c.RF_eq_span_image e he t
  obtain ⟨l, hl⟩ := Quot.exists_rep s.val
  have hsl : ∀ α, α ∈ s ↔ α ∈ l := fun α => by
    rw [← Finset.mem_val, ← hl]
    exact Multiset.mem_coe
  refine ⟨l.map fun α => ∏ i, c.x i ^ α i, ?_⟩
  rw [hs, Constructive.lspan]
  congr 1
  ext y
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact List.mem_map_of_mem (f := fun α : Fin n →₀ ℕ => ∏ i, c.x i ^ α i) ((hsl α).1 hα)
  · intro hy
    obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hy
    exact ⟨α, (hsl α).2 hα, rfl⟩

end FiniteRF

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

/-- A separated finite cover of `V(𝔭)` by local data, with a partition of unity. -/
structure ChartCover (I : Ideal A) (v₀ : ℕ → ℚ) (𝔭 : Ideal A) where
  n : ℕ
  𝔪 : Fin n → Ideal A
  max : ∀ k, (𝔪 k).IsMaximal
  le : ∀ k, 𝔭 ≤ 𝔪 k
  D : ∀ k, haveI := max k; LocData I v₀ (𝔪 k)
  f : Fin n → A
  i : A
  hi : i ∈ 𝔭
  one : i + ∑ k, f k * (D k).g = 1
  sep : ∀ k (𝔪' : Ideal A) [𝔪'.IsMaximal], (D k).g ∉ 𝔪' → I ≤ 𝔪' → InvAt I 𝔪' v₀ → 𝔭 ≤ 𝔪'

attribute [instance] ChartCover.max

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} {𝔭 : Ideal A}
  (hZ : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 → I ≤ 𝔪 ∧ InvAt I 𝔪 v₀)
include hI

omit [IsNoetherianRing A] in
/-- Local-global for one chart: membership at every point of the maximal locus of `D(g)` (in the
maximal centre) gives membership in the chart ideal over `D(g)`. -/
theorem LocData.mem_RFB_of_forall {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) (t : ℚ)
    {x : A} (hx : ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], D.g ∉ 𝔪' → I ≤ 𝔪' → InvAt I 𝔪' v₀ →
      algebraMap A (Localization.AtPrime 𝔪') x ∈ cRF I 𝔪' t) :
    algebraMap A D.B x ∈ D.RFB t := by
  classical
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ)
  set 𝔠 := (D.RFB t).colon (Ideal.span {algebraMap A D.B x})
  suffices h : 𝔠 = ⊤ by
    have h1 : (1 : D.B) ∈ 𝔠 := by rw [h]; trivial
    have := Submodule.mem_colon.1 h1 (algebraMap A D.B x) (Ideal.mem_span_singleton_self _)
    rwa [one_smul] at this
  by_contra hne
  obtain ⟨𝔫, h𝔫, h𝔠𝔫⟩ := Ideal.exists_le_maximal 𝔠 hne
  have hmax := (IsLocalization.isMaximal_iff_isMaximal_disjoint D.B D.g 𝔫).1 h𝔫
  set 𝔪' := 𝔫.under A
  have : 𝔪'.IsMaximal := hmax.1
  have hg' : D.g ∉ 𝔪' := hmax.2
  have hloc : algebraMap A (Localization.AtPrime 𝔪') x ∈ (D.RFB t).map (Loc.map (D.ctrlN 𝔪' hg')) := by
    by_cases hZ' : I ≤ 𝔪' ∧ InvAt I 𝔪' v₀
    · rw [D.RFB_map_of_mem hI hg' hZ'.1 hZ'.2]; exact hx 𝔪' hg' hZ'.1 hZ'.2
    · rw [D.RFB_map_of_not_mem hg' hZ']; trivial
  obtain ⟨y, hy, hyx⟩ := D.exists_of_mem_map hg' _ hloc
  apply hy
  show algebraMap A D.B y ∈ 𝔫
  apply h𝔠𝔫
  rw [Submodule.mem_colon]
  intro z hz
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  rw [smul_eq_mul, ← mul_assoc, mul_comm _ w, mul_assoc, ← map_mul]
  exact Ideal.mul_mem_left _ _ hyx

omit hI [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- At a point of `D(g)` where one of the first `k` chart functions is a unit, the chart ideals
are trivial (the constructive core of `LocData.RFB_map_of_not_mem`). -/
lemma LocData.RFB_map_eq_top_of_isUnit {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪)
    {𝔪' : Ideal A} [𝔪'.IsMaximal] (hg' : D.g ∉ 𝔪') (i : Fin D.n) (hi : (i : ℕ) < D.k)
    (hunit : IsUnit ((Loc.transport (D.ctrl 𝔪' hg') D.ck).x i)) (t : ℚ) :
    (D.RFB t).map (Loc.map (D.ctrlN 𝔪' hg')) = ⊤ := by
  set c₁ := Loc.transport (D.ctrl 𝔪' hg') D.ck
  have hpos : 0 < D.ek i := lt_of_le_of_ne (D.inv.nonneg i) (Ne.symm ((D.supp i).2 hi))
  obtain ⟨N, hN⟩ := exists_nat_ge (t / D.ek i)
  have hmem : c₁.x i ^ N ∈ c₁.RF D.ek t := by
    have h1 := c₁.pow_mem_RF D.ek (c₁.x_mem_RF D.ek i ((D.supp i).2 hi)) N
    refine c₁.RF_antitone D.ek ?_ h1
    rw [div_le_iff₀ hpos] at hN
    exact hN
  rw [LocData.RFB, Loc.map_RF, D.transport_cB hg']
  exact Ideal.eq_top_of_isUnit_mem _ hmem (hunit.pow N)

omit hI [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- **The maximal locus is decided at an explicit point of `D(g)`**: the point lies in the locus,
or one of the first `k` chart functions is a unit there (`Pt.dec_local`, finitely many tests). -/
lemma LocData.locus_dec_pt {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) (p : Pt A)
    (hg' : D.g ∉ p.ker) :
    (I ≤ p.ker ∧ InvAt I p.ker v₀) ∨ ∃ i : Fin D.n, (i : ℕ) < D.k ∧
      IsUnit ((Loc.transport (D.ctrl p.ker hg') D.ck).x i) := by
  rw [D.iff p.ker hg']
  exact Constructive.fin_forall_or_exists fun i => by
    rcases Nat.lt_or_ge (i : ℕ) D.k with hi | hi
    · exact (p.dec_local _).imp (fun h _ => h) fun h => ⟨hi, h⟩
    · exact Or.inl fun h => absurd h (Nat.not_lt.2 hi)

omit [IsNoetherianRing A] in
/-- **Local-global for one chart, at explicit points** (D3.2a): as `LocData.mem_RFB_of_forall`,
with no Zorn and no Jacobson. Decide `x/1 ∈ RF_t` through its contraction `N` to `A`; otherwise
the colon `(N : x)` contains no power of `g`, an explicit point of `V(N : x) ∩ D(g)` exists
(`HasPres.exists_pt_away`), the locus is decided there (`LocData.locus_dec_pt`), and either branch
puts the point's `y ∉ p` in `(N : x)`. -/
theorem LocData.mem_RFB_of_forall_pt [hpA : Fact (Constructive.HasPres A)] {𝔪 : Ideal A} [𝔪.IsMaximal]
    (D : LocData I v₀ 𝔪) (t : ℚ) {x : A}
    (hx : ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], D.g ∉ 𝔪' → I ≤ 𝔪' → InvAt I 𝔪' v₀ →
      algebraMap A (Localization.AtPrime 𝔪') x ∈ cRF I 𝔪' t) :
    algebraMap A D.B x ∈ D.RFB t := by
  have hp : Constructive.HasPres A := hpA.out
  obtain ⟨l, hl⟩ := D.cB.RF_eq_lspan D.ek D.inv.nonneg t
  obtain ⟨N, hN⟩ := Constructive.HasPres.exists_contract hp D.g D.B l
  have hRFB : ∀ y : A, algebraMap A D.B y ∈ D.RFB t ↔ y ∈ Constructive.lspan N := fun y => by
    rw [LocData.RFB, hl]; exact hN y
  rw [hRFB]
  rcases Constructive.HasPres.mem_dec hp N x with h | hxN
  · exact h
  exfalso
  obtain ⟨C, hC⟩ := Constructive.HasPres.exists_colon hp N [x]
  have hx1 : Constructive.lspan [x] = Ideal.span {x} := by
    rw [Constructive.lspan]; congr 1; ext z; simp
  have hCx : ∀ y, y * x ∈ Constructive.lspan N → y ∈ Constructive.lspan C := fun y hy =>
    (hC y).2 fun z hz => by
      rw [hx1] at hz
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      rw [mul_left_comm]
      exact Ideal.mul_mem_left _ _ hy
  have hpow : ∀ k : ℕ, D.g ^ k ∉ Constructive.lspan C := fun k hk => hxN (by
    have h1 := (hC _).1 hk x (hx1 ▸ Ideal.mem_span_singleton_self x)
    rw [← hRFB, map_mul, map_pow] at h1
    rw [← hRFB]
    exact (Ideal.unit_mul_mem_iff_mem _ ((IsLocalization.Away.algebraMap_isUnit D.g).pow k)).1 h1)
  obtain ⟨p, hCp, hgp⟩ := HasPres.exists_pt_away hp C D.g hpow
  have hloc : algebraMap A (Localization.AtPrime p.ker) x ∈
      (D.RFB t).map (Loc.map (D.ctrlN p.ker hgp)) := by
    rcases D.locus_dec_pt p hgp with ⟨hI', hv'⟩ | ⟨i, hi, hu⟩
    · rw [D.RFB_map_of_mem hI hgp hI' hv']; exact hx p.ker hgp hI' hv'
    · rw [D.RFB_map_eq_top_of_isUnit hgp i hi hu t]; trivial
  obtain ⟨y, hy, hyx⟩ := D.exists_of_mem_map hgp _ hloc
  exact hy (hCp (hCx y ((hRFB _).1 hyx)))

include hZ in
/-- **`F_t` of a component is the intersection of the chart ideals of a separated cover.** -/
theorem mem_compF_iff_chart [Fact (Constructive.HasPres A)] (C : ChartCover I v₀ 𝔭) (t : ℚ) (x : A) :
    x ∈ compF I 𝔭 t ↔ ∀ k, algebraMap A (C.D k).B x ∈ (C.D k).RFB t := by
  constructor
  · intro hx k
    refine (C.D k).mem_RFB_of_forall_pt hI t fun 𝔪' _ hg' hI' hv' => ?_
    exact mem_compF.1 hx 𝔪' (C.sep k 𝔪' hg' hI' hv')
  · intro hx
    rw [mem_compF]
    intro 𝔪' _ h𝔭𝔪'
    exact mem_cRF_of_cover hI hZ C.f (fun k => (C.D k).g) C.hi C.one t
      (fun k => ⟨C.𝔪 k, C.max k, C.D k, rfl, hx k⟩) 𝔪' h𝔭𝔪'

section Exist

omit hI [IsNoetherianRing A] [IsDomain A] [Algebra.Smooth ℚ A] in
/-- Shrinking the open `D(g)` of local data to `D(g h)`. -/
def LocData.restrict {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) (h : A) (hh : h ∉ 𝔪) :
    LocData I v₀ 𝔪 where
  n := D.n
  M := D.M
  g := D.g * h
  hg := fun hm => (Ideal.IsPrime.mem_or_mem inferInstance hm).elim D.hg hh
  ctrl := ⟨fun P _ hP => D.ctrl P fun hg => hP (Ideal.mul_mem_right _ _ hg), fun m hm =>
    (D.ctrl.dvd m hm).imp fun b hb => hb.trans (pow_dvd_pow_of_dvd (dvd_mul_right _ _) b)⟩
  k := D.k
  ck := D.ck
  ek := D.ek
  supp := D.supp
  hv := D.hv
  adm := D.adm
  inv := D.inv
  cent := D.cent
  iff := fun 𝔪' _ hg' => D.iff 𝔪' fun h1 => hg' (Ideal.mul_mem_right _ _ h1)
  rf := fun 𝔪' _ hg' => D.rf 𝔪' fun h1 => hg' (Ideal.mul_mem_right _ _ h1)

variable (hmax : IsMaxInvPt I v₀)
  (h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes)
include hmax h𝔭

/-- A function vanishing on the other components but not at a given point of `V(𝔭)`. -/
theorem exists_sep_elem (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔭𝔪 : 𝔭 ≤ 𝔪) :
    ∃ h : A, h ∉ 𝔪 ∧ ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], h ∉ 𝔪' → I ≤ 𝔪' → InvAt I 𝔪' v₀ →
      𝔭 ≤ 𝔪' := by
  classical
  have hfin : ((locusIdeal I v₀).minimalPrimes \ {𝔭}).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing A _).subset Set.sdiff_subset
  set S := hfin.toFinset
  set Q : Ideal A := ⨅ q ∈ S, q
  have hQ : 𝔭 ⊔ Q = ⊤ := Ideal.sup_iInf_eq_top fun q hq => by
    obtain ⟨hqm, hqne⟩ := (Set.Finite.mem_toFinset hfin).1 hq
    exact minimalPrimes_sup_eq_top hI (IsMaxInvPt.toMax hmax) h𝔭 hqm (Ne.symm hqne)
  have hQm : ¬ Q ≤ 𝔪 := fun hle =>
    (Ideal.IsMaximal.ne_top ‹_›) (top_le_iff.1 (hQ ▸ sup_le h𝔭𝔪 hle))
  obtain ⟨h, hhQ, hhm⟩ := Set.not_subset.1 hQm
  refine ⟨h, hhm, fun 𝔪' _ hh' hI' hv' => ?_⟩
  have hle : locusIdeal I v₀ ≤ 𝔪' := fun f hf => mem_locusIdeal.1 hf 𝔪' ⟨inferInstance, hI', hv'⟩
  obtain ⟨q, hq, hq𝔪'⟩ := Ideal.exists_minimalPrimes_le hle
  by_cases hqp : q = 𝔭
  · exact hqp ▸ hq𝔪'
  · exfalso
    apply hh'
    have hqS : q ∈ S := (Set.Finite.mem_toFinset hfin).2 ⟨hq, hqp⟩
    exact hq𝔪' ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hhQ q) hqS)

/-- **Separated chart covers exist.** -/
theorem exists_chartCover : Nonempty (ChartCover I v₀ 𝔭) := by
  classical
  let good : A → Prop := fun g => ∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal) (D : LocData I v₀ 𝔪),
    𝔭 ≤ 𝔪 ∧ D.g = g ∧ ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], D.g ∉ 𝔪' → I ≤ 𝔪' → InvAt I 𝔪' v₀ →
      𝔭 ≤ 𝔪'
  have hcov : (1 : A) ∈ 𝔭 ⊔ Ideal.span {g | good g} := by
    by_contra h1
    have hne : 𝔭 ⊔ Ideal.span {g | good g} ≠ ⊤ := fun ht => h1 (by rw [ht]; trivial)
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
    have h𝔭𝔪 : 𝔭 ≤ 𝔪 := le_sup_left.trans hle
    obtain ⟨hI𝔪, hv⟩ := mem_maxLocus_of_minimal hI (IsMaxInvPt.toMax hmax) h𝔭 𝔪 h𝔭𝔪
    obtain ⟨D⟩ := LocData.nonempty hI 𝔪 hI𝔪 hv
    obtain ⟨h, hh, hsep⟩ := exists_sep_elem hI hmax h𝔭 𝔪 h𝔭𝔪
    let D' := D.restrict h hh
    have hgood : good D'.g := ⟨𝔪, h𝔪, D', h𝔭𝔪, rfl, fun 𝔪' _ hg' hI' hv' =>
      hsep 𝔪' (fun hh' => hg' (Ideal.mul_mem_left _ _ hh')) hI' hv'⟩
    exact D'.hg (hle (le_sup_right (a := 𝔭) (Ideal.subset_span hgood)))
  obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 hcov
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hy
  choose 𝔪 hmx D hle hDg hsep using fun k => (g k).2
  refine ⟨⟨n, 𝔪, hmx, hle, D, f, i, hi, ?_, hsep⟩⟩
  rw [← hiy, ← hfg]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, hDg]

end Exist


end BezoutCounterexample.Principalization

namespace BezoutCounterexample.Principalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} {𝔭 : Ideal A}
  (hZ : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], 𝔭 ≤ 𝔪 → I ≤ 𝔪 ∧ InvAt I 𝔪 v₀)
include hI hZ

/-- **`F_t` by finitely many explicit generators per chart**: membership in `F_t(𝔭)` is
membership of `x/1` in a finitely generated ideal of each chart ring `(Dₖ).B ≅ A[1/gₖ]`. -/
theorem mem_compF_iff_finset [Fact (Constructive.HasPres A)] (C : ChartCover I v₀ 𝔭) (t : ℚ) :
    ∃ s : ∀ k, Finset (C.D k).B, ∀ x : A,
      x ∈ compF I 𝔭 t ↔ ∀ k, algebraMap A (C.D k).B x ∈ Ideal.span (s k : Set (C.D k).B) := by
  choose s hs using fun k => (C.D k).cB.RF_eq_span_finset (C.D k).ek (C.D k).inv.nonneg t
  refine ⟨s, fun x => ?_⟩
  rw [mem_compF_iff_chart hI hZ C t x]
  exact forall_congr' fun k => by rw [LocData.RFB, hs k]

/-- **The interface for the decision of `F_t`**: per chart `k` a finite list `L k` of elements of
`A[1/gₖ] = Localization.Away gₖ`, with `x ∈ F_t(𝔭) ↔ ∀ k, x/1 ∈ (L k)`. -/
theorem mem_compF_iff_list [Fact (Constructive.HasPres A)] (C : ChartCover I v₀ 𝔭) (t : ℚ) :
    ∃ L : ∀ k, List (Localization.Away (C.D k).g), ∀ x : A,
      x ∈ compF I 𝔭 t ↔ ∀ k, algebraMap A (Localization.Away (C.D k).g) x ∈
        Constructive.lspan (L k) := by
  obtain ⟨l, hl⟩ := Constructive.finite_choice_dep fun k =>
    (C.D k).cB.RF_eq_lspan (C.D k).ek (C.D k).inv.nonneg t
  let e : ∀ k, (C.D k).B ≃ₐ[A] Localization.Away (C.D k).g := fun k =>
    IsLocalization.algEquiv (Submonoid.powers (C.D k).g) (C.D k).B _
  let φ : ∀ k, (C.D k).B →+* Localization.Away (C.D k).g := fun k => (e k : (C.D k).B →+* _)
  have hφx : ∀ k (x : A), φ k (algebraMap A (C.D k).B x) =
      algebraMap A (Localization.Away (C.D k).g) x := fun k x => (e k).commutes x
  refine ⟨fun k => (l k).map (φ k), fun x => ?_⟩
  rw [mem_compF_iff_chart hI hZ C t x]
  refine forall_congr' fun k => ?_
  rw [LocData.RFB, hl k, Constructive.lspan_map, ← hφx]
  constructor
  · exact fun h => Ideal.mem_map_of_mem _ h
  · intro h
    obtain ⟨z, hz, hze⟩ := (Ideal.mem_map_iff_of_surjective (φ k) (e k).surjective).1 h
    rwa [(e k).injective hze] at hz

/-- **Separated chart covers, positively.** Inputs: an explicit separating element `q`
(`1 - q ∈ 𝔭`, and `q` vanishes on the maximal locus off `V(𝔭)`; positively `q` comes from
`1 = p + q`, `q ∈ (P : 𝔭)`, `P` the locus ideal), the explicit Nullstellensatz, generators of
`𝔭`, the decision (G) and `IndNoeth (A ⧸ 𝔭)`. Bar induction (`exists_cover`) as in
`one_mem_certC_pos`, with every chart restricted by `q`; then finite choice over the cover. -/
theorem exists_chartCover_pos (q : A) (hq : 1 - q ∈ 𝔭)
    (hqsep : ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], q ∉ 𝔪' → I ≤ 𝔪' → InvAt I 𝔪' v₀ → 𝔭 ≤ 𝔪')
    (pgens : List A) (hpg : 𝔭 = Constructive.lspan pgens) (hNS : ExplicitNS A)
    (hdec : ∀ l : List A, (1 : A) ∈ 𝔭 ⊔ Constructive.lspan l ∨ (1 : A) ∉ 𝔭 ⊔ Constructive.lspan l)
    (hN : Constructive.IndNoeth (A ⧸ 𝔭)) : Nonempty (ChartCover I v₀ 𝔭) := by
  let good : A → Prop := fun g => ∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal) (D : LocData I v₀ 𝔪),
    𝔭 ≤ 𝔪 ∧ D.g = g ∧ ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], D.g ∉ 𝔪' → I ≤ 𝔪' → InvAt I 𝔪' v₀ →
      𝔭 ≤ 𝔪'
  obtain ⟨l, hl, h1⟩ := Constructive.exists_cover 𝔭 hN good hdec fun l _ hl1 => by
    obtain ⟨L, _, _, _, z, -, hz⟩ := hNS (pgens ++ l) fun h => hl1 (lspan_append_le hpg h)
    have hmx := ker_isMaximal z
    have hle := sup_le_ker hpg z hz
    have h𝔭𝔪 : 𝔭 ≤ RingHom.ker z := le_sup_left.trans hle
    have hZ' := hZ _ h𝔭𝔪
    obtain ⟨D⟩ := LocData.nonempty hI _ hZ'.1 hZ'.2
    have hq𝔪 : q ∉ RingHom.ker z := fun h => (Ideal.IsMaximal.ne_top hmx)
      ((Ideal.eq_top_iff_one _).2 (by
        have := Ideal.add_mem _ (h𝔭𝔪 hq) h
        rwa [sub_add_cancel] at this))
    let D' := D.restrict q hq𝔪
    refine ⟨D'.g, ⟨_, hmx, D', h𝔭𝔪, rfl, fun 𝔪' _ hg' hI' hv' =>
      hqsep 𝔪' (fun h => hg' (Ideal.mul_mem_left _ _ h)) hI' hv'⟩, fun h => D'.hg (hle h)⟩
  have hcov : (1 : A) ∈ 𝔭 ⊔ Ideal.span {g | good g} := by
    refine (sup_le_sup_left ?_ 𝔭) h1
    rw [Constructive.lspan, Ideal.span_le]
    intro g hg; exact Ideal.subset_span (hl g hg)
  obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 hcov
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hy
  obtain ⟨F⟩ := Constructive.fin_nonempty_pi (X := fun k : Fin n =>
    Σ' (𝔪 : Ideal A) (hm : 𝔪.IsMaximal), {D : LocData I v₀ 𝔪 //
      𝔭 ≤ 𝔪 ∧ D.g = (g k : A) ∧ ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], D.g ∉ 𝔪' → I ≤ 𝔪' →
        InvAt I 𝔪' v₀ → 𝔭 ≤ 𝔪'}) fun k => by
    obtain ⟨𝔪, hm, D, hle, hDg, hsep⟩ := (g k).2
    exact ⟨⟨𝔪, hm, D, hle, hDg, hsep⟩⟩
  refine ⟨⟨n, fun k => (F k).1, fun k => (F k).2.1, fun k => (F k).2.2.2.1, fun k => (F k).2.2.1,
    f, i, hi, ?_, fun k => (F k).2.2.2.2.2⟩⟩
  rw [← hiy, ← hfg]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, (F k).2.2.2.2.1]

omit hI hZ [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- The separation property of `exists_chartCover_pos` from a colon certificate:
`q 𝔭 ⊆ P` with `P` contained in every point of the maximal locus (e.g. `P = locusIdeal I v₀`). -/
theorem sep_of_mem_colon {P : Ideal A} (hP : ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], I ≤ 𝔪' →
      InvAt I 𝔪' v₀ → P ≤ 𝔪')
    {q : A} (hq : ∀ p ∈ 𝔭, q * p ∈ P) (𝔪' : Ideal A) [𝔪'.IsMaximal] (hq' : q ∉ 𝔪')
    (hI' : I ≤ 𝔪') (hv' : InvAt I 𝔪' v₀) : 𝔭 ≤ 𝔪' := fun p hp =>
  ((Ideal.IsPrime.mem_or_mem inferInstance (hP 𝔪' hI' hv' (hq p hp))).resolve_left hq')

end BezoutCounterexample.Principalization
