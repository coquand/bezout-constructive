import BezoutCounterexample.Principalization.MaxLocusPt

/-!
# The component filtration at explicit points (D3.3a, `docs/d3-design.md` §8.4)

`compF I 𝔭 t` is an intersection over all maximal ideals above `𝔭`; its introduction needs the
points of `V(𝔭)` to lie in the maximal locus at *arbitrary* maximal ideals, which is not
constructive. On the path it is replaced by the intersection over explicit points.

* `Ideal.mem_of_cover`, `Ideal.le_of_cover`: comaximal local–global (cffr Lemma 2.3), with a uniform exponent over a list.
* `compFPt I 𝔭 t`, `mem_compFPt`; `compF_le_compFPt` (constructive), `compFPt_eq_compF` (classical
  comparison, off path).
* `LocusComp.pow_le_compFPt`, `LocusComp.exists_pow_mem_compFPt` (I3).
* `LocData.mem_RFB_of_forall_pts`, `mem_cRF_of_cover_pt`: local–global for one chart and gluing at a
  point, with hypotheses over points only.
* `ChartCoverPt`: a cover of `V(𝔭)` by local data at explicit points, separated over points (I1);
  `ChartCoverPt.mem_compFPt_iff`, `ChartCoverPt.map_compFPt` (I2: the filtration is the chart ideal
  on each open of the cover); `LocusComp.exists_chartCoverPt`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing IsLocalization

/-- A common exponent for a list (monotone predicate). -/
lemma exists_uniform_list {α : Type*} {P : α → ℕ → Prop} (hmono : ∀ a m n, m ≤ n → P a m → P a n) :
    ∀ l : List α, (∀ a ∈ l, ∃ n, P a n) → ∃ n, ∀ a ∈ l, P a n
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, h => by
    obtain ⟨n₀, hn₀⟩ := h a List.mem_cons_self
    obtain ⟨n₁, hn₁⟩ := exists_uniform_list hmono l fun b hb => h b (List.mem_cons_of_mem a hb)
    refine ⟨max n₀ n₁, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hmono _ _ _ (le_max_left _ _) hn₀
    · exact hmono _ _ _ (le_max_right _ _) (hn₁ b hb)

/-- **Comaximal local–global for one element**: if a power of each element of a list generating
the unit ideal multiplies `x` into `J'`, then `x ∈ J'`. -/
theorem Ideal.mem_of_cover {R : Type*} [CommRing R] {J' : Ideal R} {x : R} (gs : List R)
    (h1 : (1 : R) ∈ lspan gs) (h : ∀ g ∈ gs, ∃ n : ℕ, g ^ n * x ∈ J') : x ∈ J' := by
  obtain ⟨n, hn⟩ := exists_uniform_list (P := fun g n => g ^ n * x ∈ J')
    (fun g m n hmn hm => by
      rw [← Nat.sub_add_cancel hmn, pow_add, mul_assoc]; exact Ideal.mul_mem_left _ _ hm)
    gs h
  have htop : Ideal.span ((fun y : R => y ^ n) '' {y | y ∈ gs}) = ⊤ :=
    Ideal.span_pow_eq_top _ ((Ideal.eq_top_iff_one _).2 h1) n
  have h1' : (1 : R) ∈ lspan (gs.map (· ^ n)) := by
    rw [lspan]
    convert (Ideal.eq_top_iff_one _).1 htop using 2
    ext y; simp
  have := lspan_le_comap_mul x _ J' (fun y hy => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
    rw [mul_comm]; exact hn g hg) 1 h1'
  rwa [mul_one] at this

/-- **Comaximal local–global** (cffr Lemma 2.3): if `J ⊆ J'` after inverting each element of a
list generating the unit ideal, then `J ⊆ J'`. -/
theorem Ideal.le_of_cover {R : Type*} [CommRing R] {J J' : Ideal R} (gs : List R)
    (h1 : (1 : R) ∈ lspan gs)
    (h : ∀ g ∈ gs, J.map (algebraMap R (Localization.Away g)) ≤
      J'.map (algebraMap R (Localization.Away g))) : J ≤ J' := fun _ hx =>
  Ideal.mem_of_cover gs h1 fun g hg => exists_pow_mul_mem_of_away g _ (h g hg (Ideal.mem_map_of_mem _ hx))

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- **Local–global at explicit points** (replaces `Ideal.le_of_forall_map` when the target has
generators): membership in `J'` is decided (G); for a non-member `x` the colon `(J' : x)` is proper,
so it lies in an explicit point (NS), where `x/1 ∈ J'_p` gives a denominator in the colon. -/
theorem Ideal.le_of_forall_pt [hpA : Fact (HasPres A)] {J J' : Ideal A}
    (hJ' : ∃ l : List A, J' = lspan l)
    (h : ∀ p : Pt A, J.map (algebraMap A (Localization.AtPrime p.ker)) ≤
      J'.map (algebraMap A (Localization.AtPrime p.ker))) : J ≤ J' := by
  have hp : HasPres A := hpA.out
  obtain ⟨l, rfl⟩ := hJ'
  intro x hx
  rcases hp.mem_dec l x with hxl | hxl
  · exact hxl
  exfalso
  obtain ⟨C, hC⟩ := HasPres.exists_colon hp l [x]
  have hx1 : ∀ y, y ∈ lspan C ↔ y * x ∈ lspan l := fun y => by
    rw [hC]
    refine ⟨fun hy => hy x (Ideal.subset_span List.mem_cons_self), fun hy z hz => ?_⟩
    rw [lspan_singleton] at hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [mul_left_comm]
    exact Ideal.mul_mem_left _ _ hy
  have h1 : (1 : A) ∉ lspan C := fun h1 => hxl (by simpa using (hx1 1).1 h1)
  obtain ⟨p, hpC⟩ := HasPres.exists_pt hp C h1
  have hloc := h p (Ideal.mem_map_of_mem _ hx)
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff p.ker.primeCompl] at hloc
  obtain ⟨s, hs, hsx⟩ := hloc
  exact hs (hpC ((hx1 s).2 hsx))

/-- **The weighted ideals of the centre along `V(𝔭)`, at explicit points.** -/
def compFPt (I 𝔭 : Ideal A) (t : ℚ) : Ideal A :=
  ⨅ (p : Pt A) (_ : 𝔭 ≤ p.ker), (cRF I p.ker t).comap (algebraMap A (Localization.AtPrime p.ker))

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma mem_compFPt {I 𝔭 : Ideal A} {t : ℚ} {f : A} :
    f ∈ compFPt I 𝔭 t ↔ ∀ p : Pt A, 𝔭 ≤ p.ker →
      algebraMap A (Localization.AtPrime p.ker) f ∈ cRF I p.ker t := by
  simp only [compFPt, Submodule.mem_iInf, Ideal.mem_comap]

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- The classical filtration lies in the one at points (elimination at `p.ker`). -/
lemma compF_le_compFPt (I 𝔭 : Ideal A) (t : ℚ) : compF I 𝔭 t ≤ compFPt I 𝔭 t :=
  fun _ hf => mem_compFPt.2 fun p h => mem_compF.1 hf p.ker h

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma mem_cRF_of_eq {I 𝔪 𝔫 : Ideal A} [𝔪.IsPrime] [𝔫.IsPrime] (h : 𝔫 = 𝔪) {t : ℚ} {f : A}
    (hf : algebraMap A (Localization.AtPrime 𝔫) f ∈ cRF I 𝔫 t) :
    algebraMap A (Localization.AtPrime 𝔪) f ∈ cRF I 𝔪 t := by
  subst h; exact hf

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- **The two filtrations agree** (classical comparison; off the path). -/
theorem compFPt_eq_compF [Algebra.FiniteType ℚ A] (I 𝔭 : Ideal A) (t : ℚ) :
    compFPt I 𝔭 t = compF I 𝔭 t := by
  refine le_antisymm (fun f hf => mem_compF.2 fun 𝔪 _ h𝔭𝔪 => ?_) (compF_le_compFPt I 𝔭 t)
  have hk := Pt.ker_ofIsMaximal 𝔪
  have h1 : 𝔭 ≤ (Pt.ofIsMaximal 𝔪).ker := by rw [hk]; exact h𝔭𝔪
  exact mem_cRF_of_eq hk (mem_compFPt.1 hf (Pt.ofIsMaximal 𝔪) h1)

/-- The filtration at points is antitone (as `compF_antitone`, at points). -/
lemma compFPt_antitone {I 𝔭 : Ideal A} {s t : ℚ} (hst : s ≤ t) (hI : I ≠ ⊥)
    (hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ ∃ v, InvAt I p.ker v) :
    compFPt I 𝔭 t ≤ compFPt I 𝔭 s := by
  intro f hf
  rw [mem_compFPt] at hf ⊢
  intro p h𝔭p
  obtain ⟨hI𝔪, v, n, e, ⟨⟨J, hJ, rfl⟩, hmin⟩, -⟩ := hZ p h𝔭p
  have hJi : IsInv (Iloc I p.ker) n J.e := ⟨⟨J, hJ, rfl⟩, hmin⟩
  have := hf p h𝔭p
  rw [cRF_eq hI hI𝔪 hJ hJi] at this ⊢
  exact J.c.RF_antitone J.e hst this

variable [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)

namespace LocusComp

variable {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

/-- **Powers of a component lie in its filtration** (point form of `pow_le_compF`). -/
theorem pow_le_compFPt [Fact (HasPres A)] (N : ℕ) : 𝔭 ^ N ≤ compFPt I 𝔭 (N / d) := by
  intro f hf
  rw [mem_compFPt]
  intro p h𝔭p
  obtain ⟨hIp, hv⟩ := h𝔭.mem hI hmax p h𝔭p
  obtain ⟨D⟩ := LocData.nonempty hI p.ker hIp hv
  have hp : 𝔭 = D.p := h𝔭.eq_p D h𝔭p
  have h1 : algebraMap A (Localization.AtPrime p.ker) f ∈ (𝔭 ^ N).map (algebraMap A _) :=
    Ideal.mem_map_of_mem _ hf
  rw [Ideal.map_pow, hp, D.map_p] at h1
  exact D.P_pow_le hI hd hw N h1

/-- **The first step of the filtration is the component** (point form of `compF_one_div`; the
point above `𝔭` comes from its generators, `HasPres.exists_pt`, instead of Zorn). -/
theorem compFPt_one_div [hpA : Fact (HasPres A)] : compFPt I 𝔭 (1 / d) = 𝔭 := by
  apply le_antisymm
  · intro f hf
    have := h𝔭.isPrime
    obtain ⟨C, hC, -⟩ := h𝔭.gens
    obtain ⟨p, hp⟩ := HasPres.exists_pt hpA.out C fun h =>
      (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 (hC ▸ h))
    rw [← hC] at hp
    obtain ⟨hIp, hv⟩ := h𝔭.mem hI hmax p hp
    obtain ⟨D⟩ := LocData.nonempty hI p.ker hIp hv
    have hpD : 𝔭 = D.p := h𝔭.eq_p D hp
    have h1 := mem_compFPt.1 hf p hp
    rw [D.cRF_eq_transport hI] at h1
    have h2 := Chart.RF_le_span _ D.ek (by positivity) h1
    have hset : {i | D.ek i ≠ 0} = {i : Fin D.n | (i : ℕ) < D.k} := by
      ext i; exact D.supp i
    rw [hset, ← LocData.P, ← D.map_p, ← hpD] at h2
    rw [← under_map_atPrime hp]
    exact h2
  · have := h𝔭.pow_le_compFPt hI hmax hd hw 1
    rwa [pow_one, Nat.cast_one] at this

omit hd hw [IsNoetherianRing A] in
/-- `compFPt_antitone` for a component. -/
theorem compFPt_antitone' {s t : ℚ} (hst : s ≤ t) : compFPt I 𝔭 t ≤ compFPt I 𝔭 s :=
  compFPt_antitone hst hI fun p h => ⟨(h𝔭.mem hI hmax p h).1, v₀, (h𝔭.mem hI hmax p h).2⟩

/-- **I3**: an element of the component has a power in each step of the filtration. -/
theorem exists_pow_mem_compFPt [Fact (HasPres A)] {i : A} (hi : i ∈ 𝔭) (t : ℚ) :
    ∃ b : ℕ, i ^ b ∈ compFPt I 𝔭 t := by
  obtain ⟨b, hb⟩ := exists_nat_ge (t * d)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  refine ⟨b, ?_⟩
  have h := h𝔭.pow_le_compFPt hI hmax hd hw b (Ideal.pow_mem_pow hi b)
  refine mem_compFPt.2 fun p h𝔭p => ?_
  have h' := mem_compFPt.1 h p h𝔭p
  obtain ⟨hIp, hv⟩ := h𝔭.mem hI hmax p h𝔭p
  obtain ⟨n, e, ⟨⟨J, hJ, rfl⟩, hmin⟩, -⟩ := hv
  have hJi : IsInv (Iloc I p.ker) n J.e := ⟨⟨J, hJ, rfl⟩, hmin⟩
  rw [cRF_eq hI hIp hJ hJi] at h' ⊢
  exact J.c.RF_antitone J.e (by rw [le_div_iff₀ hdq]; exact_mod_cast hb) h'

end LocusComp

namespace LocData

omit [IsNoetherianRing A] in
include hI in
/-- **Local–global for one chart, hypotheses at points** (as `mem_RFB_of_forall_pt`, whose
hypothesis is only used at kernels of points). -/
theorem mem_RFB_of_forall_pts [hpA : Fact (HasPres A)] {𝔪 : Ideal A} [𝔪.IsMaximal]
    (D : LocData I v₀ 𝔪) (t : ℚ) {x : A}
    (hx : ∀ p : Pt A, D.g ∉ p.ker → I ≤ p.ker → InvAt I p.ker v₀ →
      algebraMap A (Localization.AtPrime p.ker) x ∈ cRF I p.ker t) :
    algebraMap A D.B x ∈ D.RFB t := by
  have hp : HasPres A := hpA.out
  obtain ⟨l, hl⟩ := D.cB.RF_eq_lspan D.ek D.inv.nonneg t
  obtain ⟨N, hN⟩ := HasPres.exists_contract hp D.g D.B l
  have hRFB : ∀ y : A, algebraMap A D.B y ∈ D.RFB t ↔ y ∈ lspan N := fun y => by
    rw [LocData.RFB, hl]; exact hN y
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
    · rw [D.RFB_map_of_mem hI hgp hI' hv']; exact hx p hgp hI' hv'
    · rw [D.RFB_map_eq_top_of_isUnit hgp i hi hu t]; trivial
  obtain ⟨y, hy, hyx⟩ := D.exists_of_mem_map hgp _ hloc
  exact hy (hCp (hCx y ((hRFB _).1 hyx)))

end LocData

include hI in
/-- **Gluing at a point** (point form of `mem_cRF_of_cover`): membership in the chart ideals of a
cover of `V(𝔭)` gives membership in the maximal centre at every explicit point above `𝔭`. -/
theorem mem_cRF_of_cover_pt [Fact (HasPres A)] {𝔭 : Ideal A}
    (hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀)
    {n : ℕ} (f : Fin n → A) (g : Fin n → A) {i : A} (hi : i ∈ 𝔭)
    (hone : i + ∑ k, f k * g k = 1) (t : ℚ) {x : A}
    (hx : ∀ k, ∃ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal) (D : LocData I v₀ 𝔪), D.g = g k ∧
      algebraMap A D.B x ∈ D.RFB t)
    (p : Pt A) (h𝔭p : 𝔭 ≤ p.ker) :
    algebraMap A (Localization.AtPrime p.ker) x ∈ cRF I p.ker t := by
  set φ := algebraMap A (Localization.AtPrime p.ker)
  have hZ' := hZ p h𝔭p
  obtain ⟨D'⟩ := LocData.nonempty hI p.ker hZ'.1 hZ'.2
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
    rw [D'.RFB_map_of_mem hI D'.hg hZ'.1 hZ'.2, D'.map_algebraMap_B D'.hg] at h4
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

/-! ### Chart covers at explicit points (I1, I2) -/

/-- **A cover of `V(𝔭)` by local data at explicit points**, separated over points (I1). -/
structure ChartCoverPt (I : Ideal A) (v₀ : ℕ → ℚ) (𝔭 : Ideal A) where
  n : ℕ
  pt : Fin n → Pt A
  le : ∀ k, 𝔭 ≤ (pt k).ker
  D : ∀ k, LocData I v₀ (pt k).ker
  f : Fin n → A
  i : A
  hi : i ∈ 𝔭
  one : i + ∑ k, f k * (D k).g = 1
  sep : ∀ k (p : Pt A), (D k).g ∉ p.ker → I ≤ p.ker → InvAt I p.ker v₀ → 𝔭 ≤ p.ker

namespace ChartCoverPt

variable {𝔭 : Ideal A} (hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀)
  (C : ChartCoverPt I v₀ 𝔭)
include hI

include hZ in
/-- **`F_t` of a component is the intersection of the chart ideals of the cover.** -/
theorem mem_compFPt_iff [Fact (HasPres A)] (t : ℚ) (x : A) :
    x ∈ compFPt I 𝔭 t ↔ ∀ k, algebraMap A (C.D k).B x ∈ (C.D k).RFB t := by
  constructor
  · intro hx k
    exact (C.D k).mem_RFB_of_forall_pts hI t fun p hg hI' hv' =>
      mem_compFPt.1 hx p (C.sep k p hg hI' hv')
  · intro hx
    exact mem_compFPt.2 fun p h => mem_cRF_of_cover_pt hI hZ C.f (fun k => (C.D k).g) C.hi C.one t
      (fun k => ⟨(C.pt k).ker, inferInstance, C.D k, rfl, hx k⟩) p h

include hZ in
/-- **I2: on each open of the cover, the filtration is the chart ideal** (as ideals of
`(D k).B ≅ A[1/gₖ]`). A numerator of the chart ideal, multiplied by a power of `gₖ`, lies in every
chart ideal of the cover (`exists_pow_mul_mem_pt`, common exponent over `Fin n`), hence in `F_t`. -/
theorem map_compFPt [Fact (HasPres A)] (t : ℚ) (k : Fin C.n) :
    (compFPt I 𝔭 t).map (algebraMap A (C.D k).B) = (C.D k).RFB t := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact (C.mem_compFPt_iff hI hZ t x).1 hx k
  intro y hy
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (C.D k).N y
  have ha : algebraMap A (C.D k).B a ∈ (C.D k).RFB t := by
    have := (C.D k).RFB t |>.mul_mem_right (algebraMap A _ (s : A)) hy
    rwa [IsLocalization.mk'_spec] at this
  obtain ⟨M, hM⟩ := exists_uniform_list
    (P := fun j m => algebraMap A (C.D j).B ((C.D k).g ^ m * a) ∈ (C.D j).RFB t)
    (fun j m n hmn hm => by
      rw [← Nat.sub_add_cancel hmn, pow_add, mul_assoc, map_mul]
      exact Ideal.mul_mem_left _ _ hm)
    (List.finRange C.n) fun j _ => (C.D k).exists_pow_mul_mem_pt hI (C.D j) a t ha
  have hmem : (C.D k).g ^ M * a ∈ compFPt I 𝔭 t :=
    (C.mem_compFPt_iff hI hZ t _).2 fun j => hM j (List.mem_finRange j)
  have h1 := Ideal.mem_map_of_mem (algebraMap A (C.D k).B) hmem
  have hgu : IsUnit (algebraMap A (C.D k).B ((C.D k).g ^ M)) :=
    IsLocalization.map_units _ (⟨(C.D k).g ^ M,
      (C.D k).N.pow_mem (le_sup_right (a := (C.D k).M) (Submonoid.mem_powers _)) M⟩ : (C.D k).N)
  rw [map_mul] at h1
  have h2 := (Ideal.unit_mul_mem_iff_mem _ hgu).1 h1
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact Ideal.mul_mem_right _ _ h2

omit hI [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- Some chart of the cover is defined at a point above `𝔭` (decided chart by chart). -/
theorem exists_g_not_mem (p : Pt A) (h𝔭p : 𝔭 ≤ p.ker) : ∃ k, (C.D k).g ∉ p.ker := by
  rcases Constructive.fin_forall_or_exists (A := fun k => (C.D k).g ∈ p.ker)
    (B := fun k => (C.D k).g ∉ p.ker) (fun k => p.mem_ker_dec _) with h | h
  · exfalso
    refine (Ideal.IsMaximal.ne_top (inferInstance : p.ker.IsMaximal)) ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← C.one]
    exact Ideal.add_mem _ (h𝔭p C.hi) (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k))
  · exact h

include hZ C in
/-- **R3: the filtration at one point** is the centre's weighted ideal there (`≥` through a chart
of the cover defined at the point, I2 and `RFB_map_of_mem`). -/
theorem map_compFPt_pt [Fact (HasPres A)] (t : ℚ) (p : Pt A) (h𝔭p : 𝔭 ≤ p.ker) :
    (compFPt I 𝔭 t).map (algebraMap A (Localization.AtPrime p.ker)) = cRF I p.ker t := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_compFPt.1 hx p h𝔭p
  obtain ⟨k, hk⟩ := C.exists_g_not_mem p h𝔭p
  obtain ⟨hI', hv'⟩ := hZ p h𝔭p
  have hcomp : (Loc.map ((C.D k).ctrlN p.ker hk)).comp (algebraMap A (C.D k).B) =
      algebraMap A (Localization.AtPrime p.ker) :=
    RingHom.ext ((C.D k).map_algebraMap_B hk)
  rw [← (C.D k).RFB_map_of_mem hI hk hI' hv', ← C.map_compFPt hI hZ t k, Ideal.map_map, hcomp]

include hZ C in
/-- **R2: the steps of the filtration are explicitly finitely generated**: each chart ideal is
contracted to `A` (`HasPres.exists_contract`) and the contractions are intersected
(`HasPres.exists_inter_fin`), by `mem_compFPt_iff`. -/
theorem exists_lspan_compFPt [hpA : Fact (HasPres A)] (t : ℚ) :
    ∃ l : List A, compFPt I 𝔭 t = lspan l := by
  have hp : HasPres A := hpA.out
  have hN : ∀ k, ∃ N : List A, ∀ x : A,
      algebraMap A (C.D k).B x ∈ (C.D k).RFB t ↔ x ∈ lspan N := by
    intro k
    obtain ⟨l, hl⟩ := (C.D k).cB.RF_eq_lspan (C.D k).ek (C.D k).inv.nonneg t
    obtain ⟨N, hN⟩ := HasPres.exists_contract hp (C.D k).g (C.D k).B l
    exact ⟨N, fun y => by rw [LocData.RFB, hl]; exact hN y⟩
  obtain ⟨N, hN⟩ := Constructive.finite_choice_dep hN
  obtain ⟨L, hL⟩ := hp.exists_inter_fin C.n N
  refine ⟨L, Ideal.ext fun x => ?_⟩
  rw [C.mem_compFPt_iff hI hZ t x, hL]
  exact forall_congr' fun k => hN k x

end ChartCoverPt

namespace LocusComp

variable {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭)
include hI hmax h𝔭

/-- **I1: separated chart covers at explicit points exist**, constructively. The separating element
`q` (`1 - q ∈ 𝔭`, `q (𝔭) ⊆ locusPt`) comes from the explicit component list (m5,
`IsCompList.one_mem_sup_colon`, comaximality by `LocusComp.sup_eq_top`); the cover from bar induction
(`exists_cover`) with explicit points (`HasPres.exists_pt`) and finite choice over the cover. -/
theorem exists_chartCoverPt [hpA : Fact (HasPres A)] : Nonempty (ChartCoverPt I v₀ 𝔭) := by
  have hp : HasPres A := hpA.out
  obtain ⟨Pg, hPg⟩ := h𝔭.Pg
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  obtain ⟨Cs, hCs⟩ := hp.exists_compList Pg
  obtain ⟨C, hCm, hCe⟩ := hCs.exists_eq_of_mem_minimalPrimes (hPg ▸ h𝔭.min)
  -- the separating element
  obtain ⟨K, hK⟩ := HasPres.exists_colon hp Pg C
  have hcomax : ∀ D ∈ Cs, lspan D = lspan C ∨ (1 : A) ∈ lspan C ⊔ lspan D := fun D hDm => by
    rcases hp.eq_dec D C with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [(hCs.locusComp hPg hbd hb₀ h𝔭.gensI h𝔭.chartn hCm).sup_eq_top hI hmax
        (hCs.locusComp hPg hbd hb₀ h𝔭.gensI h𝔭.chartn hDm)
        (Ne.symm h)]
      trivial
  have hrad : ∀ (x : A) (k : ℕ), x ^ k ∈ lspan Pg → x ∈ lspan Pg := fun x k hk => by
    rw [← hPg] at hk ⊢
    exact fun p hI' hv' => (inferInstance : p.ker.IsPrime).mem_of_pow_mem k (hk p hI' hv')
  obtain ⟨c, hc, q, hq, hcq⟩ := Submodule.mem_sup.1
    (hCs.one_mem_sup_colon hcomax hrad K hK)
  rw [hCe] at hc
  have h1q : 1 - q ∈ 𝔭 := by rw [← hcq, add_sub_cancel_right]; exact hc
  have hqsep : ∀ p : Pt A, q ∉ p.ker → I ≤ p.ker → InvAt I p.ker v₀ → 𝔭 ≤ p.ker :=
    fun p hqp hI' hv' y hy => by
      have hqy : q * y ∈ locusPt I v₀ := by
        rw [hPg]; exact (hK q).1 hq y (hCe ▸ hy)
      exact ((inferInstance : p.ker.IsPrime).mem_or_mem (hqy p hI' hv')).resolve_left hqp
  -- the cover
  obtain ⟨Cg, hCg, -⟩ := h𝔭.gens
  have hsup : ∀ l : List A, 𝔭 ⊔ lspan l = lspan (Cg ++ l) := fun l => by
    rw [hCg, lspan_append_eq]
  let good : A → Prop := fun g => ∃ (p : Pt A) (D : LocData I v₀ p.ker),
    𝔭 ≤ p.ker ∧ D.g = g ∧ ∀ p' : Pt A, D.g ∉ p'.ker → I ≤ p'.ker → InvAt I p'.ker v₀ →
      𝔭 ≤ p'.ker
  obtain ⟨l, hl, h1⟩ := exists_cover 𝔭 (indNoeth_quotient_of_hasPres hp 𝔭) good
    (fun l => by rw [hsup]; exact hp.mem_dec _ 1) fun l _ hl1 => by
    rw [hsup] at hl1
    obtain ⟨p, hle⟩ := HasPres.exists_pt hp _ hl1
    rw [← hsup] at hle
    have h𝔭p : 𝔭 ≤ p.ker := le_sup_left.trans hle
    obtain ⟨hIp, hv⟩ := h𝔭.mem hI hmax p h𝔭p
    obtain ⟨D⟩ := LocData.nonempty hI p.ker hIp hv
    have hqp : q ∉ p.ker := fun h => (Ideal.IsMaximal.ne_top inferInstance)
      ((Ideal.eq_top_iff_one _).2 (by
        have := Ideal.add_mem _ (h𝔭p h1q) h
        rwa [sub_add_cancel] at this))
    let D' := D.restrict q hqp
    exact ⟨D'.g, ⟨p, D', h𝔭p, rfl, fun p' hg' hI' hv' =>
      hqsep p' (fun h => hg' (Ideal.mul_mem_left _ _ h)) hI' hv'⟩, fun h => D'.hg (hle h)⟩
  have hcov : (1 : A) ∈ 𝔭 ⊔ Ideal.span {g | good g} := by
    refine (sup_le_sup_left ?_ 𝔭) h1
    rw [lspan, Ideal.span_le]
    intro g hg; exact Ideal.subset_span (hl g hg)
  obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 hcov
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hy
  obtain ⟨F⟩ := fin_nonempty_pi (X := fun k : Fin n =>
    Σ' (p : Pt A), {D : LocData I v₀ p.ker //
      𝔭 ≤ p.ker ∧ D.g = (g k : A) ∧ ∀ p' : Pt A, D.g ∉ p'.ker → I ≤ p'.ker →
        InvAt I p'.ker v₀ → 𝔭 ≤ p'.ker}) fun k => by
    obtain ⟨p, D, hle, hDg, hsep⟩ := (g k).2
    exact ⟨⟨p, D, hle, hDg, hsep⟩⟩
  refine ⟨⟨n, fun k => (F k).1, fun k => (F k).2.2.1, fun k => (F k).2.1, f, i, hi, ?_,
    fun k => (F k).2.2.2.2⟩⟩
  rw [← hiy, ← hfg]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, (F k).2.2.2.1]

/-- **R3 for a component** (`ChartCoverPt.map_compFPt_pt` with a cover from I1). -/
theorem map_compFPt_pt [Fact (HasPres A)] (t : ℚ) (p : Pt A) (h𝔭p : 𝔭 ≤ p.ker) :
    (compFPt I 𝔭 t).map (algebraMap A (Localization.AtPrime p.ker)) = cRF I p.ker t := by
  obtain ⟨C⟩ := h𝔭.exists_chartCoverPt hI hmax
  exact C.map_compFPt_pt hI (fun q h => h𝔭.mem hI hmax q h) t p h𝔭p

/-- **R2 for a component**: `F_t` has explicit generators. -/
theorem exists_lspan_compFPt [Fact (HasPres A)] (t : ℚ) : ∃ l : List A, compFPt I 𝔭 t = lspan l := by
  obtain ⟨C⟩ := h𝔭.exists_chartCoverPt hI hmax
  exact C.exists_lspan_compFPt hI (fun q h => h𝔭.mem hI hmax q h) t

end LocusComp

end BezoutCounterexample.Principalization
