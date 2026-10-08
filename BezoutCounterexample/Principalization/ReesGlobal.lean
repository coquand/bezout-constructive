import BezoutCounterexample.Principalization.MaxLocus
import BezoutCounterexample.Principalization.CRFGen
import BezoutCounterexample.Principalization.ComponentFilPt
import BezoutCounterexample.Constructive.ChainLiftCanon
import BezoutCounterexample.Constructive.Enum
import BezoutCounterexample.Constructive.ChainLiftSmoothK
import BezoutCounterexample.Principalization.CompFilDecPtL
import BezoutCounterexample.Principalization.ComponentFilPtL

/-!
# The global weighted extended Rees algebra of a component

Notation 3.4 and Lemma 3.5 (2), (4) (`lem:rees`) of the paper.

* `WFil.loc`, `reesMap_isLocalization`: extended Rees algebras localize.
* `compFil`: the filtration `F_j = 𝓕_{j/d}` of a component of the maximal locus.
* `compFil_le_iSup`, `reesAlg_eq_adjoin`, `reesAlg_finiteType`: generation in degrees `≤ d`.
* `reesLoc_formallySmooth`, `rees_smooth`: the extended Rees algebra is smooth over `ℚ`: smooth
  on a basic open `D(a)` around each point (spreading out the local computation), and glued over a
  cover (`Constructive.ChainLiftSmoothK`); no quantification over the primes of the Rees algebra.
-/

noncomputable section


namespace BezoutCounterexample.Principalization

open LaurentPolynomial

section ReesLoc

variable {B : Type*} [CommRing B] [Algebra ℚ B] (Φ : WFil B) (L : Type*) [CommRing L] [Algebra ℚ L]
  [Algebra B L]

/-- The extended filtration. -/
def WFil.loc : WFil L where
  F j := (Φ.F j).map (algebraMap B L)
  mul_le a b := by rw [← Ideal.map_mul]; exact Ideal.map_mono (Φ.mul_le a b)
  zero_eq := by rw [Φ.zero_eq, Ideal.map_top]

/-- The coefficientwise map of Laurent polynomials. -/
abbrev lmap {L : Type*} [CommRing L] (f : B →+* L) : B[T;T⁻¹] →+* L[T;T⁻¹] := AddMonoidAlgebra.mapRingHom ℤ f

omit [Algebra ℚ B] in
lemma lmap_coeff {L : Type*} [CommRing L] (f : B →+* L) (p : B[T;T⁻¹]) (j : ℤ) : (lmap f p).coeff j = f (p.coeff j) :=
  AddMonoidAlgebra.coeff_mapRingHom f p j

omit [Algebra ℚ B] in
lemma lmap_C_mul_T {L : Type*} [CommRing L] [Algebra ℚ L] (f : B →+* L) (b : B) (j : ℤ) :
    lmap f (LaurentPolynomial.C b * T j) = LaurentPolynomial.C (f b) * T j := by
  ext m
  rw [lmap_coeff, coeff_C_mul_T, coeff_C_mul_T]
  split_ifs <;> simp

lemma laurent_coeff_sum {L : Type*} [CommRing L] {ι : Type*} (s : Finset ι) (f : ι → L[T;T⁻¹]) (j : ℤ) :
    (∑ i ∈ s, f i).coeff j = ∑ i ∈ s, (f i).coeff j := by
  show ((s.val.map f).sum).coeff j = (s.val.map fun i => (f i).coeff j).sum
  induction s.val using Multiset.induction_on with
  | empty => simp
  | cons a m ih => rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.sum_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ih]

/-- The induced map of extended Rees algebras. -/
def reesMap : ReesAlg Φ →+* ReesAlg (Φ.loc L) :=
  ((lmap (algebraMap B L)).comp (ReesAlg Φ).val.toRingHom).codRestrict
    (ReesAlg (Φ.loc L)).toSubring (fun p j => by
      show (lmap (algebraMap B L) p).coeff j ∈ (Φ.F j).map (algebraMap B L)
      rw [lmap_coeff]
      exact Ideal.mem_map_of_mem _ (p.2 j))

omit [Algebra ℚ L] [Algebra ℚ B] in
lemma reesMap_coe (p : ReesAlg Φ) :
    (reesMap Φ L p : L[T;T⁻¹]) = lmap (algebraMap B L) p := rfl

variable [IsDomain B] (M : Submonoid B) [IsLocalization M L]

omit [IsDomain B] [Algebra ℚ L] [Algebra ℚ B] in
/-- **The extended Rees algebra localizes**: `(Φ-Rees) ⊗ M⁻¹B` is the Rees algebra of the
localized filtration. -/
theorem reesMap_isLocalization (hM : M ≤ nonZeroDivisors B) :
    @IsLocalization _ _ (M.map (algebraMap B (ReesAlg Φ))) (ReesAlg (Φ.loc L)) _
      (reesMap Φ L).toAlgebra := by
  classical
  let : Algebra (ReesAlg Φ) (ReesAlg (Φ.loc L)) := (reesMap Φ L).toAlgebra
  have hinjB : Function.Injective (algebraMap B L) := IsLocalization.injective L hM
  have hmapB : ∀ b : B, algebraMap (ReesAlg Φ) (ReesAlg (Φ.loc L))
      (algebraMap B (ReesAlg Φ) b) = algebraMap L _ (algebraMap B L b) := by
    intro b
    apply Subtype.ext
    show lmap (algebraMap B L) (algebraMap B B[T;T⁻¹] b) = algebraMap L L[T;T⁻¹] (algebraMap B L b)
    rw [← LaurentPolynomial.C_eq_algebraMap, ← LaurentPolynomial.C_eq_algebraMap]
    ext m
    rw [lmap_coeff, LaurentPolynomial.C_apply, LaurentPolynomial.C_apply]
    split_ifs <;> simp
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, ⟨m, hm, rfl⟩⟩
    rw [hmapB]
    exact (IsLocalization.map_units L ⟨m, hm⟩).map _
  · intro z
    -- clear denominators coefficientwise
    have hco : ∀ j, ∃ (a : B) (m : M), a ∈ Φ.F j ∧
        (z : L[T;T⁻¹]).coeff j * algebraMap B L m = algebraMap B L a := by
      intro j
      obtain ⟨⟨a, m⟩, hm⟩ := (IsLocalization.mem_map_algebraMap_iff M L).1 (z.2 j)
      exact ⟨a, m, a.2, hm⟩
    -- a common denominator over a finite set of degrees, by induction (no choice)
    have key : ∀ S : Finset ℤ, ∃ (μ : M) (q : B[T;T⁻¹]), q ∈ ReesAlg Φ ∧ ∀ j,
        (if j ∈ S then (z : L[T;T⁻¹]).coeff j else 0) * algebraMap B L μ =
          algebraMap B L (q.coeff j) := by
      intro S
      induction S using Finset.induction_on with
      | empty => exact ⟨1, 0, zero_mem _, fun j => by simp⟩
      | insert j₀ S hj₀ ih =>
        obtain ⟨μ, q, hq, hμq⟩ := ih
        obtain ⟨a, m, ha, hm⟩ := hco j₀
        refine ⟨μ * m, LaurentPolynomial.C (m : B) * q +
          LaurentPolynomial.C (a * μ) * T j₀, ?_, fun j => ?_⟩
        · refine add_mem (mul_mem ?_ hq) (C_mul_T_mem_ReesAlg (Ideal.mul_mem_right _ _ ha))
          rw [LaurentPolynomial.C_eq_algebraMap]; exact Subalgebra.algebraMap_mem _ _
        · rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul', coeff_C_mul_T,
            Submonoid.coe_mul, map_add, map_mul, map_mul]
          by_cases hj : j = j₀
          · subst hj
            have h0 := hμq j
            rw [if_neg hj₀, zero_mul] at h0
            rw [if_pos (Finset.mem_insert_self _ _), if_pos rfl, ← h0, mul_zero, zero_add,
              map_mul, ← hm]
            ring
          · rw [if_neg hj, map_zero, add_zero]
            have h1 := hμq j
            have hS : (j ∈ insert j₀ S) = (j ∈ S) := propext (by simp [hj])
            simp only [hS]
            rw [← h1]
            ring
    obtain ⟨μ, q, hq, hμq⟩ := key (z : L[T;T⁻¹]).coeff.support
    refine ⟨⟨⟨q, hq⟩, ⟨algebraMap B (ReesAlg Φ) μ, ⟨μ, μ.2, rfl⟩⟩⟩, ?_⟩
    apply Subtype.ext
    simp only
    rw [hmapB]
    show (z : L[T;T⁻¹]) * algebraMap L L[T;T⁻¹] (algebraMap B L μ) = lmap (algebraMap B L) q
    ext j
    rw [← LaurentPolynomial.C_eq_algebraMap, mul_comm, coeff_C_mul', lmap_coeff, ← hμq j]
    by_cases hj : j ∈ (z : L[T;T⁻¹]).coeff.support
    · rw [if_pos hj, mul_comm]
    · rw [if_neg hj, Finsupp.notMem_support_iff.1 hj, mul_zero, zero_mul]
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (reesMap Φ L x : L[T;T⁻¹]) = reesMap Φ L y := congrArg Subtype.val hxy
    rw [reesMap_coe, reesMap_coe] at this
    have hxy' : (x : B[T;T⁻¹]) = y := by
      ext j
      have := congrArg (fun p : L[T;T⁻¹] => p.coeff j) this
      simp only [lmap_coeff] at this
      exact hinjB this
    simp [Subtype.ext hxy']

end ReesLoc

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- Local–global principle for ideals of a domain. -/
lemma Ideal.le_of_forall_map {J J' : Ideal A}
    (h : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], J.map (algebraMap A (Localization.AtPrime 𝔪)) ≤
      J'.map (algebraMap A (Localization.AtPrime 𝔪))) : J ≤ J' := by
  intro x hx
  by_contra hx'
  have hcol : J'.colon (Ideal.span {x}) ≠ ⊤ := by
    intro htop
    apply hx'
    have : (1 : A) ∈ J'.colon (Ideal.span {x}) := by rw [htop]; trivial
    have := Submodule.mem_colon.1 this x (Ideal.mem_span_singleton_self x)
    simpa using this
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hcol
  have := h𝔪
  have h1 := h 𝔪 (Ideal.mem_map_of_mem _ hx)
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff 𝔪.primeCompl] at h1
  obtain ⟨m, hm, hmx⟩ := h1
  apply hm
  apply hle
  rw [Submodule.mem_colon]
  intro y hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [smul_eq_mul, show m * (z * x) = z * (m * x) by ring]
  exact J'.mul_mem_left _ hmx

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (d : ℕ)

/-- The component filtration `F_j = 𝓕_{j/d}` as a filtration, at explicit points (D3.3d, R1). The
proof fields need neither `LocusComp.mem` nor `cRF_eq` (CRFGen, D3.6); `hI hmax h𝔭` stay in the
signature (explicit binders: `include` does not apply to definitions). -/
def compFil (hI : I ≠ ⊥)
    (hmax : IsMaxInvPt I v₀)
    (h𝔭 : LocusComp I v₀ 𝔭) (d : ℕ) : WFil A where
  F j := compFPt I 𝔭 ((j : ℚ) / d)
  mul_le a b := by
    rw [Ideal.mul_le]
    intro f hf g hg
    rw [mem_compFPt] at hf hg ⊢
    intro p h𝔭p
    have := cRF_mul_le_gen I p.ker _ _ (Ideal.mul_mem_mul (hf p h𝔭p) (hg p h𝔭p))
    rw [map_mul]
    convert this using 2
    push_cast; ring
  zero_eq := by
    ext f
    simp only [Int.cast_zero, zero_div, Submodule.mem_top, iff_true]
    rw [mem_compFPt]
    intro p _
    rw [cRF_of_nonpos_gen I p.ker le_rfl]; trivial

include hI hmax h𝔭


/-- **R1**: the steps of the filtration are the filtration at points. -/
lemma compFil_F (j : ℤ) : (compFil hI hmax h𝔭 d).F j = compFPt I 𝔭 ((j : ℚ) / d) := rfl

/-- The steps as the classical filtration (comparison; off the path). -/
lemma compFil_F_eq_compF (j : ℤ) : (compFil hI hmax h𝔭 d).F j = compF I 𝔭 ((j : ℚ) / d) :=
  compFPt_eq_compF I 𝔭 _

/-- The localized filtration at a maximal ideal above `𝔭` (classical: `compF_map` at an arbitrary
maximal ideal; off the path, see `compFil_loc_F_pt`). -/
lemma compFil_loc_F (𝔪 : Ideal A) [𝔪.IsMaximal] (h𝔭𝔪 : 𝔭 ≤ 𝔪) (j : ℤ) :
    ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime 𝔪)).F j = cRF I 𝔪 ((j : ℚ) / d) := by
  show ((compFil hI hmax h𝔭 d).F j).map _ = _
  rw [compFil_F_eq_compF]
  exact compF_map hI (IsMaxInvPt.toMax hmax) h𝔭.toMin 𝔪 h𝔭𝔪 _

/-- **The localized filtration at a point above `𝔭`** (R3). -/
lemma compFil_loc_F_pt [Fact (Constructive.HasPres A)] (p : Pt A) (h𝔭p : 𝔭 ≤ p.ker) (j : ℤ) :
    ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime p.ker)).F j = cRF I p.ker ((j : ℚ) / d) :=
  h𝔭.map_compFPt_pt hI hmax _ p h𝔭p

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

/-- The weights of an invariant are at most one. -/
lemma IsInv.le_one {S : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] {I : Ideal S} {n : ℕ}
    {e : Fin n → ℚ} (he : IsInv I n e) (hIm : I ≤ maximalIdeal S) (i : Fin n) : e i ≤ 1 := by
  obtain ⟨⟨J, -, rfl⟩, hmin⟩ := he
  set J₁ : MC S n := ⟨J.c, fun _ => 1, J.centred, fun _ => zero_le_one, fun _ _ _ => le_rfl⟩
  have hadm : J₁.Adm I := by
    refine hIm.trans ?_
    show maximalIdeal S ≤ J.c.RF (fun _ => 1) 1
    rw [J.centred, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact J.c.x_mem_RF (fun _ => 1) i one_ne_zero
  have h1 := hmin J₁ hadm
  have h0 : J.e ⟨0, lt_of_le_of_lt (Nat.zero_le _) i.2⟩ ≤ 1 := by
    by_contra hlt
    push Not at hlt
    refine absurd h1 (not_le.2 ⟨⟨0, lt_of_le_of_lt (Nat.zero_le _) i.2⟩, fun j hj => ?_, hlt⟩)
    exact absurd hj (Nat.not_lt_zero _)
  exact (J.anti (Fin.le_def.2 (Nat.zero_le _))).trans h0

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

/-- **Generation in bounded degrees**: `F_j = ∑_{1 ≤ l ≤ d} F_l F_{j-l}` for `j > d`.
Constructive (D3.3d): comaximal local–global over a chart cover at points (`ChartCoverPt`,
`Ideal.mem_of_cover`). On `D(i)`, `i ∈ 𝔭`, a power of `i` lies in `F_1 F_{j-1}` (I3); on the chart
`D(gₖ)`, `F_t` is the chart ideal (I2) and a monomial of weight `≥ j/d` splits off one coordinate
`x_i` of weight `wᵢ/d`, `1 ≤ wᵢ ≤ d`. -/
theorem compFil_le_iSup [Fact (Constructive.HasPres A)] {j : ℤ} (hj : (d : ℤ) < j) :
    (compFil hI hmax h𝔭 d).F j ≤
      ⨆ l ∈ Finset.Icc (1 : ℤ) d, (compFil hI hmax h𝔭 d).F l * (compFil hI hmax h𝔭 d).F (j - l) := by
  set Φ := compFil hI hmax h𝔭 d
  set Rj := ⨆ l ∈ Finset.Icc (1 : ℤ) d, Φ.F l * Φ.F (j - l)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hR : ∀ l : ℤ, 1 ≤ l → l ≤ d → Φ.F l * Φ.F (j - l) ≤ Rj := fun l h1 h2 =>
    le_iSup₂_of_le (f := fun l (_ : l ∈ Finset.Icc (1 : ℤ) d) => Φ.F l * Φ.F (j - l)) l
      (Finset.mem_Icc.2 ⟨h1, h2⟩) le_rfl
  -- D3.8 (E2): the cover `exists_chartCoverPtL` from the generators and charts of `h𝔭`
  obtain ⟨lI, hlI⟩ := h𝔭.gensI
  obtain ⟨dim, hchartn⟩ := h𝔭.chartn
  have hchart := h𝔭.hchart
  obtain ⟨C, -, -⟩ := h𝔭.exists_chartCoverPtL hI hmax lI hlI dim hchartn
  have hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀ :=
    fun p h => h𝔭.mem_ptL hI lI hlI hchart hmax p h
  intro x hx
  have h1 : (1 : A) ∈ Constructive.lspan (C.i :: List.ofFn fun k => (C.D k).g) := by
    rw [← C.one]
    refine Ideal.add_mem _ (Ideal.subset_span List.mem_cons_self)
      (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
    exact List.mem_cons_of_mem _ (List.mem_ofFn.2 ⟨k, rfl⟩)
  refine Ideal.mem_of_cover _ h1 fun g hg => ?_
  rcases List.mem_cons.1 hg with rfl | hg
  · -- `D(i)`: `i^(b + b') ∈ F_1 F_{j-1}`
    obtain ⟨b, hb⟩ := h𝔭.exists_pow_mem_compFPt_ptL hI lI hlI hchart hmax hd hw C.hi
      (((1 : ℤ) : ℚ) / d)
    obtain ⟨b', hb'⟩ := h𝔭.exists_pow_mem_compFPt_ptL hI lI hlI hchart hmax hd hw C.hi
      (((j - 1 : ℤ) : ℚ) / d)
    have hb1 : C.i ^ b ∈ Φ.F 1 := hb
    have hb2 : C.i ^ b' ∈ Φ.F (j - 1) := hb'
    refine ⟨b + b', ?_⟩
    rw [pow_add]
    exact Ideal.mul_mem_right _ _ (hR 1 le_rfl (by exact_mod_cast hd) (Ideal.mul_mem_mul hb1 hb2))
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hg
  set D := C.D k
  have hmap : ∀ l : ℤ, (Φ.F l).map (algebraMap A D.B) = D.RFB ((l : ℚ) / d) := fun l =>
    C.map_compFPt_L hI lI hlI hchart hZ _ k
  refine exists_pow_mul_mem_of_away D.g D.B ?_
  have hxB : algebraMap A D.B x ∈ D.RFB ((j : ℚ) / d) := by
    rw [← hmap]; exact Ideal.mem_map_of_mem _ hx
  have hI' : I ≤ (C.pt k).ker := (hZ _ (C.le k)).1
  revert hxB
  generalize algebraMap A D.B x = y
  intro hy
  refine (show D.RFB ((j : ℚ) / d) ≤ Rj.map (algebraMap A D.B) from ?_) hy
  rw [LocDataPt.RFB, Chart.RF, Ideal.span_le]
  rintro _ ⟨α, h0, hα, rfl⟩
  -- pick a coordinate occurring in `α` (decided coordinatewise)
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    rcases Constructive.fin_forall_or_exists (A := fun i => α i = 0) (B := fun i => α i ≠ 0)
      (fun i => (Nat.decEq (α i) 0).em) with h | h
    · exfalso
      rw [show α = 0 from Finsupp.ext h, lam_zero] at hα
      have : (0 : ℚ) < (j : ℚ) / d := div_pos (by exact_mod_cast (by omega : (0 : ℤ) < j)) hdq
      linarith
    · exact h
  have hei : D.ek i ≠ 0 := fun h => hi (h0 i h)
  have hv : D.ek i = v₀ i := by
    have := congrFun D.hv i
    rwa [ext0_apply] at this
  obtain ⟨w, hw'⟩ := hw i
  rw [← hv] at hw'
  have hle1 : D.ek i ≤ 1 := D.inv.le_one (Iloc_le hI') i
  have hpos : 0 < D.ek i := lt_of_le_of_ne (D.inv.nonneg i) (Ne.symm hei)
  have hw1 : 1 ≤ w := by
    have : (0 : ℚ) < w := by rw [hw']; positivity
    exact_mod_cast this
  have hwd : w ≤ d := by
    have : (w : ℚ) ≤ d := by rw [hw']; nlinarith
    exact_mod_cast this
  have hei' : D.ek i = (w : ℚ) / d := by rw [hw']; field_simp
  -- split off `x_i`
  set β := α - Finsupp.single i 1
  have hαβ : α = β + Finsupp.single i 1 := by
    rw [tsub_add_cancel_of_le]
    exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
  have hprod : ∏ l, D.cB.x l ^ α l = D.cB.x i * ∏ l, D.cB.x l ^ β l := by
    rw [hαβ]
    simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [mul_comm, Finset.prod_eq_single i]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · simp
  have hlamβ : lam D.ek β = lam D.ek α - D.ek i := by
    rw [hαβ, lam_add, lam_single]; ring
  have h1 : D.cB.x i ∈ D.RFB (((w : ℤ) : ℚ) / d) := by
    have := D.cB.x_mem_RF D.ek i hei
    rw [hei'] at this; push_cast; exact this
  have h2 : ∏ l, D.cB.x l ^ β l ∈ D.RFB (((j - w : ℤ) : ℚ) / d) := by
    apply Ideal.subset_span
    refine ⟨β, fun l hl => ?_, ?_, rfl⟩
    · have := h0 l hl
      rw [hαβ, Finsupp.add_apply] at this
      omega
    · rw [hlamβ, hei']
      push_cast
      rw [sub_div]
      linarith
  rw [SetLike.mem_coe, hprod]
  refine Ideal.map_mono (hR w (by exact_mod_cast hw1) (by exact_mod_cast hwd)) ?_
  rw [Ideal.map_mul, hmap, hmap]
  exact Ideal.mul_mem_mul h1 h2

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (d : ℕ)

include hI hmax h𝔭 in
lemma compFil_F_nonpos {j : ℤ} (hj : j ≤ 0) : (compFil hI hmax h𝔭 d).F j = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [compFil_F, mem_compFPt]
  intro p _
  -- D3.8: `cRF_of_nonpos_gen` (no `LocusComp.mem`, no `cRF_eq`)
  rw [cRF_of_nonpos_gen I p.ker (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hj)
    (Nat.cast_nonneg d))]
  trivial

/-- **Canonical generators of the filtration steps** (data; R2): the canonical generators
(`ChainLiftCanon`) of `F_j`, for an enumeration `en` of `A`. A function of the ideal `F_j` alone. -/
def canonGensF [hp : Fact (Constructive.HasPres A)] (en : ℕ → A) (hen : Function.Surjective en)
    (j : ℤ) : List A :=
  Constructive.canonGens en hen hp.out.mem_dec ((compFil hI hmax h𝔭 d).F j)
    (h𝔭.exists_lspan_compFPtP hI hmax _)

lemma lspan_canonGensF [Fact (Constructive.HasPres A)] (en : ℕ → A) (hen : Function.Surjective en)
    (j : ℤ) : Constructive.lspan (canonGensF hI hmax h𝔭 d en hen j) = (compFil hI hmax h𝔭 d).F j :=
  Constructive.lspan_canonGens _ _ _ _ _

/-- **Generating lists of the filtration steps** (group B): the canonical generators of the stage
enumeration (`Constructive.Enum`). -/
def gensF [Fact (Constructive.HasPres A)] [Constructive.Enum A] (j : ℤ) : List A :=
  canonGensF hI hmax h𝔭 d Constructive.Enum.en Constructive.Enum.hen j

lemma span_gensF [Fact (Constructive.HasPres A)] [Constructive.Enum A] (j : ℤ) :
    Ideal.span {g | g ∈ gensF hI hmax h𝔭 d j} = (compFil hI hmax h𝔭 d).F j :=
  lspan_canonGensF hI hmax h𝔭 d _ _ j

/-- The pairs `(j, g)`, `1 ≤ j ≤ d`, `g ∈ canonGensF j` (over `List.range`, no `Finset.toList`). -/
def canonGenPairs [Fact (Constructive.HasPres A)] (en : ℕ → A) (hen : Function.Surjective en) :
    List (ℤ × A) :=
  (List.range d).flatMap fun k : ℕ => (canonGensF hI hmax h𝔭 d en hen ((k : ℤ) + 1)).map fun g =>
    ((k : ℤ) + 1, g)

lemma mem_canonGenPairs [Fact (Constructive.HasPres A)] (en : ℕ → A) (hen : Function.Surjective en)
    {q : ℤ × A} : q ∈ canonGenPairs hI hmax h𝔭 d en hen ↔
      1 ≤ q.1 ∧ q.1 ≤ d ∧ q.2 ∈ canonGensF hI hmax h𝔭 d en hen q.1 := by
  obtain ⟨j, g⟩ := q
  rw [canonGenPairs, List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, hq⟩
    obtain ⟨g', hg', he⟩ := List.mem_map.1 hq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have := List.mem_range.1 hk
    exact ⟨by omega, by omega, hg'⟩
  · rintro ⟨h1, hd, hg⟩
    refine ⟨(j - 1).toNat, List.mem_range.2 (by omega), List.mem_map.2 ⟨g, ?_, ?_⟩⟩
    · rwa [show ((j - 1).toNat : ℤ) + 1 = j by omega]
    · rw [show ((j - 1).toNat : ℤ) + 1 = j by omega]

/-- Generators of the extended Rees algebra: `T⁻¹` and `g T^j` for generators `g` of `F_j`,
`1 ≤ j ≤ d`. -/
def reesGenSet [Fact (Constructive.HasPres A)] [Constructive.Enum A] : Set A[T;T⁻¹] :=
  {T (-1)} ∪ ⋃ j ∈ Finset.Icc (1 : ℤ) d,
    (fun g => LaurentPolynomial.C g * T j) '' {g | g ∈ gensF hI hmax h𝔭 d j}

lemma reesGenSet_finite [Fact (Constructive.HasPres A)] [Constructive.Enum A] : (reesGenSet hI hmax h𝔭 d).Finite := by
  refine (Set.finite_singleton _).union ?_
  refine Set.Finite.biUnion (Finset.finite_toSet _) fun j _ => ?_
  exact (List.finite_toSet _).image _

lemma reesGenSet_subset [Fact (Constructive.HasPres A)] [Constructive.Enum A] : reesGenSet hI hmax h𝔭 d ⊆ ReesAlg (compFil hI hmax h𝔭 d) := by
  rintro _ (h | h)
  · rw [Set.mem_singleton_iff] at h
    subst h
    have : (T (-1) : A[T;T⁻¹]) = LaurentPolynomial.C 1 * T (-1) := by simp
    rw [this]
    exact C_mul_T_mem_ReesAlg (by rw [compFil_F_nonpos hI hmax h𝔭 d (by norm_num)]; trivial)
  · simp only [Set.mem_iUnion, Set.mem_image] at h
    obtain ⟨j, -, g, hg, rfl⟩ := h
    exact C_mul_T_mem_ReesAlg (by rw [← span_gensF]; exact Ideal.subset_span hg)

variable (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hd hw

/-- **R2, generic in the generators**: every homogeneous element lies in the algebra generated by
`T⁻¹` and `g T^j` for `g` in a generating set of `F_j`, `1 ≤ j ≤ d`. -/
theorem C_mul_T_mem_adjoin_set [Fact (Constructive.HasPres A)] (gens : ℤ → Set A)
    (hgens : ∀ j : ℤ, 1 ≤ j → j ≤ d → Ideal.span (gens j) = (compFil hI hmax h𝔭 d).F j)
    (j : ℤ) (f : A) (hf : f ∈ (compFil hI hmax h𝔭 d).F j) :
    LaurentPolynomial.C f * T j ∈ Algebra.adjoin A ({T (-1)} ∪ ⋃ j ∈ Finset.Icc (1 : ℤ) d,
      (fun g => LaurentPolynomial.C g * T j) '' gens j) := by
  set R' := Algebra.adjoin A ({T (-1)} ∪ ⋃ j ∈ Finset.Icc (1 : ℤ) d,
      (fun g => LaurentPolynomial.C g * T j) '' gens j)
  set Φ := compFil hI hmax h𝔭 d
  -- the ideal of coefficients in degree `j`
  let Mj : ℤ → Ideal A := fun j =>
    (Subalgebra.toSubmodule R').comap ((LinearMap.lsmul A A[T;T⁻¹]).flip (T j))
  have hMj : ∀ j f, f ∈ Mj j ↔ LaurentPolynomial.C f * T j ∈ R' := fun j f => by
    show f • (T j : A[T;T⁻¹]) ∈ R' ↔ _
    rw [Algebra.smul_def, ← LaurentPolynomial.C_eq_algebraMap]
  have base : ∀ j : ℤ, j ≤ d → ∀ f ∈ Φ.F j, LaurentPolynomial.C f * T j ∈ R' := by
    intro j hjd f hf
    by_cases hj0 : j ≤ 0
    · have h1 : (LaurentPolynomial.C f * T j : A[T;T⁻¹]) =
          algebraMap A A[T;T⁻¹] f * (T (-1)) ^ (-j).toNat := by
        rw [← LaurentPolynomial.C_eq_algebraMap, T_pow]
        congr 2
        omega
      rw [h1]
      exact R'.mul_mem (R'.algebraMap_mem f)
        (R'.pow_mem (Algebra.subset_adjoin (Or.inl rfl)) _)
    · have hj1 : 1 ≤ j := by omega
      rw [← hMj]
      have hle : Φ.F j ≤ Mj j := by
        rw [← hgens j hj1 hjd, Ideal.span_le]
        intro g hg
        rw [SetLike.mem_coe, hMj]
        apply Algebra.subset_adjoin
        right
        simp only [Set.mem_iUnion, Set.mem_image]
        exact ⟨j, Finset.mem_Icc.2 ⟨hj1, hjd⟩, g, hg, rfl⟩
      exact hle hf
  have main : ∀ N : ℕ, ∀ j : ℤ, j ≤ N → ∀ f ∈ Φ.F j, LaurentPolynomial.C f * T j ∈ R' := by
    intro N
    induction N with
    | zero => intro j hj f hf; exact base j (by omega) f hf
    | succ N ih =>
      intro j hj f hf
      by_cases hjd : j ≤ d
      · exact base j hjd f hf
      · push Not at hjd
        rw [← hMj]
        have hsup := compFil_le_iSup hI hmax h𝔭 hd hw hjd hf
        refine (iSup₂_le fun l hl => ?_ : _ ≤ Mj j) hsup
        rw [Ideal.mul_le]
        intro a ha b hb
        rw [hMj]
        have hl' := Finset.mem_Icc.1 hl
        have h1 := base l (by omega) a ha
        have h2 := ih (j - l) (by push_cast at hj ⊢; omega) b hb
        have : (LaurentPolynomial.C (a * b) * T j : A[T;T⁻¹]) =
            (LaurentPolynomial.C a * T l) * (LaurentPolynomial.C b * T (j - l)) := by
          rw [map_mul, show j = l + (j - l) by ring, T_add]
          ring_nf
        rw [this]; exact R'.mul_mem h1 h2
  exact main j.toNat j (Int.self_le_toNat j) f hf

/-- Every homogeneous element lies in the algebra generated by `reesGenSet`. -/
theorem C_mul_T_mem_adjoin [Constructive.Enum A] [Fact (Constructive.HasPres A)] (j : ℤ) (f : A)
    (hf : f ∈ (compFil hI hmax h𝔭 d).F j) :
    LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (reesGenSet hI hmax h𝔭 d) :=
  C_mul_T_mem_adjoin_set hI hmax h𝔭 d hd hw (fun j => {g | g ∈ gensF hI hmax h𝔭 d j})
    (fun j _ _ => span_gensF hI hmax h𝔭 d j) j f hf

omit hd hw in
/-- The generating set of a generator family given as lists. -/
def reesGenSetOf (gens : ℤ → List A) : Set A[T;T⁻¹] :=
  {T (-1)} ∪ ⋃ j ∈ Finset.Icc (1 : ℤ) d, (fun g => LaurentPolynomial.C g * T j) '' {g | g ∈ gens j}

/-- **R2 for a list family of generators** (the interface of the Rees certificate; any `gens` with
`lspan (gens j) = F_j` for `1 ≤ j ≤ d`, e.g. `canonGensF`). -/
theorem C_mul_T_mem_adjoin_of [Fact (Constructive.HasPres A)] (gens : ℤ → List A)
    (hgens : ∀ j : ℤ, 1 ≤ j → j ≤ d → Constructive.lspan (gens j) = (compFil hI hmax h𝔭 d).F j)
    (j : ℤ) (f : A) (hf : f ∈ (compFil hI hmax h𝔭 d).F j) :
    LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (reesGenSetOf d gens) :=
  C_mul_T_mem_adjoin_set hI hmax h𝔭 d hd hw (fun j => {g | g ∈ gens j}) hgens j f hf

/-- **The extended Rees algebra is generated by `reesGenSet`.** -/
theorem reesAlg_eq_adjoin [Constructive.Enum A] [Fact (Constructive.HasPres A)] :
    ReesAlg (compFil hI hmax h𝔭 d) = Algebra.adjoin A (reesGenSet hI hmax h𝔭 d) := by
  apply le_antisymm
  · intro p hp
    have hp' : p = ∑ j ∈ p.coeff.support, LaurentPolynomial.C (p.coeff j) * T j := by
      conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [single_eq_C_mul_T]
    rw [hp']
    exact Subalgebra.sum_mem _ fun j _ => C_mul_T_mem_adjoin hI hmax h𝔭 d hd hw j _ (hp j)
  · rw [Algebra.adjoin_le_iff]
    exact reesGenSet_subset hI hmax h𝔭 d

/-- **The extended Rees algebra is of finite type.** -/
theorem reesAlg_finiteType [Fact (Constructive.HasPres A)] : Algebra.FiniteType A (ReesAlg (compFil hI hmax h𝔭 d)) := by
  obtain ⟨_E⟩ := Constructive.HasPres.nonempty_enum (Fact.out : Constructive.HasPres A)
  letI := _E
  have hfg : (ReesAlg (compFil hI hmax h𝔭 d)).FG := by
    rw [reesAlg_eq_adjoin hI hmax h𝔭 d hd hw]
    exact Subalgebra.fg_def.2 ⟨_, reesGenSet_finite hI hmax h𝔭 d, rfl⟩
  exact (Subalgebra.fg_iff_finiteType _).1 hfg

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

instance laurent_tower {B : Type*} [CommRing B] : IsScalarTower B (Polynomial B) B[T;T⁻¹] :=
  IsScalarTower.of_algebraMap_eq fun b => by
    rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show LaurentPolynomial.C b = Polynomial.toLaurent (Polynomial.C b)
    rw [Polynomial.toLaurent_C]

/-- Laurent polynomials over a formally smooth `ℚ`-algebra are formally smooth. -/
instance laurent_formallySmooth {B : Type*} [CommRing B] [Algebra ℚ B] [Algebra.FormallySmooth ℚ B] :
    Algebra.FormallySmooth ℚ B[T;T⁻¹] := by
  have : Algebra.FormallySmooth (Polynomial B) B[T;T⁻¹] :=
    Algebra.FormallySmooth.of_isLocalization (Submonoid.powers (Polynomial.X : Polynomial B))
  have : Algebra.FormallySmooth B B[T;T⁻¹] := Algebra.FormallySmooth.comp B (Polynomial B) B[T;T⁻¹]
  exact Algebra.FormallySmooth.comp ℚ B B[T;T⁻¹]

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

/-- The localized Rees algebras are formally smooth. -/
theorem reesLoc_formallySmooth (𝔪 : Ideal A) [𝔪.IsMaximal] :
    Algebra.FormallySmooth ℚ (ReesAlg ((compFil hI hmax h𝔭 d).loc (Localization.AtPrime 𝔪))) := by
  set Φ' := (compFil hI hmax h𝔭 d).loc (Localization.AtPrime 𝔪)
  by_cases h𝔭𝔪 : 𝔭 ≤ 𝔪
  · have hZ := h𝔭.mem_max hI hmax 𝔪 h𝔭𝔪
    obtain ⟨n, e, ⟨⟨J, hJ, hJe⟩, hmin⟩, hev⟩ := hZ.2
    have hJi : IsInv (Iloc I 𝔪) n J.e := ⟨⟨J, hJ, rfl⟩, by rw [hJe]; exact hmin⟩
    have := residueField_isIntegral 𝔪
    obtain ⟨k, ck, hrun, -, -, hsupp⟩ := hJi.exists_run (Iloc_ne_bot hI 𝔪) (Iloc_le hZ.1) J.c
      J.centred
    have hkn : k ≤ n := hrun.stage_le (Nat.zero_le _)
    have hw' : ∀ i : Fin n, ∃ w : ℕ, (w : ℚ) = d * J.e i := fun i => by
      obtain ⟨w, hw⟩ := hw i
      refine ⟨w, ?_⟩
      rw [hw, ← hev, hJe, ext0_apply]
    choose w hwe using hw'
    have hF : ∀ j, Φ'.F j = chartFil J.c J.e d j := fun j => by
      rw [compFil_loc_F hI hmax h𝔭 d 𝔪 h𝔭𝔪, cRF_eq hI hZ.1 hJ hJi]; rfl
    exact rees_formallySmooth J.c J.centred hF J.nonneg hd hwe hkn hsupp
  · have htop : ReesAlg Φ' = ⊤ := by
      rw [eq_top_iff]
      intro p _ j
      show p.coeff j ∈ ((compFil hI hmax h𝔭 d).F j).map _
      rw [compFil_F_eq_compF, compF_map_of_not_le hI (IsMaxInvPt.toMax hmax) h𝔭.toMin hd hw 𝔪 h𝔭𝔪]; trivial
    exact Algebra.FormallySmooth.of_equiv
      (((Subalgebra.equivOfEq _ _ htop).trans Subalgebra.topEquiv).restrictScalars ℚ).symm

end BezoutCounterexample.Principalization


namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hmax h𝔭 hd hw

theorem rees_finitePresentation [Fact (Constructive.HasPres A)] :
    Algebra.FinitePresentation ℚ (ReesAlg (compFil hI hmax h𝔭 d)) := by
  have := reesAlg_finiteType hI hmax h𝔭 d hd hw
  have : Algebra.FiniteType ℚ (ReesAlg (compFil hI hmax h𝔭 d)) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  exact Algebra.FinitePresentation.of_finiteType.1 inferInstance

omit hI hmax h𝔭 hd hw in
/-- The only use of maximal ideals in `rees_smooth`: a set of elements meeting the complement of
every maximal ideal generates the unit ideal (Zorn; to be replaced by explicit points, Task C). -/
lemma span_eq_top_of_forall_isMaximal {B : Type*} [CommRing B] (s : Set B)
    (h : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ a ∈ s, a ∉ 𝔪) : Ideal.span s = ⊤ := by
  by_contra hne
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨a, ha, ha𝔪⟩ := h 𝔪 h𝔪
  exact ha𝔪 (hle (Ideal.subset_span ha))

/-- **The extended Rees algebra is smooth over `ℚ`.** Around each maximal ideal `𝔪` of `A` the
localized Rees algebra is formally smooth (`reesLoc_formallySmooth`); this spreads out to a basic
open `D(a)`, `a ∉ 𝔪` (`exists_away_smooth_of_isLocalization`), and the pieces glue
(`smooth_of_span_cover`). -/
theorem rees_smooth [Fact (Constructive.HasPres A)] : Algebra.Smooth ℚ (ReesAlg (compFil hI hmax h𝔭 d)) := by
  set Φ := compFil hI hmax h𝔭 d
  set R := ReesAlg Φ
  have := rees_finitePresentation hI hmax h𝔭 hd hw
  have hloc : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal →
      ∃ a ∈ {a : A | Algebra.Smooth ℚ (Localization.Away (algebraMap A R a))}, a ∉ 𝔪 := by
    intro 𝔪 h𝔪
    set Rm := ReesAlg (Φ.loc (Localization.AtPrime 𝔪))
    let : Algebra R Rm := (reesMap Φ (Localization.AtPrime 𝔪)).toAlgebra
    have : IsScalarTower ℚ R Rm := IsScalarTower.of_algebraMap_eq fun q =>
      congrArg (fun f : ℚ →+* Rm => f q)
        (RingHom.ext_rat (algebraMap ℚ Rm) ((algebraMap R Rm).comp (algebraMap ℚ R)))
    have : IsLocalization (𝔪.primeCompl.map (algebraMap A R)) Rm :=
      reesMap_isLocalization Φ (Localization.AtPrime 𝔪) 𝔪.primeCompl
        (Ideal.primeCompl_le_nonZeroDivisors 𝔪)
    have : Algebra.FormallySmooth ℚ Rm := reesLoc_formallySmooth hI hmax h𝔭 hd hw 𝔪
    obtain ⟨a, ha, hsm⟩ :=
      Constructive.exists_away_smooth_of_isLocalization (S := R) (Sₘ := Rm) 𝔪.primeCompl
    exact ⟨a, hsm, ha⟩
  refine Constructive.smooth_of_span_cover (algebraMap A R '' {a : A |
    Algebra.Smooth ℚ (Localization.Away (algebraMap A R a))}) ?_ ?_
  · rw [← Ideal.map_span, span_eq_top_of_forall_isMaximal _ hloc, Ideal.map_top]
  · rintro _ ⟨a, ha, rfl⟩
    exact ha

end BezoutCounterexample.Principalization

