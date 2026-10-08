import BezoutCounterexample.Principalization.CompFilDecPtL
import BezoutCounterexample.Principalization.RFStablePt
import BezoutCounterexample.Principalization.ComponentFilPtL
import BezoutCounterexample.Principalization.ReesVertex
import BezoutCounterexample.Constructive.DynRees
import BezoutCounterexample.Principalization.CRFGen

/-!
# The exceptional divisor of the Rees algebra is prime, choice-free (leaf; (A) A4, A5, A7)

`rees_s_prime` (via `span_s_isPrime`, `compFil_mul_not_mem`, `not_mem_loc`) uses `compF_map`, a
maximal ideal above `𝔭` (Zorn), `cRF_eq` and `by_contra` on memberships. At explicit points:

* `LocDataPt.RFB_map_of_mem_L`: `RFB_map_of_mem` with `cRF_eq_of_rf` (no `cRF_eq`);
* `LocusComp.exists_chart_ptL`: at a point above `𝔭`, `cRF` is the weighted ideal of a centred chart
  with integral weights, and its `1/d`-step contracts into `𝔭`;
* `LocusComp.not_mem_loc_ptL` (A4): `x ∉ F_{a+1}` stays a non-membership at every point above `𝔭`.
  From `x_q ∈ cRF_q` a chart of the cover gives `u ∉ 𝔭` with `u x ∈ F_{a+1}`; then at every point
  `p` the graded domain (`RF_mul_not_mem_dec`) and `¬¬`-stability (`mem_RF_stable`) give
  `x_p ∈ cRF_p`, i.e. `x ∈ F_{a+1}` by the definition of `compFPt`;
* `LocusComp.compFPt_mul_not_mem_ptL` (A5): the graded ring of `F` is a domain, at one explicit point
  `q` above `𝔭` (`HasPres.exists_pt`);
* `LocusComp.rees_s_isPrime_ptL` (A7): `Constructive.rees_s_dyn` with `hdec := compFPt_dec_ptL`
  and `Q := False`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing IsLocalization LaurentPolynomial

/-- `Chart.RF_le_span` without `classical` (the support test is decided over `Fin n`). -/
lemma Chart.RF_le_span_dec {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ} (c : Chart R n)
    (e : Fin n → ℚ) {t : ℚ} (ht : 0 < t) : c.RF e t ≤ Ideal.span (c.x '' {i | e i ≠ 0}) := by
  rw [Chart.RF, Ideal.span_le]
  rintro _ ⟨α, h0, hα, rfl⟩
  by_cases hex : ∃ i, α i ≠ 0
  · obtain ⟨i, hi⟩ := hex
    have hei : e i ≠ 0 := fun h => hi (h0 i h)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    refine Ideal.mul_mem_right _ _ ?_
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_image_of_mem c.x hei)) _
      (Nat.pos_of_ne_zero hi)
  · have : α = 0 := Finsupp.ext fun i => Decidable.of_not_not fun hi => hex ⟨i, hi⟩
    rw [this, lam_zero] at hα; linarith

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

namespace LocDataPt

variable {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocDataPt I v₀ 𝔪)

/-- `RFB_map_of_mem` without `cRF_eq`. -/
lemma RFB_map_of_mem_L (p : Pt A) (hg' : D.g ∉ p.ker) (hv' : InvAt I p.ker v₀) (t : ℚ) :
    (D.RFB t).map (Loc.map (D.ctrlN p.ker hg')) = cRF I p.ker t := by
  obtain ⟨n', e', he', hev⟩ := hv'
  obtain rfl := he'.card_eq (Loc.transport (D.ctrl p.ker hg') D.ck)
  have hee : e' = D.ek := ext0_injective (hev.trans D.hv.symm)
  subst hee
  rw [cRF_eq_of_rf he' fun J' hJ' hJe => D.rf p hg' J' hJ' hJe t, RFB, Loc.map_RF,
    D.transport_cB p hg']

end LocDataPt

variable [Algebra.FiniteType ℚ A]
  {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} (l : List A) (hl : I = lspan l)
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {dim : ℕ}
  (hchartn : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) dim))
  {d : ℕ} (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

namespace LocusComp

include hI l hl hmax h𝔭 hchartn hd hw

omit [Algebra.FiniteType ℚ A] in
/-- At an explicit point above `𝔭`: `cRF` is the weighted ideal of a centred chart with integral
weights, and its step `1/d` contracts into `𝔭`. -/
theorem exists_chart_ptL [Fact (HasPres A)] (p : Pt A) (h𝔭p : 𝔭 ≤ p.ker) :
    ∃ (n : ℕ) (c : Chart (Localization.AtPrime p.ker) n) (e : Fin n → ℚ) (w : Fin n → ℕ),
      c.IsCentred ∧ (∀ i, 0 ≤ e i) ∧ (∀ i, (w i : ℚ) = d * e i) ∧
      (∀ t, cRF I p.ker t = c.RF e t) ∧
      ∀ u : A, algebraMap A (Localization.AtPrime p.ker) u ∈ c.RF e (1 / d) → u ∈ 𝔭 := by
  have hchart := hchart_of_dim hI l hl hmax h𝔭 hchartn
  obtain ⟨hIp, hv⟩ := h𝔭.mem_ptL hI l hl hchart hmax p h𝔭p
  obtain ⟨f₀, hf₀, n₀, ⟨c₀⟩⟩ := hchart p
  obtain ⟨D⟩ := LocDataPt.nonempty hI l hl p hIp hv hf₀ c₀
  have hw' : ∀ i : Fin D.n, ∃ w : ℕ, (w : ℚ) = d * D.ek i := fun i => by
    obtain ⟨w, hw⟩ := hw i
    have hv0 : v₀ i = D.ek i := by
      have := congrFun D.hv (i : ℕ); rw [ext0_apply] at this; exact this.symm
    exact ⟨w, by rw [hw, hv0]⟩
  obtain ⟨w, hwe⟩ := Constructive.finite_choice_dep hw'
  refine ⟨D.n, Loc.transport (D.ctrl p.ker D.hg) D.ck, D.ek, w, D.cent, D.inv.nonneg, hwe,
    D.cRF_eq_pt, fun u hu => ?_⟩
  have hp : 𝔭 = D.p := h𝔭.eq_p_ptL D h𝔭p
  have h2 := Chart.RF_le_span_dec _ D.ek (by positivity) hu
  have hset : {i | D.ek i ≠ 0} = {i : Fin D.n | (i : ℕ) < D.k} := by
    ext i; exact D.supp i
  rw [hset, ← LocDataPt.P, ← D.map_p, ← hp] at h2
  have := h𝔭.isPrime
  rw [← under_map_atPrime h𝔭p]
  exact h2

/-- **A4**: a non-member of `F_{a+1}` (inside `F_a`) is a non-member at every point above `𝔭`. -/
theorem not_mem_loc_ptL [Fact (HasPres A)] {a : ℕ} {x : A} (hx : x ∈ compFPt I 𝔭 ((a : ℚ) / d))
    (hx1 : x ∉ compFPt I 𝔭 (((a + 1 : ℕ) : ℚ) / d)) (q : Pt A) (h𝔭q : 𝔭 ≤ q.ker) :
    algebraMap A (Localization.AtPrime q.ker) x ∉ cRF I q.ker (((a + 1 : ℕ) : ℚ) / d) := by
  intro hq
  have hchart := hchart_of_dim hI l hl hmax h𝔭 hchartn
  have hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀ :=
    fun p h => h𝔭.mem_ptL hI l hl hchart hmax p h
  obtain ⟨C, -, -⟩ := h𝔭.exists_chartCoverPtL hI hmax l hl dim hchartn
  obtain ⟨k, hk⟩ := C.cover q h𝔭q
  rw [← (C.D k).RFB_map_of_mem_L q hk (hZ q h𝔭q).2] at hq
  obtain ⟨y, hy, hyx⟩ := (C.D k).exists_of_mem_map q hk _ hq
  obtain ⟨N, hN⟩ := C.global_of_RFB_pt hI l hl hchart hZ k hyx
  have hu : (C.D k).g ^ N * y ∉ 𝔭 := fun h =>
    (Ideal.IsPrime.mem_or_mem inferInstance (h𝔭q h)).elim
      (fun h' => hk (Ideal.IsPrime.mem_of_pow_mem inferInstance N h')) hy
  apply hx1
  rw [mem_compFPt]
  intro p h𝔭p
  obtain ⟨n, c, e, w, hc, he, hwe, hcRF, hP⟩ := h𝔭.exists_chart_ptL hI l hl hmax hchartn hd hw p h𝔭p
  have hQ : QuotSeqCond (Localization.AtPrime p.ker) := quotSeqCond_of_finiteType polyBar p.ker.primeCompl
  have hux := mem_compFPt.1 hN p h𝔭p
  have hxp := mem_compFPt.1 hx p h𝔭p
  rw [hcRF] at hux hxp ⊢
  refine mem_RF_stable c hc he hd hwe hQ (Pt.dec_local p) (a + 1) _ fun hn => ?_
  have hu0 : algebraMap A (Localization.AtPrime p.ker) ((C.D k).g ^ N * y) ∈
      c.RF e (((0 : ℕ) : ℚ) / d) := by
    rw [Nat.cast_zero, zero_div, c.RF_of_nonpos he le_rfl]; trivial
  have hu1 : algebraMap A (Localization.AtPrime p.ker) ((C.D k).g ^ N * y) ∉
      c.RF e (((0 + 1 : ℕ) : ℚ) / d) := by
    rw [zero_add, Nat.cast_one]; exact fun h => hu (hP _ h)
  refine RF_mul_not_mem_dec c hc he hd hwe hQ (Pt.dec_local p) hu0 hu1 hxp hn ?_
  rw [← map_mul, mul_assoc, zero_add]
  exact hux

/-- **A5: the graded ring of the filtration is a domain**, at one explicit point. -/
theorem compFPt_mul_not_mem_ptL [hpA : Fact (HasPres A)] {a b : ℕ} {x y : A}
    (hx : x ∈ compFPt I 𝔭 ((a : ℚ) / d)) (hx1 : x ∉ compFPt I 𝔭 (((a + 1 : ℕ) : ℚ) / d))
    (hy : y ∈ compFPt I 𝔭 ((b : ℚ) / d)) (hy1 : y ∉ compFPt I 𝔭 (((b + 1 : ℕ) : ℚ) / d)) :
    x * y ∉ compFPt I 𝔭 (((a + b + 1 : ℕ) : ℚ) / d) := by
  intro hxy
  have := h𝔭.isPrime
  obtain ⟨G, hG, -⟩ := h𝔭.gens
  obtain ⟨q, hq⟩ := HasPres.exists_pt hpA.out G fun h =>
    (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 (hG ▸ h))
  rw [← hG] at hq
  obtain ⟨n, c, e, w, hc, he, hwe, hcRF, -⟩ := h𝔭.exists_chart_ptL hI l hl hmax hchartn hd hw q hq
  have hQ : QuotSeqCond (Localization.AtPrime q.ker) := quotSeqCond_of_finiteType polyBar q.ker.primeCompl
  have hx1q := h𝔭.not_mem_loc_ptL hI l hl hmax hchartn hd hw hx hx1 q hq
  have hy1q := h𝔭.not_mem_loc_ptL hI l hl hmax hchartn hd hw hy hy1 q hq
  have hxq := mem_compFPt.1 hx q hq
  have hyq := mem_compFPt.1 hy q hq
  have hxyq := mem_compFPt.1 hxy q hq
  rw [hcRF] at hx1q hy1q hxq hyq hxyq
  rw [map_mul] at hxyq
  exact RF_mul_not_mem_dec c hc he hd hwe hQ (Pt.dec_local q) hxq hx1q hyq hy1q hxyq

omit [Algebra.FiniteType ℚ A] in
/-- `1 ∉ F_1`. -/
theorem one_not_mem_compFPt_ptL [hpA : Fact (HasPres A)] : (1 : A) ∉ compFPt I 𝔭 (1 / d) := by
  intro h1
  have := h𝔭.isPrime
  obtain ⟨G, hG, -⟩ := h𝔭.gens
  obtain ⟨q, hq⟩ := HasPres.exists_pt hpA.out G fun h =>
    (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 (hG ▸ h))
  rw [← hG] at hq
  obtain ⟨n, c, e, w, -, -, -, hcRF, hP⟩ := h𝔭.exists_chart_ptL hI l hl hmax hchartn hd hw q hq
  have h := mem_compFPt.1 h1 q hq
  rw [hcRF] at h
  exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 (hP 1 h))

end LocusComp

variable [IsNoetherianRing A]

omit [Algebra.FiniteType ℚ A] in
/-- `compFil_F_nonpos` by `cRF_of_nonpos_gen` (no `LocusComp.mem`, no `cRF_eq`). -/
lemma compFil_F_nonpos_gen {j : ℤ} (hj : j ≤ 0) : (compFil hI hmax h𝔭 d).F j = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [compFil_F, mem_compFPt]
  intro p _
  rw [cRF_of_nonpos_gen I p.ker (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hj)
    (Nat.cast_nonneg d))]
  trivial

namespace LocusComp

include hI l hl hmax h𝔭 hchartn hd hw

/-- A5 in the indexing of `Constructive.rees_s_dyn` (`F_j` of `compFil`). -/
theorem compFil_gr_ptL [Fact (HasPres A)] (a b : ℕ) (x y : A)
    (hx : x ∈ (compFil hI hmax h𝔭 d).F a) (hx1 : x ∉ (compFil hI hmax h𝔭 d).F (a + 1))
    (hy : y ∈ (compFil hI hmax h𝔭 d).F b) (hy1 : y ∉ (compFil hI hmax h𝔭 d).F (b + 1))
    (hxy : x * y ∈ (compFil hI hmax h𝔭 d).F ((a + b : ℕ) + 1)) : False := by
  have hF : ∀ m : ℕ, (compFil hI hmax h𝔭 d).F (m : ℤ) = compFPt I 𝔭 ((m : ℚ) / d) := fun m => by
    rw [compFil_F, Int.cast_natCast]
  have e1 : ((a : ℤ) + 1) = ((a + 1 : ℕ) : ℤ) := by push_cast; rfl
  have e2 : ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) := by push_cast; rfl
  have e3 : (((a + b : ℕ) : ℤ) + 1) = ((a + b + 1 : ℕ) : ℤ) := by push_cast; rfl
  rw [hF] at hx hy
  rw [e1, hF] at hx1
  rw [e2, hF] at hy1
  rw [e3, hF] at hxy
  exact h𝔭.compFPt_mul_not_mem_ptL hI l hl hmax hchartn hd hw hx hx1 hy hy1 hxy

/-- **A7: the exceptional divisor `(s)` of the Rees algebra is prime**, choice-free (twin of
`rees_s_prime`): `Constructive.rees_s_dyn` with the decision `compFPt_dec_ptL` and `Q := False`
(`compFPt_mul_not_mem_ptL`). -/
theorem rees_s_isPrime_ptL [Fact (HasPres A)] :
    (Ideal.span {reesS (compFil hI hmax h𝔭 d)
      (fun _j hj => compFil_F_nonpos_gen hI hmax h𝔭 hj)}).IsPrime := by
  set Φ := compFil hI hmax h𝔭 d
  have hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤ := fun _j hj => compFil_F_nonpos_gen hI hmax h𝔭 hj
  have hdec : ∀ (j : ℤ) (x : A), x ∈ Φ.F j ∨ x ∉ Φ.F j := fun j x => by
    rw [compFil_F]; exact h𝔭.compFPt_dec_ptL hI l hl hmax hchartn _ x
  refine ⟨fun htop => ?_, fun {p q} hpq => ?_⟩
  · have h1mem : (1 : ReesAlg Φ) ∈ Ideal.span {reesS Φ hneg} := by rw [htop]; trivial
    have := (mem_span_s_iff Φ hneg 1).1 h1mem 0
    rw [show ((1 : ReesAlg Φ) : A[T;T⁻¹]) = 1 from rfl, coeff_one_laurent, ite_eq_left rfl,
      zero_add, compFil_F, Int.cast_one] at this
    exact h𝔭.one_not_mem_compFPt_ptL hI l hl hmax hchartn hd hw this
  rw [mem_span_s_iff] at hpq ⊢
  rw [mem_span_s_iff]
  rcases rees_s_dyn Φ.F Φ.mul_le hneg hdec (Q := False)
      (fun a b x y => h𝔭.compFil_gr_ptL hI l hl hmax hchartn hd hw a b x y)
      p.2 q.2 hpq with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact h.elim

end LocusComp

end BezoutCounterexample.Principalization
