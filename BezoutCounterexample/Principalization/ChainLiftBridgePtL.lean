import BezoutCounterexample.Principalization.ChainLiftBridgeFinal
import BezoutCounterexample.Principalization.ChainLiftBridgeTower
import BezoutCounterexample.Principalization.ChartCoverPtLGlue
import BezoutCounterexample.Principalization.ChainLiftReesLocalPt

/-!
# The chain-lifting bridge over a `ChartCoverPtL` (leaf)

The chart lemmas of the torsor step (BridgeHead, BridgeMain, BridgeFinal, BridgeTower) for local
data at explicit points (`LocDataPt`) and covers at explicit points (`ChartCoverPtL`), same proofs:

* `exists_numerators_pt`, `chart_partition_pt`, `head_support_pt`, `LocDataPt.n_eq`,
  `LocDataPt.n_le` (only the chart data of `D` is used);
* `lid_A_ptL`, `hid_A_ptL` (via `ChartCoverPtL.global_of_RFB_pt`, `ChartCoverPtL.mem_compFPt_iff`
  and `hid_B_pt`; inputs `l hl hchart`);
* `lid_gen_L`, `hid_gen_L`, `chart_heads_L` (`l hl hchart` from `LocusComp.gensI`/`chartn`).

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive IsLocalization
open scoped Matrix

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Chart

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal]

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- **Head numerators**: a common power `gˢ` clears the chart functions. -/
theorem exists_numerators_pt {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocDataPt I v₀ 𝔪) :
    ∃ (s : ℕ) (a : Fin D.n → A), ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s = algebraMap A D.B (a i) := by
  obtain ⟨⟨b, hb⟩, hint⟩ := exist_integer_multiples_of_finite (Submonoid.powers D.g) D.cB.x
  obtain ⟨s, rfl⟩ := hb
  obtain ⟨a, ha⟩ := Constructive.finite_choice_dep fun i => (hint i : ∃ a : A, _ = _)
  refine ⟨s, a, fun i => ?_⟩
  rw [ha i, Algebra.smul_def, map_pow, mul_comm]

/-- **One chart: integer chart data of the `τ`-coordinates and the partition in `A`.** -/
theorem chart_partition_pt {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ))
    (e : Quo (GQ G) ≃+* A) (D : LocDataPt I v₀ 𝔪) (hD : D.n = n) {kc : ℕ} (hk : kc ≤ n)
    (hn : 0 < n) :
    ∃ (s : ℕ) (a : Fin n → A) (ã : Fin kc → MvPolynomial (Fin (m + n)) ℤ) (Dq : Fin kc → ℕ)
      (T : RowIdx (m + n) (n - kc) → ChartData G) (M : ℕ) (β : RowIdx (m + n) (n - kc) → A)
      (ω : Fin kc → A),
      (∀ q, 0 < Dq q ∧ e (Ideal.Quotient.mk _ (toQ (ã q))) = (Dq q : A) * a (headIdx hk q)) ∧
      (∀ τ, (T τ).x = yZ hk ã τ) ∧
      (∀ j : Fin D.n, D.cB.x j * algebraMap A D.B D.g ^ s =
        algebraMap A D.B (a (Fin.cast hD j))) ∧
      D.g ^ M = ∑ τ, β τ * e (Ideal.Quotient.mk _ (toQ (T τ).c)) + ∑ q, ω q * a (headIdx hk q) := by
  subst hD
  -- the chart ring as an algebra over the presented ring
  letI alg : Algebra (Quo (GQ G)) D.B := ((algebraMap A D.B).comp e.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ (Quo (GQ G)) D.B := IsScalarTower.of_algebraMap_eq fun q => by
    have := RingHom.ext_rat (algebraMap ℚ D.B)
      ((algebraMap (Quo (GQ G)) D.B).comp (algebraMap ℚ (Quo (GQ G))))
    exact congrArg (fun f : ℚ →+* D.B => f q) this
  set Mo : Submonoid (Quo (GQ G)) := D.N.map e.symm
  haveI : IsLocalization Mo D.B := isLocalization_of_base_ringEquiv D.N D.B e.symm
  have htoS : ∀ p, toS (S := D.B) (GQ G) p = algebraMap A D.B (e (Ideal.Quotient.mk _ p)) :=
    fun p => rfl
  set c := D.cB
  -- numerators and lifts
  obtain ⟨s, a, ha⟩ := exists_numerators_pt D
  have hsurj : ∀ x : A, ∃ p, e (Ideal.Quotient.mk _ p) = x := fun x => by
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨p, rfl⟩
  obtain ⟨pa, hpa⟩ := Constructive.finite_choice_dep fun j => hsurj (a j)
  obtain ⟨pg, hpg⟩ := hsurj D.g
  obtain ⟨D₀, ã, hD₀, hã⟩ := exists_int_mul_fin (σ := Fin (m + D.n)) fun q : Fin kc => pa (headIdx hk q)
  -- the coordinate families
  have hyQ : ∀ τ, (fun j => toQ (yZ hk ã τ j)) = yTau hk pa (fun _ => (D₀ : ℚ)) τ := by
    intro τ; funext j
    by_cases h : (j : ℕ) < kc
    · simp only [yZ, yTau, h, dite_true, hã, ← map_natCast C]
      congr 2
    · simp [yZ, yTau, h]
  obtain ⟨T, hT⟩ := Constructive.finite_choice_dep fun τ => chartData_of_chart G Mo c hn (yZ hk ã τ)
  obtain ⟨DT, hT⟩ := Constructive.finite_choice_dep hT
  obtain ⟨lam, hT⟩ := Constructive.finite_choice_dep hT
  have hTx := fun τ => (hT τ).1
  have hDT := fun τ => (hT τ).2.1
  have hlam := fun τ => (hT τ).2.2.1
  have hTc := fun τ => (hT τ).2.2.2
  -- the partition in the chart ring
  have hgS : toS (S := D.B) (GQ G) pg = algebraMap A D.B D.g := by rw [htoS, hpg]
  obtain ⟨u, hu⟩ : ∃ u : D.B, u * toS (GQ G) pg ^ s = 1 := by
    rw [hgS]
    obtain ⟨v, hv⟩ := ((IsLocalization.Away.algebraMap_isUnit (S := D.B) D.g).pow s).exists_left_inv
    exact ⟨v, hv⟩
  have hp : ∀ j, c.x j * toS (S := D.B) (GQ G) pg ^ s = toS (GQ G) (pa j) := fun j => by
    rw [hgS, htoS, hpa, ← ha j]
  obtain ⟨r, z, hz, hsum⟩ := partition_chart (GQ G) c hk pg s u hu pa hp fun _ => (D₀ : ℚ)
  -- `det J_τ = c_τ / (D_τ λ_τ)`
  set cA : RowIdx (m + D.n) (D.n - kc) → A := fun τ => e (Ideal.Quotient.mk _ (toQ (T τ).c))
  have hunit : ∀ τ, IsUnit ((DT τ : D.B) * toS (GQ G) (lam τ)) := fun τ => by
    refine IsUnit.mul ?_ ?_
    · have : IsUnit ((DT τ : ℚ)) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (hDT τ).ne')
      simpa using this.map (algebraMap ℚ D.B)
    · exact IsLocalization.map_units (M := Mo) D.B ⟨_, hlam τ⟩
  obtain ⟨ν, hν⟩ := Constructive.finite_choice_dep fun τ => (hunit τ).exists_left_inv
  have hdet : ∀ τ, (Jm (GQ G) c (yTau hk pa (fun _ => (D₀ : ℚ)) τ)).det =
      ν τ * algebraMap A D.B (cA τ) := fun τ => by
    rw [← htoS, hTc τ, hyQ τ, ← mul_assoc, hν τ, one_mul]
  -- the head part `z = Σ w_q x_q`
  rw [Ideal.mem_span_range_iff_exists_fun] at hz
  obtain ⟨w, rfl⟩ := hz
  -- clear the denominators in `D.B = A[1/g]`
  obtain ⟨⟨b, hb⟩, hint⟩ := exist_integer_multiples_of_finite (Submonoid.powers D.g)
    (Sum.elim (fun τ => r τ * ν τ) w : RowIdx (m + D.n) (D.n - kc) ⊕ Fin kc → D.B)
  obtain ⟨j₀, rfl⟩ := hb
  obtain ⟨ρ, hρ⟩ := Constructive.finite_choice_dep fun i => (hint i : ∃ a : A, _ = _)
  have hρτ : ∀ τ, algebraMap A D.B (ρ (Sum.inl τ)) = algebraMap A D.B D.g ^ j₀ * (r τ * ν τ) :=
    fun τ => by rw [hρ, Algebra.smul_def, map_pow]; rfl
  have hρq : ∀ q, algebraMap A D.B (ρ (Sum.inr q)) = algebraMap A D.B D.g ^ j₀ * w q :=
    fun q => by rw [hρ, Algebra.smul_def, map_pow]; rfl
  have hB : algebraMap A D.B (∑ τ, D.g ^ s * ρ (Sum.inl τ) * cA τ) = algebraMap A D.B
      ((D₀ : A) ^ kc * D.g ^ (j₀ + s + s * kc) + ∑ q, ρ (Sum.inr q) * a (headIdx hk q)) := by
    have h1 := congrArg (fun y => algebraMap A D.B D.g ^ (j₀ + s) * y) hsum
    rw [map_sum, map_add, map_sum]
    have eL : ∀ τ, algebraMap A D.B (D.g ^ s * ρ (Sum.inl τ) * cA τ) =
        algebraMap A D.B D.g ^ (j₀ + s) * (r τ * (Jm (GQ G) c (yTau hk pa (fun _ => (D₀ : ℚ)) τ)).det) :=
      fun τ => by rw [hdet, map_mul, map_mul, map_pow, hρτ, pow_add]; ring
    have eR : ∀ q, algebraMap A D.B (ρ (Sum.inr q) * a (headIdx hk q)) =
        algebraMap A D.B D.g ^ (j₀ + s) * (w q * c.x (headIdx hk q)) := fun q => by
      rw [map_mul, hρq, ← ha (headIdx hk q), pow_add]; ring
    simp only [eL, eR, ← Finset.mul_sum]
    rw [h1, mul_add]
    congr 1
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul, map_mul,
      map_pow, map_pow, map_natCast, ← map_natCast (algebraMap ℚ D.B), pow_add, pow_add, hgS]
    simp only [map_natCast]
    ring
  obtain ⟨⟨_, t, rfl⟩, ht⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers D.g) D.B).1 hB
  -- divide by `D₀^kc`
  set κ : A := algebraMap ℚ A ((D₀ : ℚ) ^ kc)⁻¹
  have hκ : κ * (D₀ : A) ^ kc = 1 := by
    rw [← map_natCast (algebraMap ℚ A), ← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _
      (Nat.cast_ne_zero.2 hD₀.ne')), map_one]
  refine ⟨s, a, ã, fun _ => D₀, T, t + (j₀ + s + s * kc),
    fun τ => κ * D.g ^ t * (D.g ^ s * ρ (Sum.inl τ)), fun q => -(κ * D.g ^ t * ρ (Sum.inr q)),
    fun q => ⟨hD₀, ?_⟩, hTx, fun j => by simpa using ha j, ?_⟩
  · rw [show e (Ideal.Quotient.mk _ (toQ (ã q))) = e (Ideal.Quotient.mk _ ((D₀ : MvPolynomial _ ℚ) *
      pa (headIdx hk q))) by rw [hã q], map_mul, map_mul, map_natCast, map_natCast, hpa]
  · have ht' : D.g ^ t * ∑ τ, D.g ^ s * ρ (Sum.inl τ) * cA τ = D.g ^ t * ((D₀ : A) ^ kc *
        D.g ^ (j₀ + s + s * kc) + ∑ q, ρ (Sum.inr q) * a (headIdx hk q)) := ht
    have : D.g ^ (t + (j₀ + s + s * kc)) = κ * (D₀ : A) ^ kc * D.g ^ (t + (j₀ + s + s * kc)) := by
      rw [hκ, one_mul]
    rw [this, pow_add]
    have e2 : κ * (D₀ : A) ^ kc * (D.g ^ t * D.g ^ (j₀ + s + s * kc)) =
        κ * (D.g ^ t * ((D₀ : A) ^ kc * D.g ^ (j₀ + s + s * kc) +
          ∑ q, ρ (Sum.inr q) * a (headIdx hk q))) -
        κ * D.g ^ t * ∑ q, ρ (Sum.inr q) * a (headIdx hk q) := by ring
    rw [e2, ← ht']
    simp only [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun τ _ => by simp only [cA]; ring
    · exact Finset.sum_congr rfl fun q _ => by ring


omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- **The head of a chart is given by the invariant**: `eᵢ ≠ 0 ↔ i < #{j : v₀ j ≠ 0}`. -/
theorem head_support_pt {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocDataPt I v₀ 𝔪) {n : ℕ} (hdn : D.n = n) :
    ∀ i : Fin D.n, D.ek i ≠ 0 ↔
      (Fin.cast hdn i : ℕ) < (Finset.univ.filter fun j : Fin n => v₀ j ≠ 0).card := by
  subst hdn
  have hek : ∀ j : Fin D.n, D.ek j = v₀ j := fun j => by
    have := congrFun D.hv j; rwa [ext0_apply] at this
  have hset : (Finset.univ.filter fun j : Fin D.n => v₀ j ≠ 0) =
      Finset.univ.filter fun j : Fin D.n => (j : ℕ) < D.k := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← hek, D.supp]
  intro i
  rw [hset, Fin.card_filter_val_lt, D.supp]
  simp [lt_min_iff, i.2]

/-- **All charts of HM's domain have the same size.** Both charts are transported to the
fraction field `A_(0)`: `M ≤ (0)ᶜ` by `ctrl` at the prime `(0)`, since `g ≠ 0`. No maximal
ideal is needed (S1). -/
theorem LocDataPt.n_eq {𝔪₁ 𝔪₂ : Ideal A} [𝔪₁.IsMaximal] [𝔪₂.IsMaximal] (D₁ : LocDataPt I v₀ 𝔪₁)
    (D₂ : LocDataPt I v₀ 𝔪₂) : D₁.n = D₂.n := by
  have hg1 : D₁.g ∉ (⊥ : Ideal A) := fun h => D₁.hg ((Submodule.mem_bot A).1 h ▸ zero_mem _)
  have hg2 : D₂.g ∉ (⊥ : Ideal A) := fun h => D₂.hg ((Submodule.mem_bot A).1 h ▸ zero_mem _)
  exact Chart.card_eq (Loc.transport (D₁.ctrl ⊥ hg1) D₁.ck) (Loc.transport (D₂.ctrl ⊥ hg2) D₂.ck)

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- **The chart dimension is at most the number of variables of a presentation.** -/
theorem LocDataPt.n_le {N : ℕ} (G₀ : List (MvPolynomial (Fin N) ℚ)) (e : Quo G₀ ≃+* A)
    {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocDataPt I v₀ 𝔪) : D.n ≤ N := by
  set S := Localization.AtPrime 𝔪
  let alg : Algebra (Quo G₀) S := ((algebraMap A S).comp e.toRingHom).toAlgebra
  have : IsScalarTower ℚ (Quo G₀) S := IsScalarTower.of_algebraMap_eq fun q => by
    have := RingHom.ext_rat (algebraMap ℚ S) ((algebraMap (Quo G₀) S).comp (algebraMap ℚ (Quo G₀)))
    exact congrArg (fun f : ℚ →+* S => f q) this
  have htoS : ∀ p, toS (S := S) G₀ p = algebraMap A S (e (Ideal.Quotient.mk _ p)) := fun p => rfl
  have hpre : ∀ a : A, ∃ p, e (Ideal.Quotient.mk (lspan G₀) p) = a := fun a => by
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (e.symm a)
    exact ⟨p, by rw [hp, RingEquiv.apply_symm_apply]⟩
  refine chart_card_le G₀ (fun x => ?_) (Loc.transport (D.ctrl 𝔪 D.hg) D.ck)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj 𝔪.primeCompl x
  obtain ⟨p, hp⟩ := hpre a
  obtain ⟨q, hq⟩ := hpre b
  obtain ⟨w, hw⟩ := IsLocalization.map_units S b
  refine ⟨p, q, ↑w⁻¹, ?_, ?_⟩
  · rw [htoS, hq, ← hw, Units.inv_mul]
  · rw [htoS, htoS, hp, hq]; exact hab

end Chart

section PtL

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} {𝔭 : Ideal A} (Cp : ChartCoverPtL I v₀ 𝔭)

include hI in
/-- **lid in `A`, over a `ChartCoverPtL`**: `g^N aₕ ∈ F_{eₕ}` for a head numerator `aₕ`. -/
theorem lid_A_ptL [Fact (HasPres A)] (l : List A) (hl : I = lspan l)
    (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
    (hZp : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀)
    (k : Fin Cp.n) (s : ℕ) (a : Fin (Cp.D k).n → A)
    (ha : ∀ i, (Cp.D k).cB.x i * algebraMap A (Cp.D k).B (Cp.D k).g ^ s =
      algebraMap A (Cp.D k).B (a i)) (h : Fin (Cp.D k).n) (hne : (Cp.D k).ek h ≠ 0) :
    ∃ N : ℕ, (Cp.D k).g ^ N * a h ∈ compFPt I 𝔭 ((Cp.D k).ek h) := by
  apply Cp.global_of_RFB_pt hI l hl hchart hZp k
  rw [← ha h]
  exact Ideal.mul_mem_right _ _ ((Cp.D k).cB.x_mem_RF (Cp.D k).ek h hne)

include hI in
/-- **hid in `A`, over a `ChartCoverPtL`**: an element of `F_t` is, up to a power of `g`, a
combination of head monomials of weighted degree `≥ t`. -/
theorem hid_A_ptL [Fact (HasPres A)] (k : Fin Cp.n) (s : ℕ) (a : Fin (Cp.D k).n → A)
    (ha : ∀ i, (Cp.D k).cB.x i * algebraMap A (Cp.D k).B (Cp.D k).g ^ s =
      algebraMap A (Cp.D k).B (a i)) {t : ℚ} {z : A} (hz : z ∈ compFPt I 𝔭 t) :
    ∃ (S K : ℕ) (b : Fin K → A) (α : Fin K → (Fin (Cp.D k).n →₀ ℕ)),
      (∀ j l, (Cp.D k).ek l = 0 → α j l = 0) ∧ (∀ j, t ≤ lam (Cp.D k).ek (α j)) ∧
      (Cp.D k).g ^ S * z = ∑ j, b j * ∏ l, a l ^ α j l :=
  hid_B_pt (Cp.D k) s a ha (Cp.mem_RFB_of_mem hI k hz)

end PtL

section HM

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (d : ℕ) (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hd hw in
/-- **lid over the torsor generators**: `g^N aₕ = Σ_γ c_γ gen^γ`, `γ·deg ≥ wₕ`, `γ ≠ 0`. -/
theorem lid_gen_L [Constructive.Enum A] [Fact (Constructive.HasPres A)] (C : ChartCoverPtL I v₀ 𝔭) (k : Fin C.n) (s : ℕ) (a : Fin (C.D k).n → A)
    (ha : ∀ i, (C.D k).cB.x i * algebraMap A (C.D k).B (C.D k).g ^ s =
      algebraMap A (C.D k).B (a i)) (π : A) (h : Fin (C.D k).n) (hne : (C.D k).ek h ≠ 0)
    (wh : ℕ) (hwh : (wh : ℚ) = d * v₀ h) :
    ∃ (N : ℕ) (Γ : Finset (Fin (nGen hI hmax h𝔭 d + 1) → ℕ))
      (c : (Fin (nGen hI hmax h𝔭 d + 1) → ℕ) → A),
      (∀ γ ∈ Γ, (wh : ℤ) ≤ ∑ i, (γ i : ℤ) * genDeg hI hmax h𝔭 d i ∧ ∑ i, γ i ≠ 0) ∧
      (C.D k).g ^ N * a h = ∑ γ ∈ Γ, c γ * ∏ i, genCoeff hI hmax h𝔭 d π i ^ γ i := by
  have hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀ := fun p h => h𝔭.memP hI hmax p h
  obtain ⟨l, hl⟩ := h𝔭.gensI
  obtain ⟨dim, hchartn⟩ := h𝔭.chartn
  have hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n) :=
    fun p => (hchartn p).imp fun _ hf => ⟨hf.1, dim, hf.2⟩
  obtain ⟨N, hN⟩ := lid_A_ptL hI C l hl hchart hZ k s a ha h hne
  have hek : (C.D k).ek h = v₀ h := by
    have := congrFun (C.D k).hv h
    rwa [ext0_apply] at this
  have hF : compFPt I 𝔭 ((C.D k).ek h) = (compFil hI hmax h𝔭 d).F wh := by
    rw [compFil_F, hek]
    congr 1
    push_cast
    rw [hwh]
    field_simp
  rw [hF] at hN
  have hpos : 0 < v₀ h := by
    rw [← hek]
    exact lt_of_le_of_ne ((C.D k).inv.nonneg h) (Ne.symm hne)
  have hwh1 : (1 : ℤ) ≤ wh := by
    have : (0 : ℚ) < wh := by rw [hwh]; positivity
    exact_mod_cast this
  have hRI := mem_RI_of_mem_F hI hmax h𝔭 d hd hw (genCoeff hI hmax h𝔭 d π) (genDeg hI hmax h𝔭 d)
    (gen_covers hI hmax h𝔭 d π) hwh1 hN
  obtain ⟨Γ, c, hΓ, hz⟩ := exists_sum_of_mem_RI _ _ hRI
  exact ⟨N, Γ, c, hΓ, hz⟩

include hw in
/-- **hid over the torsor generators**: `g^S genᵢ = Σ_j b_j a^{α_j}`, `α_j` on the head, of
weighted degree `≥ degᵢ`. -/
theorem hid_gen_L [Constructive.Enum A] [Fact (Constructive.HasPres A)] (C : ChartCoverPtL I v₀ 𝔭) (k : Fin C.n) (s : ℕ) (a : Fin (C.D k).n → A)
    (ha : ∀ i, (C.D k).cB.x i * algebraMap A (C.D k).B (C.D k).g ^ s =
      algebraMap A (C.D k).B (a i)) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
    (hd : 0 < d) (w : Fin (C.D k).n → ℕ) (hwl : ∀ l, (w l : ℚ) = d * v₀ l)
    (i : Fin (nGen hI hmax h𝔭 d + 1)) :
    ∃ (S K : ℕ) (b : Fin K → A) (α : Fin K → (Fin (C.D k).n →₀ ℕ)),
      (∀ j (l : Fin (C.D k).n), (C.D k).ek l = 0 → α j l = 0) ∧
      (∀ j, genDeg hI hmax h𝔭 d i ≤ ∑ l, (w l : ℤ) * α j l) ∧
      (C.D k).g ^ S * genCoeff hI hmax h𝔭 d π i = ∑ j, b j * ∏ l, a l ^ α j l := by
  have hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀ := fun p h => h𝔭.memP hI hmax p h
  have hmem := genCoeff_mem hI hmax h𝔭 d hπ i
  rw [compFil_F] at hmem
  obtain ⟨S, K, b, α, hα0, hαt, hid⟩ := hid_A_ptL hI C k s a ha hmem
  refine ⟨S, K, b, α, hα0, fun j => ?_, hid⟩
  · have hek : ∀ l, (C.D k).ek l = v₀ l := fun l => by
      have := congrFun (C.D k).hv l
      rwa [ext0_apply] at this
    have h1 := hαt j
    rw [lam] at h1
    have h2 : ((genDeg hI hmax h𝔭 d i : ℤ) : ℚ) ≤ ((∑ l, (w l : ℤ) * α j l : ℤ) : ℚ) := by
      push_cast
      have hdq : (0 : ℚ) < d := by exact_mod_cast hd
      have : ∑ l, (w l : ℚ) * (α j l : ℚ) = d * ∑ l, (α j l : ℚ) * (C.D k).ek l := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [hwl, hek]; ring
      rw [this]
      calc (genDeg hI hmax h𝔭 d i : ℚ) = d * ((genDeg hI hmax h𝔭 d i : ℚ) / d) := by
            field_simp
        _ ≤ d * ∑ l, (α j l : ℚ) * (C.D k).ek l := mul_le_mul_of_nonneg_left h1 hdq.le
    exact_mod_cast h2

set_option maxHeartbeats 2000000 in
include hd hw in
/-- **The head data of one chart**, for every chart data with coordinates `yZ`, after scaling
the multiplier by `K g_k^ℓ`. -/
theorem chart_heads_L [Fact (Constructive.HasPres A)] [Constructive.Enum A] (C : ChartCoverPtL I v₀ 𝔭) (k : Fin C.n) {m n kc : ℕ}
    (G : List (MvPolynomial (Fin (m + n)) ℤ)) (e : Quo (GQ G) ≃+* A)
    (hdk : (C.D k).n = n) (hkn : kc ≤ n)
    (hhead : ∀ i : Fin (C.D k).n, (C.D k).ek i ≠ 0 ↔ (Fin.cast hdk i : ℕ) < kc) {π : A}
    (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1) (s : ℕ) (a : Fin n → A)
    (hnum : ∀ j : Fin (C.D k).n, (C.D k).cB.x j * algebraMap A (C.D k).B (C.D k).g ^ s =
      algebraMap A (C.D k).B (a (Fin.cast hdk j)))
    (ã : Fin kc → MvPolynomial (Fin (m + n)) ℤ) (Dq : Fin kc → ℕ) (hDq : ∀ q, 0 < Dq q)
    (hã : ∀ q, toA G e (ã q) = (Dq q : A) * a (headIdx hkn q))
    (gZ : Fin (nGen hI hmax h𝔭 d + 1) → MvPolynomial (Fin (m + n)) ℤ) (Dg₀ : ℕ) (hDg₀ : 0 < Dg₀)
    (hgZ : ∀ i, toA G e (gZ i) = (Dg₀ : A) * genCoeff hI hmax h𝔭 d π i)
    (gk : MvPolynomial (Fin (m + n)) ℤ) (Dgk : ℕ) (hDgk : 0 < Dgk)
    (hgk : toA G e gk = (Dgk : A) * (C.D k).g) :
    ∃ (K ℓ : ℕ), 0 < K ∧ 1 ≤ ℓ ∧
      (∀ q, ∃ N, (C.D k).g ^ N * a (headIdx hkn q) ∈
        Ideal.span (Set.range (genCoeff hI hmax h𝔭 d π))) ∧
      ∀ (T : ChartData G) (τ : RowIdx (m + n) (n - kc)), T.x = yZ hkn ã τ →
        Nonempty (ChartHead (T.scale ((K : MvPolynomial (Fin (m + n)) ℤ) * gk ^ ℓ)) gZ
          (fun i => (genDeg hI hmax h𝔭 d i).toNat) kc) := by
  haveI : Fact (Constructive.HasPres A) := ⟨⟨m + n, GQ G, ⟨e⟩⟩⟩
  subst hdk
  have hcast : ∀ j : Fin (C.D k).n, Fin.cast rfl j = j := fun j => rfl
  simp only [hcast] at hnum hhead
  have htail : ∀ t : Fin ((C.D k).n - kc), (C.D k).ek (tailIdx hkn t) = 0 := fun t => by
    by_contra h
    have := (hhead _).1 h
    simp [tailIdx] at this
  -- weights
  -- (unique choice: `wᵢ = ⌊d v₀ᵢ⌋₊`)
  obtain ⟨wv, hwv⟩ : ∃ wv : ℕ → ℕ, ∀ i, (wv i : ℚ) = d * v₀ i :=
    ⟨fun i => ⌊(d : ℚ) * v₀ i⌋₊, fun i => by
      obtain ⟨w, hw⟩ := hw i; show ((⌊(d : ℚ) * v₀ i⌋₊ : ℕ) : ℚ) = _; rw [← hw, Nat.floor_natCast]⟩
  have hpos : ∀ q : Fin kc, 0 < v₀ (headIdx hkn q) := fun q => by
    have hek : (C.D k).ek (headIdx hkn q) = v₀ (headIdx hkn q) := by
      have := congrFun (C.D k).hv (headIdx hkn q); rwa [ext0_apply] at this
    rw [← hek]
    exact lt_of_le_of_ne ((C.D k).inv.nonneg _) (Ne.symm ((hhead _).2 q.2))
  -- lid data
  have hlid := fun q : Fin kc => lid_gen_L hI hmax h𝔭 d hd (fun i => ⟨wv i, hwv i⟩) C k s a hnum π
    (headIdx hkn q) ((hhead _).2 q.2) (wv (headIdx hkn q)) (hwv _)
  obtain ⟨N, hlid⟩ := finite_choice hlid
  obtain ⟨Γ, hlid⟩ := finite_choice hlid
  obtain ⟨cl, hlid⟩ := finite_choice hlid
  have hΓ := fun q => (hlid q).1
  have hlidA := fun q => (hlid q).2
  -- hid data
  have hhid := fun i : Fin (nGen hI hmax h𝔭 d + 1) => hid_gen_L hI hmax h𝔭 d
    (fun i => ⟨wv i, hwv i⟩) C k s a hnum hπ hd (fun l => wv l) (fun l => hwv l) i
  obtain ⟨S, hhid⟩ := finite_choice hhid
  obtain ⟨Kh, hhid⟩ := finite_choice hhid
  obtain ⟨b, hhid⟩ := finite_choice_dep hhid
  obtain ⟨α, hhid⟩ := finite_choice_dep hhid
  have hα0 := fun i => (hhid i).1
  have hαdeg := fun i => (hhid i).2.1
  have hhidA := fun i => (hhid i).2.2
  -- `κ`: inverses of positive integers in `A`
  have hinvA : ∀ D : ℕ, 0 < D → algebraMap ℚ A ((D : ℚ))⁻¹ * (D : A) = 1 := fun D hD => by
    rw [← map_natCast (algebraMap ℚ A), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hD.ne'),
      map_one]
  -- lid congruences
  have hlidP : ∀ q : Fin kc, ∃ (Kl : ℕ) (ql : Γ q → MvPolynomial (Fin (m + (C.D k).n)) ℤ),
      0 < Kl ∧ (Kl : MvPolynomial (Fin (m + (C.D k).n)) ℤ) * (gk ^ N q * ã q) -
        ∑ γ : Γ q, ql γ * ∏ i, gZ i ^ γ.1 i ∈ lspan G := fun q => by
    refine int_cong_of_A G e _ _ (fun γ : Γ q => ((Dgk : A) ^ N q * (Dq q : A)) * cl q γ *
      algebraMap ℚ A (((Dg₀ : ℚ) ^ ∑ i, γ.1 i))⁻¹) ?_
    rw [toA_mul, ← toAHom_apply, map_pow, toAHom_apply, hgk, hã q, mul_pow]
    have : (C.D k).g ^ N q * a (headIdx hkn q) = _ := hlidA q
    calc ((Dgk : A) ^ N q * (C.D k).g ^ N q) * ((Dq q : A) * a (headIdx hkn q))
        = ((Dgk : A) ^ N q * (Dq q : A)) * ((C.D k).g ^ N q * a (headIdx hkn q)) := by ring
      _ = _ := by
        rw [this, Finset.mul_sum, ← Finset.sum_coe_sort]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [← toAHom_apply, map_prod]
        simp only [map_pow, toAHom_apply, hgZ, mul_pow, Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum]
        have hκ := hinvA (Dg₀ ^ ∑ i, γ.1 i) (pow_pos hDg₀ _)
        push_cast at hκ
        linear_combination (-(↑Dgk ^ N q * ↑(Dq q) * cl q ↑γ *
          ∏ x, genCoeff hI hmax h𝔭 d π x ^ (γ.1 x) : A)) * hκ
  obtain ⟨Kl, hlidP⟩ := finite_choice hlidP
  obtain ⟨ql, hlidP⟩ := finite_choice_dep hlidP
  have hKl := fun q => (hlidP q).1
  replace hlidP := fun q => (hlidP q).2
  -- hid congruences
  have hhidP : ∀ i, ∃ (Kh' : ℕ) (qh : Fin (Kh i) → MvPolynomial (Fin (m + (C.D k).n)) ℤ),
      0 < Kh' ∧ (Kh' : MvPolynomial (Fin (m + (C.D k).n)) ℤ) * (gk ^ S i * gZ i) -
        ∑ j, qh j * ∏ q, ã q ^ α i j (headIdx hkn q) ∈ lspan G := fun i => by
    refine int_cong_of_A G e _ _ (fun j => ((Dgk : A) ^ S i * (Dg₀ : A)) * b i j *
      algebraMap ℚ A (∏ q, ((Dq q : ℚ) ^ α i j (headIdx hkn q)))⁻¹) ?_
    rw [toA_mul, ← toAHom_apply, map_pow, toAHom_apply, hgk, hgZ i, mul_pow]
    calc ((Dgk : A) ^ S i * (C.D k).g ^ S i) * ((Dg₀ : A) * genCoeff hI hmax h𝔭 d π i)
        = ((Dgk : A) ^ S i * (Dg₀ : A)) * ((C.D k).g ^ S i * genCoeff hI hmax h𝔭 d π i) := by ring
      _ = _ := by
        rw [hhidA i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hph : ∏ l, a l ^ α i j l = ∏ q, a (headIdx hkn q) ^ α i j (headIdx hkn q) :=
          prod_head hkn _ fun t => by
            rw [hα0 i j (tailIdx hkn t) (htail t), pow_zero]
        rw [hph, ← toAHom_apply, map_prod]
        simp only [map_pow, toAHom_apply, hã, mul_pow, Finset.prod_mul_distrib]
        have hκ : algebraMap ℚ A (∏ q, ((Dq q : ℚ) ^ α i j (headIdx hkn q)))⁻¹ *
            ∏ q, (Dq q : A) ^ α i j (headIdx hkn q) = 1 := by
          have e1 : ∏ q, (Dq q : A) ^ α i j (headIdx hkn q) =
              algebraMap ℚ A (∏ q, (Dq q : ℚ) ^ α i j (headIdx hkn q)) := by
            simp [map_prod, map_pow, map_natCast]
          rw [e1, ← map_mul, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun q _ =>
            pow_ne_zero _ (Nat.cast_ne_zero.2 (hDq q).ne')), map_one]
        linear_combination (-((Dgk : A) ^ S i * (Dg₀ : A) * b i j *
          ∏ q, a (headIdx hkn q) ^ α i j (headIdx hkn q))) * hκ
  obtain ⟨Kh', hhidP⟩ := finite_choice hhidP
  obtain ⟨qh, hhidP⟩ := finite_choice_dep hhidP
  have hKh' := fun i => (hhidP i).1
  replace hhidP := fun i => (hhidP i).2
  -- the constants
  set K : ℕ := (∏ q, Kl q) * ∏ i, Kh' i
  set ℓ : ℕ := 1 + ∑ q, N q + ∑ i, S i
  have hK : 0 < K := Nat.mul_pos (Finset.prod_pos fun q _ => hKl q)
    (Finset.prod_pos fun i _ => hKh' i)
  have hNℓ : ∀ q, N q ≤ ℓ := fun q => by
    have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q); omega
  have hSℓ : ∀ i, S i ≤ ℓ := fun i => by
    have := Finset.single_le_sum (f := S) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i); omega
  set Kr : Fin kc → ℕ := fun q => (∏ q' ∈ Finset.univ.erase q, Kl q') * ∏ i, Kh' i
  have hKr : ∀ q, Kr q * Kl q = K := fun q => by
    simp only [Kr, K]; rw [mul_comm _ (Kl q), ← mul_assoc, mul_comm (Kl q),
      Finset.prod_erase_mul _ _ (Finset.mem_univ q)]
  set Kr' : Fin (nGen hI hmax h𝔭 d + 1) → ℕ :=
    fun i => (∏ q, Kl q) * ∏ i' ∈ Finset.univ.erase i, Kh' i'
  have hKr' : ∀ i, Kr' i * Kh' i = K := fun i => by
    simp only [Kr', K]; rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hwpos : ∀ q : Fin kc, wv (headIdx hkn q) ≠ 0 := fun q => by
    intro h0
    have := hwv (headIdx hkn q)
    rw [h0, Nat.cast_zero] at this
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    have := hpos q
    nlinarith
  refine ⟨K, ℓ, hK, by omega, fun q => ⟨N q, ?_⟩, fun T τ hTx => ⟨?_⟩⟩
  · rw [hlidA q]
    exact Ideal.sum_mem _ fun γ hγ => Ideal.mul_mem_left _ _
      (prod_mem_span _ γ (hΓ q γ hγ).2)
  have hx : ∀ q, T.x (headIdx hkn q) = ã q := fun q => by rw [hTx, yZ_head]
  have hu : ∀ M : ℕ, M ≤ ℓ → ∀ K₁ K₂ : ℕ, K₁ * K₂ = K →
      ((K : MvPolynomial (Fin (m + (C.D k).n)) ℤ) * gk ^ ℓ) =
        ((K₁ : MvPolynomial (Fin (m + (C.D k).n)) ℤ) * gk ^ (ℓ - M)) * ((K₂ : _) * gk ^ M) := by
    intro M hM K₁ K₂ hK12
    rw [← hK12, Nat.cast_mul]
    have : ℓ = ℓ - M + M := (Nat.sub_add_cancel hM).symm
    conv_lhs => rw [this, pow_add]
    ring
  exact {
    hd := headIdx hkn
    hd_inj := fun q q' h => Fin.ext (by
      have := congrArg Fin.val h; simpa [headIdx] using this)
    w := fun q => wv (headIdx hkn q)
    hw := hwpos
    la := fun _ => 1
    ls := fun _ => 1
    lΓ := Γ
    lc := fun q γ => if h : γ ∈ Γ q then
      T.c * ((Kr q : MvPolynomial (Fin (m + (C.D k).n)) ℤ) * gk ^ (ℓ - N q)) * ql q ⟨γ, h⟩ else 0
    lhom := fun q γ hγ => by
      have h1 := (hΓ q γ hγ).1
      have h2 : ((1 * wv (headIdx hkn q) : ℕ) : ℤ) ≤
          ((∑ j, γ j * (genDeg hI hmax h𝔭 d j).toNat : ℕ) : ℤ) := by
        push_cast
        rw [one_mul]
        refine h1.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
        have := genDeg_pos hI hmax h𝔭 d j
        rw [Int.toNat_of_nonneg (by omega)]
      exact_mod_cast h2
    lne := fun q γ hγ => (hΓ q γ hγ).2
    lid := fun q => by
      have h := Ideal.mul_mem_left (lspan G)
        (T.c * ((Kr q : MvPolynomial (Fin (m + (C.D k).n)) ℤ) * gk ^ (ℓ - N q))) (hlidP q)
      convert h using 1
      simp only [ChartData.scale, pow_one, hx q]
      rw [hu (N q) (hNℓ q) (Kr q) (Kl q) (hKr q), mul_sub, ← Finset.sum_coe_sort (Γ q),
        Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun γ _ => ?_
        simp only [γ.2, dite_true]; ring
    hs := fun _ => 1
    hΓ := fun i => Finset.univ.image fun j => fun q => α i j (headIdx hkn q)
    hb := fun i α' => T.c * ((Kr' i : MvPolynomial (Fin (m + (C.D k).n)) ℤ) * gk ^ (ℓ - S i)) *
      ∑ j ∈ Finset.univ.filter (fun j => (fun q => α i j (headIdx hkn q)) = α'), qh i j
    hdeg := fun i α' hα' => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hα'
      have h1 := hαdeg i j
      rw [sum_head hkn _ (fun t => by
        rw [hα0 i j (tailIdx hkn t) (htail t), Nat.cast_zero, mul_zero])] at h1
      have h2 : (((genDeg hI hmax h𝔭 d i).toNat : ℕ) : ℤ) ≤
          ((∑ q, wv (headIdx hkn q) * α i j (headIdx hkn q) : ℕ) : ℤ) := by
        push_cast
        have := genDeg_pos hI hmax h𝔭 d i
        rw [Int.toNat_of_nonneg (by omega)]
        exact h1
      exact_mod_cast h2
    hid := fun i => by
      have h := Ideal.mul_mem_left (lspan G)
        (T.c * ((Kr' i : MvPolynomial (Fin (m + (C.D k).n)) ℤ) * gk ^ (ℓ - S i))) (hhidP i)
      convert h using 1
      simp only [ChartData.scale, pow_one, hx]
      rw [hu (S i) (hSℓ i) (Kr' i) (Kh' i) (hKr' i), mul_sub]
      rw [sum_regroup (fun j => fun q => α i j (headIdx hkn q)) (qh i)
        (fun α' => ∏ q, ã q ^ α' q), Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun α' _ => ?_
        ring }

end HM

end BezoutCounterexample.Principalization
