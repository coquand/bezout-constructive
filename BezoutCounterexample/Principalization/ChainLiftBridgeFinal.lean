import Mathlib
import BezoutCounterexample.Principalization.ChainLiftBridgeMain
import BezoutCounterexample.Principalization.ChainLiftBridgeConormal
import BezoutCounterexample.Principalization.Torsor
import BezoutCounterexample.Constructive.ChainLiftOffPres
import BezoutCounterexample.Constructive.ChainLiftChoice
import BezoutCounterexample.Principalization.MaxLocusPt

/-!
# The chain-lifting bridge: assembly (bridge milestone)

* `int_cong_of_A`: an identity `toA P₀ = Σ_j c_j toA P_j` in `A ≅ ℚ[Y] ⧸ (G)` between images of
  integer polynomials gives an integer congruence `K P₀ ≡ Σ_j q_j P_j` modulo `(G)` (`K > 0`).
* `exists_sum_of_mem_RI`: members of `RI` as explicit sums over a `Finset` of exponents.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive IsLocalization
open scoped Matrix

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Transfer

variable {A : Type*} [CommRing A] [Algebra ℚ A] {N : ℕ} (G : List (MvPolynomial (Fin N) ℤ))
  (e : MvPolynomial (Fin N) ℚ ⧸ lspan (G.map toQ) ≃+* A)

/-- The image of an integer polynomial in `A`. -/
def toA (P : MvPolynomial (Fin N) ℤ) : A := e (Ideal.Quotient.mk _ (toQ P))

lemma toA_add (P Q : MvPolynomial (Fin N) ℤ) : toA G e (P + Q) = toA G e P + toA G e Q := by
  simp [toA]

lemma toA_mul (P Q : MvPolynomial (Fin N) ℤ) : toA G e (P * Q) = toA G e P * toA G e Q := by
  simp [toA]

/-- `toA` as a ring hom. -/
def toAHom : MvPolynomial (Fin N) ℤ →+* A :=
  e.toRingHom.comp ((Ideal.Quotient.mk _).comp toQ)

lemma toAHom_apply (P : MvPolynomial (Fin N) ℤ) : toAHom G e P = toA G e P := rfl

/-- **Integer congruences from identities in `A`.** -/
theorem int_cong_of_A {ι : Type*} [Fintype ι] (P₀ : MvPolynomial (Fin N) ℤ)
    (P : ι → MvPolynomial (Fin N) ℤ) (c : ι → A) (h : toA G e P₀ = ∑ j, c j * toA G e (P j)) :
    ∃ (K : ℕ) (q : ι → MvPolynomial (Fin N) ℤ), 0 < K ∧
      (K : MvPolynomial (Fin N) ℤ) * P₀ - ∑ j, q j * P j ∈ lspan G := by
  have hsurj : ∀ x : A, ∃ p, e (Ideal.Quotient.mk _ p) = x := fun x => by
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨p, rfl⟩
  obtain ⟨cH, hcH⟩ := finite_choice fun j => hsurj (c j)
  obtain ⟨K₁, q, hK₁, hq⟩ := exists_int_mul_fin cH
  set Z := (K₁ : MvPolynomial (Fin N) ℤ) * P₀ - ∑ j, q j * P j
  have hZ : toQ Z ∈ lspan (G.map toQ) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply e.injective
    rw [map_zero]
    simp only [Z, map_sub, map_mul, map_natCast, map_sum, hq]
    have : e (Ideal.Quotient.mk _ (toQ P₀)) = ∑ j, c j * e (Ideal.Quotient.mk _ (toQ (P j))) := h
    rw [this, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hcH j]
    ring
  obtain ⟨K₂, hK₂, hmem⟩ := exists_int_mem G Z hZ
  refine ⟨K₂ * K₁, fun j => (K₂ : MvPolynomial (Fin N) ℤ) * q j, Nat.mul_pos hK₂ hK₁, ?_⟩
  convert hmem using 1
  simp only [Z, Nat.cast_mul, mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ => by ring

end Transfer

section RIsum

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → A)
  (deg : ι → ℤ)

/-- **Members of `RI k` as explicit sums.** -/
theorem exists_sum_of_mem_RI {k : ℤ} {z : A} (hz : z ∈ RI g deg k) :
    ∃ (Γ : Finset (ι → ℕ)) (c : (ι → ℕ) → A),
      (∀ γ ∈ Γ, k ≤ ∑ i, (γ i : ℤ) * deg i ∧ ∑ i, γ i ≠ 0) ∧
      z = ∑ γ ∈ Γ, c γ * ∏ i, g i ^ γ i := by
  rw [RI, Submodule.mem_span_set'] at hz
  obtain ⟨n, f, gg, hfg⟩ := hz
  obtain ⟨γ, hγ⟩ := fin_choice fun j => (gg j).2
  have hγk := fun j => (hγ j).1
  have hγne := fun j => (hγ j).2.1
  have hγz := fun j => (hγ j).2.2
  refine ⟨Finset.univ.image γ, fun γ' => ∑ j ∈ Finset.univ.filter (γ · = γ'), f j, ?_, ?_⟩
  · intro γ' hγ'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hγ'
    exact ⟨hγk j, hγne j⟩
  · rw [← hfg]
    simp only [Finset.sum_mul]
    have hfib : ∀ x ∈ Finset.univ.image γ, ∑ j ∈ Finset.univ.filter (γ · = x),
        f j * ∏ i, g i ^ x i = ∑ j ∈ Finset.univ.filter (γ · = x), f j * ∏ i, g i ^ γ j i :=
      fun x _ => Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.1 hj).2]
    rw [Finset.sum_congr rfl hfib, Finset.sum_fiberwise_of_maps_to (g := γ)
      (fun j _ => Finset.mem_image_of_mem γ (Finset.mem_univ j))
      (f := fun j => f j * ∏ i, g i ^ γ j i)]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul, hγz j]

end RIsum

/-! ## Helpers -/

/-- **Scaling chart data** by a polynomial. -/
def _root_.BezoutCounterexample.Constructive.ChartData.scale {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)} (T : ChartData G)
    (u : MvPolynomial (Fin (m + n)) ℤ) : ChartData G where
  x := T.x
  B := u • T.B
  V := u • T.V
  c := u * T.c
  hL := fun i j => by
    have := Ideal.mul_mem_left (lspan G) u (T.hL i j)
    convert this using 1
    simp only [Matrix.add_apply, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring
  hD := fun i j => by
    have := Ideal.mul_mem_left (lspan G) u (T.hD i j)
    convert this using 1
    simp [Matrix.mul_smul]
  hX := fun i j => by
    have := Ideal.mul_mem_left (lspan G) u (T.hX i j)
    convert this using 1
    simp only [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring

/-- Regrouping a sum indexed by `Fin K` by the values of an exponent map. -/
lemma sum_regroup {R : Type*} [CommRing R] {K : ℕ} {β : Type*} [DecidableEq β] (α : Fin K → β)
    (q : Fin K → R) (Mon : β → R) :
    ∑ j, q j * Mon (α j) =
      ∑ a ∈ Finset.univ.image α, (∑ j ∈ Finset.univ.filter (α · = a), q j) * Mon a := by
  simp only [Finset.sum_mul]
  have hfib : ∀ a ∈ Finset.univ.image α, ∑ j ∈ Finset.univ.filter (α · = a), q j * Mon a =
      ∑ j ∈ Finset.univ.filter (α · = a), q j * Mon (α j) :=
    fun a _ => Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_fiberwise_of_maps_to (g := α)
    (fun j _ => Finset.mem_image_of_mem α (Finset.mem_univ j)) (f := fun j => q j * Mon (α j))]

/-- **The radical argument** for the global partition of unity. -/
theorem one_mem_of_radical {R : Type*} [CommRing R] (𝔉 𝔅 : Ideal R) (h𝔉𝔅 : 𝔉 ≤ 𝔅)
    {K : ℕ} (i : R) (f g : Fin K → R) (hone : i + ∑ k, f k * g k = 1)
    (hi : i ∈ 𝔉.radical) (hg : ∀ k, g k ∈ 𝔅.radical) : (1 : R) ∈ 𝔅 := by
  have h1 : (1 : R) ∈ 𝔅.radical := by
    rw [← hone]
    refine Ideal.add_mem _ (Ideal.radical_mono h𝔉𝔅 hi) ?_
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hg k)
  obtain ⟨n, hn⟩ := h1
  rwa [one_pow] at hn

section HM

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (d : ℕ) (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hI hmax h𝔭 in
/-- The torsor generators contain the Rees generators. -/
lemma gen_covers [Fact (Constructive.HasPres A)] [Constructive.Enum A] (π : A) (j : ℤ) (hj1 : 1 ≤ j) (hjd : j ≤ d) (x : A)
    (hx : x ∈ gensF hI hmax h𝔭 d j) :
    ∃ i, genCoeff hI hmax h𝔭 d π i = x ∧ genDeg hI hmax h𝔭 d i = j := by
  obtain ⟨i, hi⟩ := List.get_of_mem (mem_genPairs hI hmax h𝔭 d hj1 hjd hx)
  refine ⟨i.succ, ?_, ?_⟩
  · simp only [genCoeff, Fin.cons_succ, hi]
  · simp only [genDeg, Fin.cons_succ, hi]

include hd hw in
/-- **lid over the torsor generators**: `g^N aₕ = Σ_γ c_γ gen^γ`, `γ·deg ≥ wₕ`, `γ ≠ 0`. -/
theorem lid_gen [Constructive.Enum A] [Fact (Constructive.HasPres A)] (C : ChartCoverPt I v₀ 𝔭) (k : Fin C.n) (s : ℕ) (a : Fin (C.D k).n → A)
    (ha : ∀ i, (C.D k).cB.x i * algebraMap A (C.D k).B (C.D k).g ^ s =
      algebraMap A (C.D k).B (a i)) (π : A) (h : Fin (C.D k).n) (hne : (C.D k).ek h ≠ 0)
    (wh : ℕ) (hwh : (wh : ℚ) = d * v₀ h) :
    ∃ (N : ℕ) (Γ : Finset (Fin (nGen hI hmax h𝔭 d + 1) → ℕ))
      (c : (Fin (nGen hI hmax h𝔭 d + 1) → ℕ) → A),
      (∀ γ ∈ Γ, (wh : ℤ) ≤ ∑ i, (γ i : ℤ) * genDeg hI hmax h𝔭 d i ∧ ∑ i, γ i ≠ 0) ∧
      (C.D k).g ^ N * a h = ∑ γ ∈ Γ, c γ * ∏ i, genCoeff hI hmax h𝔭 d π i ^ γ i := by
  have hZ : ∀ p : Pt A, 𝔭 ≤ p.ker → I ≤ p.ker ∧ InvAt I p.ker v₀ := fun p h => h𝔭.memP hI hmax p h
  obtain ⟨N, hN⟩ := lid_A_pt hI hZ C k s a ha h hne
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
theorem hid_gen [Constructive.Enum A] [Fact (Constructive.HasPres A)] (C : ChartCoverPt I v₀ 𝔭) (k : Fin C.n) (s : ℕ) (a : Fin (C.D k).n → A)
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
  obtain ⟨S, K, b, α, hα0, hαt, hid⟩ := hid_A_pt hI hZ C k s a ha hmem
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

include hI hmax h𝔭 hd hw in
/-- **The component lies in `F₁`.** -/
theorem comp_le_F1 [Fact (Constructive.HasPres A)] : 𝔭 ≤ (compFil hI hmax h𝔭 d).F 1 := by
  intro x hx
  have h := h𝔭.pow_le_compFPtP hI hmax hd hw 1 (by rwa [pow_one])
  rw [compFil_F]
  simpa using h

/-! ## Head data of one chart -/

/-- Products over `Fin n` with exponents vanishing on the tail are products over the head. -/
lemma prod_head {R : Type*} [CommMonoid R] {n kc : ℕ} (hk : kc ≤ n) (f : Fin n → R)
    (ht : ∀ t, f (tailIdx hk t) = 1) : ∏ j, f j = ∏ q, f (headIdx hk q) := by
  rw [← (headTail hk).prod_comp, Fintype.prod_sum_type]
  simp only [headTail_inl, headTail_inr, ht, Finset.prod_const_one, mul_one]

/-- Sums over `Fin n` with terms vanishing on the tail are sums over the head. -/
lemma sum_head {R : Type*} [AddCommMonoid R] {n kc : ℕ} (hk : kc ≤ n) (f : Fin n → R)
    (ht : ∀ t, f (tailIdx hk t) = 0) : ∑ j, f j = ∑ q, f (headIdx hk q) := by
  rw [← (headTail hk).sum_comp, Fintype.sum_sum_type]
  simp only [headTail_inl, headTail_inr, ht, Finset.sum_const_zero, add_zero]

lemma yZ_head {m n kc : ℕ} (hk : kc ≤ n) (ã : Fin kc → MvPolynomial (Fin (m + n)) ℤ)
    (τ : RowIdx (m + n) (n - kc)) (q : Fin kc) : yZ hk ã τ (headIdx hk q) = ã q := by
  simp [yZ, headIdx]

/-- A monomial with a positive exponent lies in the ideal of the generators. -/
lemma prod_mem_span {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (g : ι → R) (γ : ι → ℕ)
    (hγ : ∑ i, γ i ≠ 0) : ∏ i, g i ^ γ i ∈ Ideal.span (Set.range g) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hγ
  refine Ideal.prod_mem _ (Finset.mem_univ i) ?_
  rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi), pow_succ]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

set_option maxHeartbeats 2000000 in
include hd hw in
/-- **The head data of one chart**, for every chart data with coordinates `yZ`, after scaling
the multiplier by `K g_k^ℓ`. -/
theorem chart_heads [Fact (Constructive.HasPres A)] [Constructive.Enum A] (C : ChartCoverPt I v₀ 𝔭) (k : Fin C.n) {m n kc : ℕ}
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
  have hlid := fun q : Fin kc => lid_gen hI hmax h𝔭 d hd (fun i => ⟨wv i, hwv i⟩) C k s a hnum π
    (headIdx hkn q) ((hhead _).2 q.2) (wv (headIdx hkn q)) (hwv _)
  obtain ⟨N, hlid⟩ := finite_choice hlid
  obtain ⟨Γ, hlid⟩ := finite_choice hlid
  obtain ⟨cl, hlid⟩ := finite_choice hlid
  have hΓ := fun q => (hlid q).1
  have hlidA := fun q => (hlid q).2
  -- hid data
  have hhid := fun i : Fin (nGen hI hmax h𝔭 d + 1) => hid_gen hI hmax h𝔭 d
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

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- **The head of a chart is given by the invariant**: `eᵢ ≠ 0 ↔ i < #{j : v₀ j ≠ 0}`. -/
theorem head_support {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) {n : ℕ} (hdn : D.n = n) :
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
theorem LocData.n_eq {𝔪₁ 𝔪₂ : Ideal A} [𝔪₁.IsMaximal] [𝔪₂.IsMaximal] (D₁ : LocData I v₀ 𝔪₁)
    (D₂ : LocData I v₀ 𝔪₂) : D₁.n = D₂.n := by
  have hg1 : D₁.g ∉ (⊥ : Ideal A) := fun h => D₁.hg ((Submodule.mem_bot A).1 h ▸ zero_mem _)
  have hg2 : D₂.g ∉ (⊥ : Ideal A) := fun h => D₂.hg ((Submodule.mem_bot A).1 h ▸ zero_mem _)
  exact Chart.card_eq (Loc.transport (D₁.ctrl ⊥ hg1) D₁.ck) (Loc.transport (D₂.ctrl ⊥ hg2) D₂.ck)

/-! ## The main theorem -/

/-- `D₂ = 2 Π dⱼ` and `Eᵢ = 2 Π_{j ≠ i} dⱼ`. -/
lemma exists_E {r : ℕ} (dd : Fin r → ℕ) (hdd : ∀ i, 0 < dd i) :
    ∃ (D₂ : ℕ) (E : Fin r → ℕ), D₂ ≠ 0 ∧ (∀ i, E i * dd i = D₂) ∧ ∀ i, Even (E i) := by
  refine ⟨2 * ∏ j, dd j, fun i => 2 * ∏ j ∈ Finset.univ.erase i, dd j,
    Nat.mul_ne_zero two_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => (hdd i).ne'),
    fun i => ?_, fun i => even_two_mul _⟩
  rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

include hd hw in
/-- **Chain lifting for one of HM's torsor steps.** For the ring `A ≅ ℚ[Y] ⧸ (G)` (integer
presentation `G`, `Y = (Y₁ … Y_{m+n})`, `n` the chart dimension), a separated chart cover `C` of
the component `V(𝔭)`, a non-divisorial centre (`v₀ 1 ≠ 0`, so `kc ≥ 2` head functions) and
`π ∈ F₁`: integer lifts `gZᵢ` of the
torsor generators (up to positive integers), the torsor presentation `G'` (with its presentation
property) and its `OffStep`, which **lifts chains**. -/
theorem chainLift_torsor_step [Constructive.Enum A] [Fact (Constructive.HasPres A)] {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
    {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ)) (e : Quo (GQ G) ≃+* A)
    (C : ChartCoverPt I v₀ 𝔭) (hdim₀ : ∃ k, (C.D k).n = n) (hv1 : v₀ 1 ≠ 0)
    (hcon : ∃ Dc : ℕ, 0 < Dc ∧ ConormalInj G (Dc : MvPolynomial (Fin (m + n)) ℤ)) :
    ∃ (gZ : Fin (nGen hI hmax h𝔭 d + 1) → MvPolynomial (Fin (m + n)) ℤ)
      (Dg : Fin (nGen hI hmax h𝔭 d + 1) → ℕ)
      (G' : List (MvPolynomial (Fin ((m + n) + (1 + ((nGen hI hmax h𝔭 d + 1) +
        (nGen hI hmax h𝔭 d + 1))))) ℤ))
      (O : OffStep (m + n) ((m + n) + (1 + ((nGen hI hmax h𝔭 d + 1) + (nGen hI hmax h𝔭 d + 1))))
        (Fin (nGen hI hmax h𝔭 d + 1))),
      (∀ i, 0 < Dg i ∧ toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i) ∧
      O.Pt = PtG G ∧ O.Pt' = PtG G' ∧ O.g = (fun i w => evalR w (gZ i)) ∧
      O.d = (fun i => (genDeg hI hmax h𝔭 d i).toNat) ∧
      (∀ h, aeval (fvec gZ O.d) h ∈ lspan (H₀ G gZ O.d) ↔ h ∈ lspan (G'.map toQZ)) ∧
      O.π = (fun x k => x (Fin.castAdd _ k)) ∧ ChainLift O.Pt O.Pt' O.π := by
  -- destructure first, so that `omega` below does not see `hcon` (it would use `hcon.choose`)
  obtain ⟨Dc, hDc, hinj⟩ := hcon
  -- all charts have `n` functions
  obtain ⟨k₁, hk₁⟩ := hdim₀
  have hdim : ∀ k, (C.D k).n = n := fun k => (LocData.n_eq (C.D k) (C.D k₁)).trans hk₁
  -- the head count from the invariant
  set kc := (Finset.univ.filter fun j : Fin n => v₀ j ≠ 0).card
  have hkn : kc ≤ n := (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  obtain ⟨k₀⟩ : Nonempty (Fin C.n) := by
    rcases Nat.eq_zero_or_pos C.n with h0 | h0
    · exfalso
      have h1 := C.one
      have : C.i = 1 := by
        rw [← h1, Finset.sum_eq_zero (fun k _ => absurd k.2 (by omega)), add_zero]
      exact h𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (this ▸ C.hi))
    · exact ⟨⟨0, h0⟩⟩
  have hhead := fun k => head_support (C.D k) (hdim k)
  have h1n : 1 < n := by
    by_contra h
    apply hv1
    have := congrFun (C.D k₀).hv 1
    rw [← this]
    simp only [ext0]
    rw [dif_neg (by rw [hdim k₀]; omega)]
  have hn : 0 < n := by omega
  have hk2 : 2 ≤ kc := by
    have hek : ∀ j : Fin (C.D k₀).n, (C.D k₀).ek j = v₀ j := fun j => by
      have := congrFun (C.D k₀).hv j; rwa [ext0_apply] at this
    have hn' : 1 < (C.D k₀).n := by rw [hdim k₀]; exact h1n
    have hv1' : v₀ 1 ≠ 0 := hv1
    have hv0 : v₀ 0 ≠ 0 := by
      have hle : (C.D k₀).ek ⟨1, hn'⟩ ≤ (C.D k₀).ek ⟨0, by omega⟩ :=
        (C.D k₀).inv.anti (Fin.le_def.2 (by simp))
      rw [hek, hek] at hle
      have hnn : 0 ≤ v₀ 1 := by rw [← hek ⟨1, hn'⟩]; exact (C.D k₀).inv.nonneg _
      intro h0
      exact hv1 (le_antisymm (h0 ▸ hle) hnn)
    have hsub : ({⟨0, by omega⟩, ⟨1, h1n⟩} : Finset (Fin n)) ⊆
        Finset.univ.filter fun j : Fin n => v₀ j ≠ 0 := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp [hv0, hv1]
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (by simp [Fin.ext_iff])] at this
  set ι := Fin (nGen hI hmax h𝔭 d + 1)
  set gen := genCoeff hI hmax h𝔭 d π
  set dd : ι → ℕ := fun i => (genDeg hI hmax h𝔭 d i).toNat
  have hdd : ∀ i, 0 < dd i := fun i => by
    have := genDeg_pos hI hmax h𝔭 d i; simp only [dd]; omega
  have hddZ : ∀ i, ((dd i : ℕ) : ℤ) = genDeg hI hmax h𝔭 d i := fun i => by
    have := genDeg_pos hI hmax h𝔭 d i; simp only [dd]; omega
  -- 1. integer lifts of the torsor generators
  have hsurj : ∀ x : A, ∃ p, e (Ideal.Quotient.mk _ p) = x := fun x => by
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨p, rfl⟩
  obtain ⟨pgen, hpgen⟩ := finite_choice fun i => hsurj (gen i)
  obtain ⟨Dg₀, gZ, hDg₀, hgZ⟩ := exists_int_mul_fin pgen
  have hgZA : ∀ i, toA G e (gZ i) = (Dg₀ : A) * gen i := fun i => by
    rw [toA, hgZ i, map_mul, map_mul, map_natCast, map_natCast, hpgen]
  -- 2. the torsor presentation and its `OffStep`
  obtain ⟨D₂, E, hD₂, hEd, hE⟩ := exists_E dd hdd
  obtain ⟨G', O, hPt, hPt', hOg, hOd, hOE, hOπ, hpres⟩ := exists_offStep G gZ dd hD₂ E hEd hE
  refine ⟨gZ, fun _ => Dg₀, G', O, fun i => ⟨hDg₀, hgZA i⟩, hPt, hPt', hOg, hOd,
    hOd ▸ hpres, hOπ, ?_⟩
  -- 3. conormal injectivity (given: from smoothness or from a certificate; destructured above)
  -- 4. the charts
  have hP := fun k => chart_partition G e (C.D k) (hdim k) hkn hn
  obtain ⟨sC, hP⟩ := finite_choice hP
  obtain ⟨aC, hP⟩ := finite_choice hP
  obtain ⟨ãC, hP⟩ := finite_choice hP
  obtain ⟨DqC, hP⟩ := finite_choice hP
  obtain ⟨TC, hP⟩ := finite_choice hP
  obtain ⟨MC, hP⟩ := finite_choice hP
  obtain ⟨βC, hP⟩ := finite_choice hP
  obtain ⟨ωC, hP⟩ := finite_choice hP
  have hDqC := fun k => (hP k).1
  have hTxC := fun k => (hP k).2.1
  have hnumC := fun k => (hP k).2.2.1
  have hpartC := fun k => (hP k).2.2.2
  obtain ⟨pgk, hpgk⟩ := finite_choice fun k : Fin C.n => hsurj (C.D k).g
  obtain ⟨Dgk, gk, hDgk, hgk⟩ := exists_int_mul_fin pgk
  have hgkA : ∀ k, toA G e (gk k) = (Dgk : A) * (C.D k).g := fun k => by
    rw [toA, hgk k, map_mul, map_mul, map_natCast, map_natCast, hpgk]
  have hH := fun k => chart_heads hI hmax h𝔭 d hd hw C k G e (hdim k)
    hkn (hhead k) hπ (sC k) (aC k) (hnumC k) (ãC k) (DqC k) (fun q => (hDqC k q).1)
    (fun q => (hDqC k q).2) gZ Dg₀ hDg₀ hgZA (gk k) Dgk hDgk (hgkA k)
  obtain ⟨Kk, hH⟩ := finite_choice hH
  obtain ⟨ℓk, hH⟩ := finite_choice hH
  have hKk := fun k => (hH k).1
  have hℓk := fun k => (hH k).2.1
  have hlidk := fun k => (hH k).2.2.1
  have hHk := fun k => (hH k).2.2.2
  set uk : Fin C.n → MvPolynomial (Fin (m + n)) ℤ := fun k => (Kk k : _) * gk k ^ ℓk k
  set T' : (Σ k : Fin C.n, RowIdx (m + n) (n - kc)) → ChartData G :=
    fun p => (TC p.1 p.2).scale (uk p.1)
  obtain ⟨H'⟩ : Nonempty (∀ p, ChartHead (T' p) gZ dd kc) :=
    finite_nonempty_pi fun p => hHk p.1 (TC p.1 p.2) p.2 (hTxC p.1 p.2)
  -- 5. the global partition in `A`
  set 𝔉 : Ideal A := Ideal.span (Set.range gen)
  set 𝔅 : Ideal A := 𝔉 ⊔ Ideal.span (Set.range fun p => toA G e (T' p).c)
  have hF1 : (compFil hI hmax h𝔭 d).F 1 ≤ 𝔉 := by
    rw [← span_gensF, Ideal.span_le]
    intro x hx
    obtain ⟨i, hi, -⟩ := gen_covers hI hmax h𝔭 d π 1 le_rfl (by exact_mod_cast hd) x hx
    exact Ideal.subset_span ⟨i, hi⟩
  have hinvA : ∀ D : ℕ, 0 < D → algebraMap ℚ A ((D : ℚ))⁻¹ * (D : A) = 1 := fun D hD => by
    rw [← map_natCast (algebraMap ℚ A), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hD.ne'),
      map_one]
  have hone : (1 : A) ∈ 𝔅 := by
    refine one_mem_of_radical 𝔉 𝔅 le_sup_left C.i C.f (fun k => (C.D k).g) C.one
      (Ideal.le_radical (hF1 (comp_le_F1 hI hmax h𝔭 d hd hw C.hi))) fun k => ?_
    -- `g_k ∈ √𝔅`
    have hga : ∀ q, (C.D k).g ^ ℓk k * aC k (headIdx hkn q) ∈ 𝔅.radical := fun q => by
      obtain ⟨N, hN⟩ := hlidk k q
      refine ⟨N + 1, ?_⟩
      have : ((C.D k).g ^ ℓk k * aC k (headIdx hkn q)) ^ (N + 1) =
          ((C.D k).g ^ N * aC k (headIdx hkn q)) *
            ((C.D k).g ^ (ℓk k * (N + 1) - N) * aC k (headIdx hkn q) ^ N) := by
        have hle : N ≤ ℓk k * (N + 1) := by nlinarith [hℓk k]
        rw [mul_pow, ← pow_mul, pow_succ (aC k _)]
        conv_lhs => rw [show ℓk k * (N + 1) = N + (ℓk k * (N + 1) - N) by omega, pow_add]
        ring
      rw [this]
      exact le_sup_left (α := Ideal A) (Ideal.mul_mem_right _ _ hN)
    have hc' : ∀ τ, toA G e (T' ⟨k, τ⟩).c =
        (Kk k : A) * (Dgk : A) ^ ℓk k * (C.D k).g ^ ℓk k * e (Ideal.Quotient.mk _ (toQ (TC k τ).c)) :=
      fun τ => by
        show toA G e ((Kk k : MvPolynomial (Fin (m + n)) ℤ) * gk k ^ ℓk k * (TC k τ).c) = _
        have h1 : toA G e ((Kk k : MvPolynomial (Fin (m + n)) ℤ)) = (Kk k : A) := by simp [toA]
        have h2 : toA G e (gk k ^ ℓk k) = toA G e (gk k) ^ ℓk k := by
          rw [← toAHom_apply, map_pow]; rfl
        rw [toA_mul, toA_mul, h1, h2, hgkA k, toA]; ring
    have hpow : (C.D k).g ^ (MC k + ℓk k) ∈ 𝔅.radical := by
      have hmem : ((Kk k : A) * (Dgk : A) ^ ℓk k) * (C.D k).g ^ (MC k + ℓk k) ∈ 𝔅.radical := by
        have : ((Kk k : A) * (Dgk : A) ^ ℓk k) * (C.D k).g ^ (MC k + ℓk k) =
            ∑ τ, βC k τ * toA G e (T' ⟨k, τ⟩).c + ∑ q, ((Kk k : A) * (Dgk : A) ^ ℓk k * ωC k q) *
              ((C.D k).g ^ ℓk k * aC k (headIdx hkn q)) := by
          rw [pow_add, hpartC k]
          simp only [hc', add_mul, Finset.sum_mul, mul_add, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
        rw [this]
        refine Ideal.add_mem _ (Ideal.le_radical (Ideal.sum_mem _ fun τ _ =>
          Ideal.mul_mem_left _ _ (le_sup_right (α := Ideal A) (Ideal.subset_span ⟨⟨k, τ⟩, rfl⟩))))
          (Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (hga q))
      have hunit : algebraMap ℚ A (((Kk k : ℚ) * (Dgk : ℚ) ^ ℓk k))⁻¹ *
          ((Kk k : A) * (Dgk : A) ^ ℓk k) = 1 := by
        have := hinvA (Kk k * Dgk ^ ℓk k) (Nat.mul_pos (hKk k) (pow_pos hDgk _))
        push_cast at this; exact this
      have := Ideal.mul_mem_left (𝔅.radical) (algebraMap ℚ A (((Kk k : ℚ) * (Dgk : ℚ) ^ ℓk k))⁻¹) hmem
      rwa [← mul_assoc, hunit, one_mul] at this
    obtain ⟨r, hr⟩ := hpow
    exact ⟨(MC k + ℓk k) * r, by rw [pow_mul]; exact hr⟩
  -- 6. the partition as a combination
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hone
  rw [Ideal.mem_span_range_iff_exists_fun] at hx hy
  obtain ⟨β, rfl⟩ := hx
  obtain ⟨ε, rfl⟩ := hy
  -- 7. the integer cover
  obtain ⟨K₀, q, hK₀, hq⟩ := int_cong_of_A G e (1 : MvPolynomial (Fin (m + n)) ℤ)
    (Sum.elim gZ fun p => (T' p).c * (Dc : MvPolynomial (Fin (m + n)) ℤ))
    (Sum.elim (fun i => β i * algebraMap ℚ A ((Dg₀ : ℚ))⁻¹)
      (fun p => ε p * algebraMap ℚ A ((Dc : ℚ))⁻¹)) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have h1 : toA G e (1 : MvPolynomial (Fin (m + n)) ℤ) = 1 := by simp [toA]
    rw [h1, ← hxy]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hgZA i]
      linear_combination (-(β i * gen i)) * hinvA Dg₀ hDg₀
    · refine Finset.sum_congr rfl fun p _ => ?_
      have h2 : toA G e ((T' p).c * (Dc : MvPolynomial (Fin (m + n)) ℤ)) =
          toA G e (T' p).c * (Dc : A) := by rw [toA_mul]; simp [toA]
      rw [h2]
      linear_combination (-(ε p * toA G e (T' p).c)) * hinvA Dc hDc)
  -- 8. flatten the chart index and conclude
  set eqv := (Fintype.equivFin (Σ k : Fin C.n, RowIdx (m + n) (n - kc))).symm
  have hd' : O.d = dd := hOd
  have Hf : ∀ j, ChartHead (T' (eqv j)) gZ O.d kc := fun j => hd' ▸ H' (eqv j)
  refine ChainLift.of_charts hn hk2 O hPt gZ hOg (fun j => T' (eqv j))
    (fun _ => (Dc : MvPolynomial (Fin (m + n)) ℤ)) (fun _ => hinj) Hf K₀ hK₀
    (fun i => q (Sum.inl i)) (fun j => q (Sum.inr (eqv j))) ?_
  have hsum := hq
  rw [Fintype.sum_sum_type, mul_one] at hsum
  simp only [Sum.elim_inl, Sum.elim_inr] at hsum
  convert hsum using 3
  rw [← eqv.sum_comp (fun p => q (Sum.inr p) * ((T' p).c * (Dc : MvPolynomial (Fin (m + n)) ℤ)))]
  exact Finset.sum_congr rfl fun j _ => by ring

end HM

end BezoutCounterexample.Principalization
