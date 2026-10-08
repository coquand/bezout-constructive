import Mathlib
import BezoutCounterexample.Constructive.ChainLiftMinorPoly
import BezoutCounterexample.Constructive.ChainLiftCert

/-!
# Gluing the charts (§2.2, milestones C2–C4, certificate level)

Inputs, all polynomial certificates modulo `(G)` over `ℤ`:

* finitely many charts `T k : ChartData G` with conormal multipliers `dc k` (`ConormalInj G (dc k)`);
* a **linear partition of unity** `C₀ ≡ Σᵢ bᵢ gᵢ + Σₖ eₖ cₖ dcₖ` (`C₀` a positive integer) by the
  filtration generators `gᵢ` and the chart multipliers.

`glue_cover` (C2): the square pieces of all charts (`exists_minor_cover`), indexed by
`Fin K × Sub G`, with a partition `C ≡ Σᵢ cbᵢ gᵢ + Σ_p ca_p h_p` (`C` a positive integer). Power
trick: `(Σ f)^M ∈ (f_j^L)` (pigeonhole), `f_k^L` is a multiple of the `W_k` of chart `k`, and the
constants `m!^{K_k}` are made uniform as `m!^{Σ K_k}`.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}

/-- Equality in the quotient as membership. -/
lemma mem_of_quot_eq {x y : MvPolynomial (Fin (m + n)) ℤ} (h : π G x = π G y) : x - y ∈ lspan G :=
  Ideal.Quotient.eq.1 h

lemma quot_eq_of_mem {x y : MvPolynomial (Fin (m + n)) ℤ} (h : x - y ∈ lspan G) : π G x = π G y :=
  Ideal.Quotient.eq.2 h

/-- **C2: the pieces of all charts and a linear partition of unity.** -/
theorem glue_cover (hn : 0 < n) {K : ℕ} (T : Fin K → ChartData G) (dc : Fin K → MvPolynomial (Fin (m + n)) ℤ)
    (hinj : ∀ k, ConormalInj G (dc k)) {ι : Type*} [Fintype ι] (g : ι → MvPolynomial (Fin (m + n)) ℤ) (C₀ : ℕ)
    (hC₀ : 0 < C₀) (b : ι → MvPolynomial (Fin (m + n)) ℤ) (e : Fin K → MvPolynomial (Fin (m + n)) ℤ)
    (hcov : (C₀ : MvPolynomial (Fin (m + n)) ℤ) - (∑ i, b i * g i + ∑ k, e k * (T k).c * dc k) ∈ lspan G) :
    ∃ (P : Fin K × ChartData.MinorIdx (m := m) (n := n) G → SquarePiece m n G) (C : ℕ)
      (cb : ι → MvPolynomial (Fin (m + n)) ℤ) (ca : Fin K × ChartData.MinorIdx (m := m) (n := n) G → MvPolynomial (Fin (m + n)) ℤ), 0 < C ∧
      (∀ p, (P p).F = Fin.addCases (fun a => G.get (ChartData.subEnum p.2 a)) (T p.1).x) ∧
      (∀ p, (P p).h - (T p.1).Δ (ChartData.subEnum p.2) ^ (2 * G.length + 1) *
        ((T p.1).c ^ (n + G.length * (n + 1)) * dc p.1 ^ G.length) ∈ lspan G) ∧
      (C : MvPolynomial (Fin (m + n)) ℤ) - (∑ i, cb i * g i + ∑ p, ca p * (P p).h) ∈ lspan G := by
  set r := G.length
  have hex : ∀ k, ∃ t : ℕ × (ChartData.MinorIdx (m := m) (n := n) G → SquarePiece m n G) ×
      (ChartData.MinorIdx (m := m) (n := n) G → MvPolynomial (Fin (m + n)) ℤ),
      (∀ s, (t.2.1 s).F = Fin.addCases (fun a => G.get (ChartData.subEnum s a)) (T k).x) ∧
      (∀ s, (t.2.1 s).h - (T k).Δ (ChartData.subEnum s) ^ (2 * r + 1) *
        ((T k).c ^ (n + r * (n + 1)) * dc k ^ r) ∈ lspan G) ∧
      ((m.factorial ^ t.1 : ℕ) : MvPolynomial (Fin (m + n)) ℤ) * ((T k).c ^ (m * t.1 + (n + r * (n + 1))) * dc k ^ r) -
        ∑ s, t.2.2 s * (t.2.1 s).h ∈ lspan G := fun k => by
    obtain ⟨K', P, u, h1, h2, h3⟩ := (T k).exists_minor_cover hn (dc k) (hinj k)
    exact ⟨(K', P, u), h1, h2, h3⟩
  obtain ⟨t, ht⟩ := fin_choice hex
  -- exponents
  set Kk : Fin K → ℕ := fun k => (t k).1
  set Kt := ∑ k, Kk k
  set a : Fin K → ℕ := fun k => m * Kk k + (n + r * (n + 1))
  set L := 1 + ∑ k, a k
  have haL : ∀ k, a k ≤ L := fun k => by
    have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    omega
  have hra : ∀ k, r ≤ a k := fun k => by
    have : r ≤ r * (n + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos n)
    simp only [a]; omega
  have hKt : ∀ k, Kk k ≤ Kt := fun k =>
    Finset.single_le_sum (f := Kk) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  -- the terms of the partition
  set f : Option (Fin K) → MvPolynomial (Fin (m + n)) ℤ := fun o => Option.elim o (∑ i, b i * g i)
    (fun k => e k * (T k).c * dc k)
  have hsum : ∑ o, f o = ∑ i, b i * g i + ∑ k, e k * (T k).c * dc k := by
    rw [Fintype.sum_option]; rfl
  set M := (Finset.univ : Finset (Option (Fin K))).card * (L - 1) + 1
  have hpow := Ideal.sum_pow_mem_span_pow (Finset.univ : Finset (Option (Fin K))) f (L - 1)
  rw [Finset.coe_univ, Set.image_univ, Ideal.mem_span_range_iff_exists_fun] at hpow
  obtain ⟨α, hα⟩ := hpow
  have hL1 : L - 1 + 1 = L := by omega
  rw [hL1] at hα
  set mf : MvPolynomial (Fin (m + n)) ℤ := (m.factorial : MvPolynomial (Fin (m + n)) ℤ)
  refine ⟨fun p => (t p.1).2.1 p.2, m.factorial ^ Kt * C₀ ^ M,
    fun i => mf ^ Kt * α none * (∑ j, b j * g j) ^ (L - 1) * b i,
    fun p => mf ^ (Kt - Kk p.1) * α (some p.1) * e p.1 ^ L * (T p.1).c ^ (L - a p.1) *
      dc p.1 ^ (L - r) * (t p.1).2.2 p.2,
    by positivity, fun p => (ht p.1).1 p.2, fun p => (ht p.1).2.1 p.2, ?_⟩
  apply mem_of_quot_eq
  have e1 : π G ((m.factorial ^ Kt * C₀ ^ M : ℕ) : MvPolynomial (Fin (m + n)) ℤ) = π G (mf ^ Kt * (∑ o, f o) ^ M) := by
    have h := quot_eq_of_mem hcov
    rw [← hsum] at h
    push_cast
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, h]
  have e3 : ∀ k, π G (∑ s, (t k).2.2 s * ((t k).2.1 s).h) =
      π G (mf ^ Kk k * ((T k).c ^ a k * dc k ^ r)) := fun k => by
    have := quot_eq_of_mem (ht k).2.2
    push_cast at this
    exact this.symm
  -- the right-hand side, as a combination of the `W_k`
  have hR : π G (∑ i, (mf ^ Kt * α none * (∑ j, b j * g j) ^ (L - 1) * b i) * g i +
      ∑ p : Fin K × ChartData.MinorIdx (m := m) (n := n) G,
        (mf ^ (Kt - Kk p.1) * α (some p.1) * e p.1 ^ L * (T p.1).c ^ (L - a p.1) *
          dc p.1 ^ (L - r) * (t p.1).2.2 p.2) * ((t p.1).2.1 p.2).h) =
      π G (∑ i, (mf ^ Kt * α none * (∑ j, b j * g j) ^ (L - 1) * b i) * g i +
        ∑ k, (mf ^ (Kt - Kk k) * α (some k) * e k ^ L * (T k).c ^ (L - a k) * dc k ^ (L - r)) *
          (mf ^ Kk k * ((T k).c ^ a k * dc k ^ r))) := by
    rw [map_add, map_add]
    congr 1
    rw [Fintype.sum_prod_type, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← e3 k, ← map_mul]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e1, hR, ← hα, Fintype.sum_option]
  congr 1
  have hpL : ∀ x : MvPolynomial (Fin (m + n)) ℤ, x ^ L = x ^ (L - 1) * x := fun x => by
    rw [← pow_succ, hL1]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · simp only [f, Option.elim]
    rw [hpL, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [f, Option.elim]
    have h1 : mf ^ (Kt - Kk k) * mf ^ Kk k = mf ^ Kt := pow_sub_mul_pow _ (hKt k)
    have h2 : (T k).c ^ (L - a k) * (T k).c ^ a k = (T k).c ^ L := pow_sub_mul_pow _ (haL k)
    have h3 : dc k ^ (L - r) * dc k ^ r = dc k ^ L := pow_sub_mul_pow _ ((hra k).trans (haL k))
    rw [mul_pow, mul_pow, ← h1, ← h2, ← h3]
    ring

/-! ## C3: the `ν` identities of a chart, transferred to its pieces -/

/-- **Head data of a chart**: head coordinates `x (hd q)` with weights `w q`, and the two
identities of §2.3 with multiplier a power of the chart denominator `c`:
`c^s x_q^a ≡ Σ_γ c_γ g^γ` (`a w_q ≤ γ·d`, `γ ≠ 0`) and `c^s gᵢ ≡ Σ_α b_α x_head^α`
(`dᵢ ≤ w·α`). -/
structure ChartHead (T : ChartData G) {ι : Type} [Fintype ι] (g : ι → MvPolynomial (Fin (m + n)) ℤ) (d : ι → ℕ)
    (kc : ℕ) where
  hd : Fin kc → Fin n
  hd_inj : Function.Injective hd
  w : Fin kc → ℕ
  hw : ∀ q, w q ≠ 0
  la : Fin kc → ℕ
  ls : Fin kc → ℕ
  lΓ : Fin kc → Finset (ι → ℕ)
  lc : Fin kc → (ι → ℕ) → MvPolynomial (Fin (m + n)) ℤ
  lhom : ∀ q, ∀ γ ∈ lΓ q, la q * w q ≤ ∑ j, γ j * d j
  lne : ∀ q, ∀ γ ∈ lΓ q, ∑ j, γ j ≠ 0
  lid : ∀ q, T.c ^ ls q * T.x (hd q) ^ la q - ∑ γ ∈ lΓ q, lc q γ * ∏ j, g j ^ γ j ∈ lspan G
  hs : ι → ℕ
  hΓ : ι → Finset (Fin kc → ℕ)
  hb : ι → (Fin kc → ℕ) → MvPolynomial (Fin (m + n)) ℤ
  hdeg : ∀ i, ∀ α ∈ hΓ i, d i ≤ ∑ q, w q * α q
  hid : ∀ i, T.c ^ hs i * g i - ∑ α ∈ hΓ i, hb i α * ∏ q, T.x (hd q) ^ α q ∈ lspan G

/-- **Transfer of a multiplier**: `h ≡ Y c` and `cˢ X ≡ Z` give `hˢ X ≡ Yˢ Z`. -/
lemma transfer_mult {h Y c X Z : MvPolynomial (Fin (m + n)) ℤ} (s : ℕ) (hh : h - Y * c ∈ lspan G)
    (hX : c ^ s * X - Z ∈ lspan G) : h ^ s * X - Y ^ s * Z ∈ lspan G := by
  apply mem_of_quot_eq
  have e1 := quot_eq_of_mem hh
  have e2 := quot_eq_of_mem hX
  rw [map_mul, map_pow, e1, map_mul, map_mul, map_pow, ← e2, map_mul, map_pow]
  ring

/-! ## C4: the certified push-off data and chain lifting -/

/-- **Chain lifting for a torsor step from chart certificates.** The step is given by its
`OffStep` (the torsor presentation; its real points over `PtG G`), with filtration generators the
integer polynomials `g`. The charts `T k` carry chart data, a conormal multiplier `dc k`, and head
data; together with the filtration generators their multipliers form a linear partition of unity
`C₀ ≡ Σ bᵢ gᵢ + Σ eₖ cₖ dcₖ`. -/
theorem ChainLift.of_charts {N' : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (hn : 0 < n)
    {kc : ℕ} (hk : 2 ≤ kc) (O : OffStep (m + n) N' ι) (hPt : O.Pt = PtG G) (g : ι → MvPolynomial (Fin (m + n)) ℤ)
    (hg : O.g = fun i w => evalR w (g i)) {K : ℕ} (T : Fin K → ChartData G) (dc : Fin K → MvPolynomial (Fin (m + n)) ℤ)
    (hinj : ∀ k, ConormalInj G (dc k)) (H : ∀ k, ChartHead (T k) g O.d kc) (C₀ : ℕ)
    (hC₀ : 0 < C₀) (b : ι → MvPolynomial (Fin (m + n)) ℤ) (e : Fin K → MvPolynomial (Fin (m + n)) ℤ)
    (hcov : (C₀ : MvPolynomial (Fin (m + n)) ℤ) - (∑ i, b i * g i + ∑ k, e k * (T k).c * dc k) ∈ lspan G) :
    ChainLift O.Pt O.Pt' O.π := by
  obtain ⟨P, C, cb, ca, hC, hF, hh, hcid⟩ := glue_cover hn T dc hinj g C₀ hC₀ b e hcov
  set r := G.length
  set Y : Fin K × ChartData.MinorIdx (m := m) (n := n) G → MvPolynomial (Fin (m + n)) ℤ := fun p =>
    (T p.1).Δ (ChartData.subEnum p.2) ^ (2 * r + 1) *
      ((T p.1).c ^ (n - 1 + r * (n + 1)) * dc p.1 ^ r)
  have hY : ∀ p, (P p).h - Y p * (T p.1).c ∈ lspan G := fun p => by
    have e : Y p * (T p.1).c = (T p.1).Δ (ChartData.subEnum p.2) ^ (2 * r + 1) *
        ((T p.1).c ^ (n + r * (n + 1)) * dc p.1 ^ r) := by
      simp only [Y]
      have : n + r * (n + 1) = (n - 1 + r * (n + 1)) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [e]; exact hh p
  have hx : ∀ p q, (P p).F (Fin.natAdd m ((H p.1).hd q)) = (T p.1).x ((H p.1).hd q) :=
    fun p q => by rw [hF p]; simp
  let CP : CertPush m n G := {
    ι := ι
    g := g
    d := O.d
    E := O.E
    D₂ := O.D₂
    hD := O.hD
    hEd := O.hEd
    hE := O.hE
    J := Fin K × ChartData.MinorIdx (m := m) (n := n) G
    piece := P
    k := kc
    hk := hk
    hd := fun p => (H p.1).hd
    hd_inj := fun p => (H p.1).hd_inj
    w := fun p => (H p.1).w
    hw := fun p => (H p.1).hw
    la := fun p => (H p.1).la
    ls := fun p => (H p.1).ls
    lΓ := fun p => (H p.1).lΓ
    lc := fun p q γ => Y p ^ (H p.1).ls q * (H p.1).lc q γ
    lhom := fun p => (H p.1).lhom
    lne := fun p => (H p.1).lne
    lid := fun p q => by
      rw [hx p q]
      have := transfer_mult ((H p.1).ls q) (hY p) ((H p.1).lid q)
      convert this using 2
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun γ _ => by ring
    hs := fun p => (H p.1).hs
    hΓ := fun p => (H p.1).hΓ
    hb := fun p i α => Y p ^ (H p.1).hs i * (H p.1).hb i α
    hdeg := fun p => (H p.1).hdeg
    hid := fun p i => by
      have := transfer_mult ((H p.1).hs i) (hY p) ((H p.1).hid i)
      convert this using 2
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by simp only [hx]; ring
    cb := cb
    ca := ca
    C0 := C
    hC0 := hC
    cid := hcid }
  exact ChainLift.torsor_cert CP O hPt hg rfl

end BezoutCounterexample.Constructive
