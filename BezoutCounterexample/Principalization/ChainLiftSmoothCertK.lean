import Mathlib
import BezoutCounterexample.Principalization.ChainLiftSmoothChart
import BezoutCounterexample.Principalization.ChartDim
import BezoutCounterexample.Constructive.ChainLiftJouCert

/-!
# The Jacobian criterion in certificate form (K item, trusted primitive)

`exists_smoothCert_of_smooth`: a smooth `ℚ`-domain with an explicit presentation and a chart of
size `n > 0` at one prime has a smoothness certificate of dimension `n` (`ChartDim B n`).

**Status: K item** (a known constructive fact, trusted primitive `@[cprim]`, classical Lean proof).
References: the Jacobian criterion and local structure of smooth algebras, Stacks 00TA, 00T7,
07BU; constructively, Lombardi–Quitté, *Commutative Algebra: Constructive Methods*, Ch. VI–VIII
(finitely presented projective modules of constant rank over a domain, local freeness).
Constructive reading: `Ω_{B/ℚ}` is finitely generated projective; over a domain its rank is
constant, and the chart fixes it to `n`; the conormal sequence splits, which gives local
relations with a unit Jacobian minor generating the ideal on basic opens, and finitely many
basic opens cover.

**Why the hypotheses have this form** (design note `docs/pending/taskB-wish4-design.md`):
the dimension is pinned by *one chart at one prime*, not by `ringKrullDim B = n`, because at
the use site (`chartDim_U`) the hypotheses must be available constructively; a classical
`ringKrullDim_U` would bring R5 (Krull dimension theory), which is to leave the cone entirely.
`[Algebra.Smooth ℚ B]` is also supplied classically at the use site today (`torsor_smooth`, via
`rees_smooth` with Zorn and the `ChainLiftSmoothK` cprims); this is accepted because those
steps are already scheduled for removal (Task C replaces `span_eq_top_of_forall_isMaximal`; the
Rees layer of wish 4 removes the cprims). `0 < n` is needed: a `SmoothCert` of dimension `0`
has no pieces, so `ChartDim B 0` is false for every domain.

Proof (classical, all inside this file; the helpers are used only here):
* `mem_mul_of_pderiv_mem` (split conormal sequence), `exists_smul_le` (Cayley–Hamilton),
  `exists_minor`, `exists_local_jacobian`: the local Jacobian criterion for a fixed
  presentation;
* `exists_clear`, `exists_int_mem`, `exists_pieceData`: integer data;
* `pieceOf`, `PieceData.toPiece`: the square pieces (minor columns, then the complementary
  coordinates);
* `dim_eq_of_piece`, `lt_of_chart`, `piece_dim_eq`: every piece has `n` coordinates;
* `chartDim_of_cover`: gluing over a finite cover.
-/

set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial KaehlerDifferential TensorProduct BezoutCounterexample.Constructive
  BezoutCounterexample.Principalization

namespace BezoutCounterexample.Principalization.SmoothCertK

variable {N : ℕ}


lemma D_eq_sum (x : MvPolynomial (Fin N) ℚ) :
    D ℚ (MvPolynomial (Fin N) ℚ) x = ∑ j, pderiv j x • D ℚ (MvPolynomial (Fin N) ℚ) (X j) := by
  apply (mvPolynomialBasis ℚ (Fin N)).repr.injective
  ext i
  simp [map_sum, Finsupp.single_apply]

/-- **(F1)** For a smooth quotient `ℚ[Y]/I` and a prime `Q ⊇ I`: an element of `I` all of whose
partial derivatives lie in `Q` lies in `Q · I` (split conormal sequence). -/
theorem mem_mul_of_pderiv_mem (I Q : Ideal (MvPolynomial (Fin N) ℚ)) (hIQ : I ≤ Q)
    [Algebra.FormallySmooth ℚ (MvPolynomial (Fin N) ℚ ⧸ I)] {x : MvPolynomial (Fin N) ℚ}
    (hx : x ∈ I) (hd : ∀ j, pderiv j x ∈ Q) : x ∈ Q * I := by
  classical
  let K := RingHom.ker (algebraMap (MvPolynomial (Fin N) ℚ) (MvPolynomial (Fin N) ℚ ⧸ I))
  have hK : K = I := Ideal.mk_ker
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := ℚ)
    (P := MvPolynomial (Fin N) ℚ) (A := MvPolynomial (Fin N) ℚ ⧸ I)
    Ideal.Quotient.mk_surjective).1 inferInstance
  have hxK : x ∈ K := hK ▸ hx
  choose y hy using fun j : Fin N =>
    Ideal.toCotangent_surjective K (l (1 ⊗ₜ D ℚ (MvPolynomial (Fin N) ℚ) (X j)))
  have key : K.toCotangent ⟨x, hxK⟩ = K.toCotangent (∑ j, pderiv j x • y j) := by
    have h1 := congrArg (fun f => f (K.toCotangent ⟨x, hxK⟩)) hl
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [← h1]
    erw [kerCotangentToTensor_toCotangent]
    rw [D_eq_sum, tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tmul_smul, map_smul, map_smul, hy]
  rw [Ideal.toCotangent_eq] at key
  have hmem : (∑ j, pderiv j x • y j : K).1 ∈ Q * I := by
    rw [Submodule.coe_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Submodule.coe_smul, smul_eq_mul]
    exact Ideal.mul_mem_mul (hd j) (hK ▸ (y j).2)
  have hsq : K ^ 2 ≤ Q * I := by
    rw [hK, pow_two]; exact Ideal.mul_mono_left hIQ
  have := Ideal.add_mem _ (hsq key) hmem
  simpa using this

/-- `eval t p ∉ Q` for `p` monic with lower coefficients in `Q` and `t ∉ Q`. -/
lemma eval_notMem {R : Type*} [CommRing R] (Q : Ideal R) [Q.IsPrime] {t : R} (ht : t ∉ Q)
    {p : Polynomial R} (hp : p.Monic) (hc : ∀ k, p.coeff k ∈ Q ^ (p.natDegree - k)) :
    p.eval t ∉ Q := by
  intro hs
  have hlow : p.eval t - t ^ p.natDegree ∈ Q := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul,
      add_sub_cancel_right]
    refine Ideal.sum_mem _ fun k hk => Ideal.mul_mem_right _ _ ?_
    have hk' : 1 ≤ p.natDegree - k := by rw [Finset.mem_range] at hk; omega
    exact Ideal.pow_le_self (by omega) (hc k)
  have : t ^ p.natDegree ∈ Q := by
    have := Q.sub_mem hs hlow
    rwa [sub_sub_cancel] at this
  exact ht (‹Q.IsPrime›.mem_of_pow_mem _ this)

/-- **(F3)**, module form: if `t · M ⊆ L + Q · M` with `t ∉ Q`, then `s · M ⊆ L` for some
`s ∉ Q` (Cayley–Hamilton on `M / L`). -/
lemma exists_smul_le_module {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (Q : Ideal R) [Q.IsPrime] (L : Submodule R M) {t : R} (ht : t ∉ Q)
    (hle : ∀ m : M, t • m ∈ L ⊔ Q • ⊤) : ∃ s ∉ Q, ∀ m : M, s • m ∈ L := by
  classical
  have hrange : LinearMap.range (t • LinearMap.id : Module.End R (M ⧸ L)) ≤ Q • ⊤ := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨m, rfl⟩ := L.mkQ_surjective m
    obtain ⟨n, hn, y, hy, hxy⟩ := Submodule.mem_sup.1 (hle m)
    have h1 : (t • LinearMap.id : Module.End R (M ⧸ L)) (L.mkQ m) = L.mkQ y := by
      rw [LinearMap.smul_apply, LinearMap.id_apply, ← map_smul, ← hxy, map_add,
        show L.mkQ n = 0 from (Submodule.Quotient.mk_eq_zero L).2 hn, zero_add]
    rw [h1]
    have h2 : (Q • ⊤ : Submodule R M).map L.mkQ ≤ Q • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact h2 ⟨y, hy, rfl⟩
  obtain ⟨p, hp, -, hc, hev⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero (f := _) (I := Q) (hI := hrange)
  refine ⟨p.eval t, eval_notMem Q ht hp hc, fun m => ?_⟩
  have h1 : (t • LinearMap.id : Module.End R (M ⧸ L)) = algebraMap R (Module.End R (M ⧸ L)) t := by
    rw [Module.algebraMap_end_eq_smul_id]
  rw [h1, Polynomial.aeval_algebraMap_apply] at hev
  have h2 := congrArg (fun φ : Module.End R (M ⧸ L) => φ (L.mkQ m)) hev
  simp only [Module.algebraMap_end_apply, LinearMap.zero_apply, ← map_smul] at h2
  exact (Submodule.Quotient.mk_eq_zero L).1 h2

/-- **(F3)** for ideals: if `t · I ⊆ N' + Q · I` with `t ∉ Q`, then `s · I ⊆ N'`, `s ∉ Q`. -/
lemma exists_smul_le {R : Type*} [CommRing R] [IsNoetherianRing R] (I Q N' : Ideal R)
    [Q.IsPrime] {t : R} (ht : t ∉ Q) (hle : ∀ x ∈ I, t * x ∈ N' ⊔ Q * I) :
    ∃ s ∉ Q, ∀ x ∈ I, s * x ∈ N' := by
  have hQI : ∀ y ∈ Q * I, ∃ z ∈ (Q • (⊤ : Submodule R (I : Submodule R R))), (z : R) = y := by
    intro y hy
    have : (Q • (⊤ : Submodule R (I : Submodule R R))).map (Submodule.subtype (I : Submodule R R)) = Q * I := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]; rfl
    rw [← this] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, rfl⟩
  obtain ⟨s, hs, hsI⟩ := exists_smul_le_module (M := (I : Submodule R R)) Q
    (Submodule.comap (Submodule.subtype (I : Submodule R R)) (N' : Submodule R R)) ht (by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn, y, hy, hxy⟩ := Submodule.mem_sup.1 (hle x hx)
    obtain ⟨z, hz, hzy⟩ := hQI y hy
    have hyI : y ∈ I := hzy ▸ z.2
    refine Submodule.mem_sup.2 ⟨⟨n, ?_⟩, ?_, z, hz, ?_⟩
    · have : n = t * x - y := by rw [← hxy]; ring
      rw [this]; exact I.sub_mem (I.mul_mem_left t hx) hyI
    · exact hn
    · ext; simp [hzy, ← hxy])
  exact ⟨s, hs, fun x hx => hsI ⟨x, hx⟩⟩

/-- **(F4)** `c` linearly independent rows in `K^N` have a nonsingular `c × c` minor. -/
lemma exists_minor {K : Type*} [Field K] {c : ℕ} (v : Fin c → Fin N → K)
    (hv : LinearIndependent K v) :
    ∃ J : Fin c → Fin N, Function.Injective J ∧ (Matrix.of fun i k => v i (J k)).det ≠ 0 := by
  classical
  let M : Matrix (Fin c) (Fin N) K := Matrix.of v
  have hrank : Module.finrank K (Submodule.span K (Set.range M.col)) = c := by
    rw [← Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_row]
    exact (finrank_span_eq_card hv).trans (Fintype.card_fin c)
  have htop : Submodule.span K (Set.range M.col) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hrank, Module.finrank_fin_fun])
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K M.col
  haveI : Fintype κ := by
    haveI := hli.finite; exact Fintype.ofFinite κ
  have hcard : Fintype.card κ = c := by
    rw [← finrank_span_eq_card hli, hsp, htop, finrank_top, Module.finrank_fin_fun]
  let e : κ ≃ Fin c := Fintype.equivFinOfCardEq hcard
  refine ⟨a ∘ e.symm, ha.comp e.symm.injective, ?_⟩
  have hu : IsUnit (Matrix.of fun i k => v i ((a ∘ e.symm) k)) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have : (Matrix.of fun i k => v i ((a ∘ e.symm) k)).col = (M.col ∘ a) ∘ e.symm := by
      ext k i; rfl
    rw [this]; exact hli.comp _ e.symm.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

/-- **The local Jacobian criterion** for a fixed presentation `ℚ[Y]/I` (smooth): at a prime
`Q ⊇ I` there are relations `f₁ … f_c ∈ I`, columns `J`, and `s ∉ Q` with a minor
`det (∂f_i/∂Y_{J k}) ∉ Q` and `s · I ⊆ (f)`. -/
theorem exists_local_jacobian (I Q : Ideal (MvPolynomial (Fin N) ℚ)) [Q.IsPrime] (hIQ : I ≤ Q)
    [Algebra.FormallySmooth ℚ (MvPolynomial (Fin N) ℚ ⧸ I)] :
    ∃ (c : ℕ) (f : Fin c → MvPolynomial (Fin N) ℚ) (J : Fin c → Fin N)
      (s : MvPolynomial (Fin N) ℚ), Function.Injective J ∧ (∀ i, f i ∈ I) ∧ s ∉ Q ∧
      (Matrix.of fun i k => pderiv (J k) (f i)).det ∉ Q ∧
      ∀ x ∈ I, s * x ∈ Ideal.span (Set.range f) := by
  classical
  let K := FractionRing (MvPolynomial (Fin N) ℚ ⧸ Q)
  let π : MvPolynomial (Fin N) ℚ →+* K :=
    (algebraMap (MvPolynomial (Fin N) ℚ ⧸ Q) K).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ p, π p = 0 ↔ p ∈ Q := fun p => by
    simp only [π, RingHom.comp_apply]
    rw [(IsFractionRing.injective (MvPolynomial (Fin N) ℚ ⧸ Q) K).eq_iff' (map_zero _),
      Ideal.Quotient.eq_zero_iff_mem]
  let ψ : I → Fin N → K := fun x j => π (pderiv j x.1)
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' K ψ
  haveI : Fintype κ := by haveI := hli.finite; exact Fintype.ofFinite κ
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  set c := Fintype.card κ
  let f : Fin c → MvPolynomial (Fin N) ℚ := fun i => (a (e.symm i)).1
  let v : Fin c → Fin N → K := fun i => ψ (a (e.symm i))
  have hv : LinearIndependent K v := hli.comp _ e.symm.injective
  have hrange : Set.range v = Set.range (ψ ∘ a) := by
    ext w; constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨e k, by simp [v]⟩
  obtain ⟨J, hJ, hdet⟩ := exists_minor v hv
  -- the minor
  have hdetQ : (Matrix.of fun i k => pderiv (J k) (f i)).det ∉ Q := by
    rw [← hπ, RingHom.map_det]
    have : π.mapMatrix (Matrix.of fun i k => pderiv (J k) (f i)) = Matrix.of fun i k => v i (J k) := by
      ext; rfl
    rw [this]; exact hdet
  -- the spreading
  have hψmul : ∀ (p : MvPolynomial (Fin N) ℚ) (x : MvPolynomial (Fin N) ℚ), x ∈ I →
      ∀ j, π (pderiv j (p * x)) = π p * π (pderiv j x) := by
    intro p x hx j
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
      (hπ x).2 (hIQ hx), zero_mul, add_zero]
  have hgen : ∀ x ∈ I, ∃ σ : MvPolynomial (Fin N) ℚ, σ ∉ Q ∧
      σ * x ∈ Ideal.span (Set.range f) ⊔ Q * I := by
    intro x hx
    have hmem : ψ ⟨x, hx⟩ ∈ Submodule.span K (Set.range v) := by
      rw [hrange, hspan]; exact Submodule.subset_span ⟨_, rfl⟩
    obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples
      (nonZeroDivisors (MvPolynomial (Fin N) ℚ ⧸ Q)) Finset.univ lam
    choose α' hα' using fun i => hb i (Finset.mem_univ i)
    obtain ⟨σ, hσ⟩ := Ideal.Quotient.mk_surjective (b : MvPolynomial (Fin N) ℚ ⧸ Q)
    choose α hα using fun i => Ideal.Quotient.mk_surjective (α' i)
    have hπσ : π σ = algebraMap _ K (b : MvPolynomial (Fin N) ℚ ⧸ Q) := by
      simp [π, hσ]
    have hπα : ∀ i, π (α i) = (b : MvPolynomial (Fin N) ℚ ⧸ Q) • lam i := by
      intro i; simp only [π, RingHom.comp_apply, hα]; exact hα' i
    refine ⟨σ, fun h => ?_, ?_⟩
    · have := (hπ σ).2 h
      rw [hπσ] at this
      exact nonZeroDivisors.coe_ne_zero b
        ((IsFractionRing.injective _ K).eq_iff' (map_zero _) |>.1 this)
    · have hx' : σ * x - ∑ i, α i * f i ∈ Q * I := by
        refine mem_mul_of_pderiv_mem I Q hIQ
          (I.sub_mem (I.mul_mem_left _ hx) (I.sum_mem fun i _ => I.mul_mem_left _ (a _).2))
          fun j => (hπ _).1 ?_
        rw [map_sub, map_sum, map_sub, map_sum,
          Finset.sum_congr rfl fun i _ => hψmul (α i) (f i) (a (e.symm i)).2 j, hψmul σ x hx, hπσ]
        simp only [hπα]
        have := congrFun hlam j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        change algebraMap _ K (b : MvPolynomial (Fin N) ℚ ⧸ Q) * ψ ⟨x, hx⟩ j -
          ∑ i, (b : MvPolynomial (Fin N) ℚ ⧸ Q) • lam i * v i j = 0
        rw [← Algebra.smul_def, ← this]
        rw [sub_eq_zero]; exact Finset.smul_sum (r := (b : MvPolynomial (Fin N) ℚ ⧸ Q)) (s := Finset.univ) (f := fun i => lam i * v i j) |>.trans (Finset.sum_congr rfl fun i _ => (smul_mul_assoc _ _ _).symm)
      have h1 : ∑ i, α i * f i ∈ Ideal.span (Set.range f) :=
        Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
      have : σ * x = ∑ i, α i * f i + (σ * x - ∑ i, α i * f i) := by ring
      rw [this]
      exact Submodule.add_mem_sup h1 hx'
  -- the generators of `I`
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian I : I.FG)
  have hTI : ∀ x ∈ T, x ∈ I := fun x hx => hT ▸ Ideal.subset_span hx
  choose σ hσQ hσ using fun x : T => hgen x.1 (hTI x.1 x.2)
  let t := ∏ x : T, σ x
  have ht : t ∉ Q := by
    rw [Ideal.IsPrime.prod_mem_iff]; push Not; exact fun x _ => hσQ x
  have hle : ∀ x ∈ I, t * x ∈ Ideal.span (Set.range f) ⊔ Q * I := by
    intro x hx
    rw [← hT] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have : t = (∏ y ∈ Finset.univ.erase ⟨x, hx⟩, σ y) * σ ⟨x, hx⟩ :=
        (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
      rw [this, mul_assoc]
      exact Ideal.mul_mem_left _ _ (hσ ⟨x, hx⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
    | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx
  obtain ⟨s, hs, hsI⟩ := exists_smul_le I Q _ ht hle
  exact ⟨c, f, J, s, hJ, fun i => (a (e.symm i)).2, hs, hdetQ, hsI⟩

/-! ### Clearing denominators -/

lemma exists_clear {σ : Type*} (p : MvPolynomial σ ℚ) :
    ∃ (D : ℕ) (q : MvPolynomial σ ℤ), 0 < D ∧ toQZ q = (D : MvPolynomial σ ℚ) * p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    refine ⟨a.den, monomial s a.num, a.den_pos, ?_⟩
    rw [toQZ, map_monomial, show ((a.den : ℕ) : MvPolynomial σ ℚ) = C (a.den : ℚ) by simp,
      C_mul_monomial]
    congr 1
    simp [Rat.den_mul_eq_num]
  | add p q hp hq =>
    obtain ⟨D₁, q₁, hD₁, h₁⟩ := hp
    obtain ⟨D₂, q₂, hD₂, h₂⟩ := hq
    refine ⟨D₁ * D₂, (D₂ : MvPolynomial σ ℤ) * q₁ + (D₁ : MvPolynomial σ ℤ) * q₂,
      Nat.mul_pos hD₁ hD₂, ?_⟩
    simp only [map_add, map_mul, map_natCast, h₁, h₂]
    push_cast; ring

lemma toQZ_injective {σ : Type*} : Function.Injective (toQZ : MvPolynomial σ ℤ → _) :=
  MvPolynomial.map_injective _ (RingHom.injective_int _)

/-- An integer polynomial whose image lies in the extension of an ideal `J` of `ℤ[Y]` has a
positive integer multiple in `J`. -/
lemma exists_int_mem {σ : Type*} (J : Ideal (MvPolynomial σ ℤ)) {q : MvPolynomial σ ℤ}
    (hq : toQZ q ∈ J.map toQZ) : ∃ D : ℕ, 0 < D ∧ (D : MvPolynomial σ ℤ) * q ∈ J := by
  have key : ∀ y ∈ J.map (toQZ : MvPolynomial σ ℤ →+* _),
      ∃ (D : ℕ) (z : MvPolynomial σ ℤ), 0 < D ∧ z ∈ J ∧ toQZ z = (D : MvPolynomial σ ℚ) * y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨1, z, one_pos, hz, by simp⟩
    | zero => exact ⟨1, 0, one_pos, J.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨D₁, z₁, hD₁, hz₁, h₁⟩ := hx
      obtain ⟨D₂, z₂, hD₂, hz₂, h₂⟩ := hy
      refine ⟨D₁ * D₂, (D₂ : MvPolynomial σ ℤ) * z₁ + (D₁ : MvPolynomial σ ℤ) * z₂,
        Nat.mul_pos hD₁ hD₂, J.add_mem (J.mul_mem_left _ hz₁) (J.mul_mem_left _ hz₂), ?_⟩
      simp only [map_add, map_mul, map_natCast, h₁, h₂]
      push_cast; ring
    | smul r x _ hx =>
      obtain ⟨D₁, z₁, hD₁, hz₁, h₁⟩ := hx
      obtain ⟨D₂, r', hD₂, h₂⟩ := exists_clear r
      refine ⟨D₂ * D₁, r' * z₁, Nat.mul_pos hD₂ hD₁, J.mul_mem_left _ hz₁, ?_⟩
      rw [map_mul, h₁, h₂, smul_eq_mul]
      push_cast; ring
  obtain ⟨D, z, hD, hz, h⟩ := key _ hq
  refine ⟨D, hD, ?_⟩
  have : z = (D : MvPolynomial σ ℤ) * q := toQZ_injective (by rw [h, map_mul, map_natCast])
  rwa [← this]

lemma lspan_map_toQZ {σ : Type*} (G : List (MvPolynomial σ ℤ)) :
    lspan (G.map toQZ) = (lspan G).map toQZ := by
  rw [lspan, lspan, Ideal.map_span]
  congr 1
  ext x; simp

/-! ### Renaming variables -/

lemma rename_mem {σ τ : Type*} {G : List (MvPolynomial σ ℤ)} (e : σ → τ) {p : MvPolynomial σ ℤ}
    (hp : p ∈ lspan G) : rename e p ∈ lspan (G.map (rename e)) := by
  have h1 : (lspan G).map (rename e) ≤ lspan (G.map (rename e)) := by
    rw [lspan, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact Ideal.subset_span (List.mem_map_of_mem hg)
  exact h1 (Ideal.mem_map_of_mem _ hp)

lemma rename_mem_ofFn {σ τ : Type*} {k : ℕ} {L : Fin k → MvPolynomial σ ℤ} (e : σ → τ)
    {p : MvPolynomial σ ℤ} (hp : p ∈ lspan (List.ofFn L)) {L' : List (MvPolynomial τ ℤ)}
    (hL : ∀ i, rename e (L i) ∈ L') : rename e p ∈ lspan L' := by
  have h1 : (lspan (List.ofFn L)).map (rename e) ≤ lspan L' := by
    rw [lspan, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
    exact Ideal.subset_span (hL i)
  exact h1 (Ideal.mem_map_of_mem _ hp)

/-! ### A square piece from local Jacobian data -/

section OfLocal

variable {N m n : ℕ}

/-- The variables: the minor's columns `J`, then the complement. -/
noncomputable def colEquiv (J : Fin m → Fin (m + n)) (hJ : Function.Injective J) :
    Fin m ⊕ Fin n ≃ Fin (m + n) := by
  classical
  have hcard : Fintype.card (Fin n) = Fintype.card {x : Fin (m + n) // x ∉ Set.range J} := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_fin,
      Set.card_range_of_injective hJ, Fintype.card_fin]; omega
  exact (Equiv.sumCongr (Equiv.ofInjective J hJ) (Fintype.equivOfCardEq hcard)).trans
    (Equiv.sumCompl fun x => x ∈ Set.range J)

lemma colEquiv_inl (J : Fin m → Fin (m + n)) (hJ : Function.Injective J) (k : Fin m) :
    colEquiv J hJ (Sum.inl k) = J k := by
  simp [colEquiv]

/-- The rows of the piece: the relations, then the complementary coordinates. -/
noncomputable def rowsOf (f : Fin m → MvPolynomial (Fin (m + n)) ℤ) (J : Fin m → Fin (m + n))
    (hJ : Function.Injective J) : Fin m ⊕ Fin n → MvPolynomial (Fin (m + n)) ℤ :=
  Sum.elim f fun j => X (colEquiv J hJ (Sum.inr j))

lemma det_rowsOf (f : Fin m → MvPolynomial (Fin (m + n)) ℤ) (J : Fin m → Fin (m + n))
    (hJ : Function.Injective J) :
    (Matrix.of fun a b => pderiv (colEquiv J hJ b) (rowsOf f J hJ a)).det =
      (Matrix.of fun i k => pderiv (J k) (f i)).det := by
  classical
  set M := Matrix.of fun a b => pderiv (colEquiv J hJ b) (rowsOf f J hJ a)
  have h21 : M.toBlocks₂₁ = 0 := by
    ext j k
    simp only [M, Matrix.toBlocks₂₁, Matrix.of_apply, rowsOf, Sum.elim_inr, pderiv_X,
      Pi.single_apply, Matrix.zero_apply]
    rw [if_neg]
    intro h; exact Sum.inl_ne_inr ((colEquiv J hJ).injective h).symm
  have h22 : M.toBlocks₂₂ = 1 := by
    ext j l
    simp only [M, Matrix.toBlocks₂₂, Matrix.of_apply, rowsOf, Sum.elim_inr, pderiv_X,
      Pi.single_apply, Matrix.one_apply, (colEquiv J hJ).injective.eq_iff, Sum.inr.injEq]
  have h11 : M.toBlocks₁₁ = Matrix.of fun i k => pderiv (J k) (f i) := by
    ext i k
    simp [M, Matrix.toBlocks₁₁, rowsOf, colEquiv_inl]
  rw [← Matrix.fromBlocks_toBlocks M, h21, Matrix.det_fromBlocks_zero₂₁, h11, h22,
    Matrix.det_one, mul_one]

/-- **A square piece from local Jacobian data** (already renamed to `Fin (m + n)`). -/
noncomputable def pieceOf (G : List (MvPolynomial (Fin (m + n)) ℤ)) (hn : 0 < n)
    (f : Fin m → MvPolynomial (Fin (m + n)) ℤ) (hf : ∀ i, f i ∈ lspan G)
    (J : Fin m → Fin (m + n)) (hJ : Function.Injective J) (h U : MvPolynomial (Fin (m + n)) ℤ)
    (hdet : (Matrix.of fun i k => pderiv (J k) (f i)).det * U - h ∈ lspan G)
    (hgen : ∀ g ∈ G, h * g ∈ lspan (List.ofFn f)) : SquarePiece m n G where
  F := rowsOf f J hJ ∘ finSumFinEquiv.symm
  hn := hn
  eqmem i := by simpa [rowsOf] using hf i
  h := h
  e := 1
  f := 1
  U := (((Equiv.Perm.sign ((colEquiv J hJ).symm.symm.trans finSumFinEquiv.symm) : ℤˣ) : ℤ) :
      MvPolynomial (Fin (m + n)) ℤ) * U
  detc := by
    classical
    set s : MvPolynomial (Fin (m + n)) ℤ :=
      (((Equiv.Perm.sign ((colEquiv J hJ).symm.symm.trans finSumFinEquiv.symm) : ℤˣ) : ℤ) :
        MvPolynomial (Fin (m + n)) ℤ)
    have hjac : jacPoly (rowsOf f J hJ ∘ finSumFinEquiv.symm) =
        (Matrix.of fun a b => pderiv (colEquiv J hJ b) (rowsOf f J hJ a)).submatrix
          finSumFinEquiv.symm (colEquiv J hJ).symm := by
      ext i v; simp [jacPoly]
    have hs : s * s = 1 := by
      simp only [s, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
        Int.cast_one]
    rw [hjac, JouCert.det_submatrix_equiv_equiv, det_rowsOf, pow_one]
    have : s * (Matrix.of fun i k => pderiv (J k) (f i)).det * (s * U) - h =
        (s * s) * ((Matrix.of fun i k => pderiv (J k) (f i)).det * U) - h := by ring
    rw [this, hs, one_mul]; exact hdet
  genc g hg := by
    rw [pow_one]
    refine (Ideal.span_mono ?_) (hgen g hg)
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact List.mem_ofFn.2 ⟨i, by simp [rowsOf]⟩

end OfLocal

/-- Integer local Jacobian data for a presentation `G` (any number of relations `c`). -/
structure PieceData (N : ℕ) (G : List (MvPolynomial (Fin N) ℤ)) where
  c : ℕ
  f : Fin c → MvPolynomial (Fin N) ℤ
  hf : ∀ i, f i ∈ lspan G
  J : Fin c → Fin N
  hJ : Function.Injective J
  h : MvPolynomial (Fin N) ℤ
  U : MvPolynomial (Fin N) ℤ
  hdet : (Matrix.of fun i k => pderiv (J k) (f i)).det * U - h ∈ lspan G
  hgen : ∀ g ∈ G, h * g ∈ lspan (List.ofFn f)

/-- The square piece of `PieceData` with `c = m`. -/
noncomputable def PieceData.toPiece {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}
    (D : PieceData (m + n) G) (hc : D.c = m) (hn : 0 < n) : SquarePiece m n G :=
  pieceOf G hn (D.f ∘ Fin.cast hc.symm) (fun i => D.hf _) (D.J ∘ Fin.cast hc.symm)
    (D.hJ.comp (Fin.cast_injective _)) D.h D.U
    (by
      have : (Matrix.of fun i k => pderiv ((D.J ∘ Fin.cast hc.symm) k)
          ((D.f ∘ Fin.cast hc.symm) i)) =
          (Matrix.of fun i k => pderiv (D.J k) (D.f i)).submatrix (finCongr hc.symm)
            (finCongr hc.symm) := by ext; rfl
      rw [this, Matrix.det_submatrix_equiv_self]; exact D.hdet)
    (fun g hg => by
      refine (Ideal.span_mono ?_) (D.hgen g hg)
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact List.mem_ofFn.2 ⟨Fin.cast hc i, by simp⟩)

@[simp] lemma PieceData.toPiece_h {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}
    (D : PieceData (m + n) G) (hc : D.c = m) (hn : 0 < n) : (D.toPiece hc hn).h = D.h := rfl

lemma D_eq_sum' {N : ℕ} (x : MvPolynomial (Fin N) ℚ) :
    KaehlerDifferential.D ℚ (MvPolynomial (Fin N) ℚ) x =
      ∑ j, pderiv j x • KaehlerDifferential.D ℚ (MvPolynomial (Fin N) ℚ) (X j) := by
  apply (KaehlerDifferential.mvPolynomialBasis ℚ (Fin N)).repr.injective
  ext i
  simp [map_sum, Finsupp.single_apply]

/-- A chart on `R_M` gives one on `R_{M'}` for `M ≤ M'`. -/
noncomputable def chartLe {R : Type*} [CommRing R] [Algebra ℚ R] {M M' : Submonoid R}
    (hle : M ≤ M') {n : ℕ} (c : Chart (Localization M) n) : Chart (Localization M') n :=
  letI := IsLocalization.localizationAlgebraOfSubmonoidLe (Localization M) (Localization M') _ _ hle
  haveI := IsLocalization.localization_isScalarTower_of_submonoid_le (Localization M)
    (Localization M') _ _ hle
  haveI := IsLocalization.isLocalization_of_submonoid_le (Localization M) (Localization M') _ _ hle
  haveI : IsScalarTower ℚ (Localization M) (Localization M') :=
    IsScalarTower.of_algebraMap_eq fun q => by
      have := RingHom.ext_rat (algebraMap ℚ (Localization M'))
        ((algebraMap (Localization M) (Localization M')).comp (algebraMap ℚ (Localization M)))
      exact congrArg (fun f : ℚ →+* Localization M' => f q) this
  c.localization (M'.map (algebraMap R (Localization M)))

/-- **(G4)** A piece with `h ≠ 0` of a domain has the dimension of any chart. -/
theorem dim_eq_of_piece {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}
    (S : SquarePiece m n G) [IsDomain (SmoothCert.QB G)] (hh : SquarePiece.mkQ G S.h ≠ 0)
    {B : Type} [CommRing B] [Algebra ℚ B] (eB : SmoothCert.QB G ≃+* B) (𝔭 : Ideal B)
    [𝔭.IsPrime] {n₀ : ℕ} (c : Chart (Localization.AtPrime 𝔭) n₀) : n = n₀ := by
  haveI : (⊥ : Ideal (SmoothCert.QB G)).IsPrime := Ideal.isPrime_bot
  have h1 : Submonoid.powers (SquarePiece.mkQ G S.h) ≤ (⊥ : Ideal (SmoothCert.QB G)).primeCompl :=
    (Submonoid.powers_le).2 fun h0 => hh (Ideal.mem_bot.1 h0)
  haveI := Ideal.comap_isPrime (eB : SmoothCert.QB G →+* B) 𝔭
  have h2 : (𝔭.comap (eB : SmoothCert.QB G →+* B)).primeCompl ≤
      (⊥ : Ideal (SmoothCert.QB G)).primeCompl := fun x hx h0 => by
    rw [Ideal.mem_bot.1 h0] at hx; exact hx (Ideal.zero_mem _)
  exact Chart.card_eq (chartLe h1 S.chart)
    (chartLe h2 (c.ofRingEquiv (ChartDim.locEquiv eB 𝔭).symm))

/-- A derivation of a localization vanishing on the base ring is zero. -/
lemma derivation_loc_eq_zero {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
    [Algebra R S] [IsScalarTower ℚ R S] (M : Submonoid R) [IsLocalization M S]
    (d : Derivation ℚ S S) (hd : ∀ r, d (algebraMap R S r) = 0) : d = 0 := by
  have hL : d.liftKaehlerDifferential = 0 := by
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_map_derivation_of_isLocalization
      ℚ R S M)
    intro r
    simp [KaehlerDifferential.map_D, hd]
  ext x
  rw [← Derivation.liftKaehlerDifferential_comp_D d, hL]; rfl

set_option maxHeartbeats 1000000 in
/-- **(G5)** Relations with a full nonsingular Jacobian contradict a chart of positive size at
the generic point: so `c < N`. -/
theorem lt_of_chart {N c : ℕ} {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A]
    (π : MvPolynomial (Fin N) ℚ →+* A) (hπ : Function.Surjective π)
    (f : Fin c → MvPolynomial (Fin N) ℚ) (hf : ∀ i, π (f i) = 0) (J : Fin c → Fin N)
    (hJ : Function.Injective J) (hdet : π (Matrix.of fun i k => pderiv (J k) (f i)).det ≠ 0)
    {n₀ : ℕ} (hn₀ : 0 < n₀) (c' : Chart (Localization.AtPrime (⊥ : Ideal A)) n₀) : c < N := by
  classical
  have hle : c ≤ N := by simpa using Fintype.card_le_of_injective J hJ
  refine lt_of_le_of_ne hle fun hcN => ?_
  subst hcN
  have hJb : Function.Bijective J := (Finite.injective_iff_bijective).1 hJ
  let φ : MvPolynomial (Fin c) ℚ →+* Localization.AtPrime (⊥ : Ideal A) :=
    (algebraMap A (Localization.AtPrime (⊥ : Ideal A))).comp π
  let d := c'.d ⟨0, hn₀⟩
  have hform : ∀ p, d (φ p) = ∑ j, φ (pderiv j p) * d (φ (X j)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have : φ (C a) = algebraMap ℚ (Localization.AtPrime (⊥ : Ideal A)) a :=
        congrFun (congrArg DFunLike.coe (Subsingleton.elim (φ.comp C)
          (algebraMap ℚ (Localization.AtPrime (⊥ : Ideal A))))) a
      rw [this, Derivation.map_algebraMap]; simp
    | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
    | mul_X p i hp =>
      rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp]
      have : ∀ j, φ (pderiv j (p * X i)) =
          φ p * (if i = j then 1 else 0) + φ (X i) * φ (pderiv j p) := by
        intro j
        rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
          Pi.single_apply]
        by_cases h : j = i
        · subst h; simp [add_comm]
        · simp [Ne.symm h, add_comm]
      simp only [this, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  let w : Fin c → Localization.AtPrime (⊥ : Ideal A) := fun j => d (φ (X j))
  let M : Matrix (Fin c) (Fin c) (Localization.AtPrime (⊥ : Ideal A)) :=
    Matrix.of fun i k => φ (pderiv (J k) (f i))
  have hMw : M.mulVec (w ∘ J) = 0 := by
    ext i
    have h0 : d (φ (f i)) = 0 := by
      rw [show φ (f i) = 0 by simp [φ, hf i], map_zero]
    rw [hform] at h0
    simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, Function.comp_apply, Pi.zero_apply]
    rw [← h0]
    exact (Equiv.ofBijective J hJb).sum_comp (fun j => φ (pderiv j (f i)) * w j)
  have hunit : IsUnit M.det := by
    have : M.det = φ (Matrix.of fun i k => pderiv (J k) (f i)).det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact IsLocalization.map_units _ (⟨π _, fun h0 => hdet (Ideal.mem_bot.1 h0)⟩ :
      (⊥ : Ideal A).primeCompl)
  have hw : w ∘ J = 0 := by
    have := congrArg (M⁻¹).mulVec hMw
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
  have hw' : ∀ j, w j = 0 := fun j => by
    obtain ⟨k, rfl⟩ := hJb.2 j; exact congrFun hw k
  have hφ0 : ∀ p, d (φ p) = 0 := fun p => by
    rw [hform]
    exact Finset.sum_eq_zero fun j _ => by rw [show d (φ (X j)) = w j from rfl, hw', mul_zero]
  have hd0 : d = 0 := by
    refine derivation_loc_eq_zero (⊥ : Ideal A).primeCompl d fun a => ?_
    obtain ⟨p, rfl⟩ := hπ a
    exact hφ0 p
  have := c'.d_x ⟨0, hn₀⟩ ⟨0, hn₀⟩
  rw [if_pos rfl] at this
  change d _ = 1 at this
  rw [hd0, Derivation.zero_apply] at this
  exact zero_ne_one this


lemma mem_of_natCast_mul {σ : Type*} {Q : Ideal (MvPolynomial σ ℚ)} {r : ℕ} (hr : 0 < r)
    {x : MvPolynomial σ ℚ} (h : (r : MvPolynomial σ ℚ) * x ∈ Q) : x ∈ Q := by
  have hx : x = C ((r : ℚ)⁻¹) * ((r : MvPolynomial σ ℚ) * x) := by
    rw [← mul_assoc, show (r : MvPolynomial σ ℚ) = C (r : ℚ) by simp, ← C_mul,
      inv_mul_cancel₀ (by exact_mod_cast hr.ne'), C_1, one_mul]
  rw [hx]; exact Q.mul_mem_left _ h

lemma toQZ_mem_lspan {σ : Type*} {G : List (MvPolynomial σ ℤ)} {p : MvPolynomial σ ℤ}
    (hp : p ∈ lspan G) : toQZ p ∈ lspan (G.map toQZ) := by
  rw [lspan_map_toQZ]; exact Ideal.mem_map_of_mem _ hp

/-- **Integer local data** at a prime `Q ⊇ (G)`. -/
theorem exists_pieceData (G : List (MvPolynomial (Fin N) ℤ)) (Q : Ideal (MvPolynomial (Fin N) ℚ))
    [Q.IsPrime] (hIQ : lspan (G.map toQZ) ≤ Q)
    [Algebra.FormallySmooth ℚ (MvPolynomial (Fin N) ℚ ⧸ lspan (G.map toQZ))] :
    ∃ D : PieceData N G, toQZ D.h ∉ Q ∧
      (Matrix.of fun i k => pderiv (D.J k) (toQZ (D.f i))).det ∉ lspan (G.map toQZ) := by
  classical
  set I := lspan (G.map toQZ) with hIdef
  have hI : I = (lspan G).map toQZ := lspan_map_toQZ G
  obtain ⟨c, f, J, s, hJ, hfI, hs, hdet, hsI⟩ := exists_local_jacobian I Q hIQ
  choose D q hD hq using fun i => exists_clear (f i)
  have hqI : ∀ i, toQZ (q i) ∈ (lspan G).map toQZ := fun i => by
    rw [hq i, ← hI]; exact I.mul_mem_left _ (hfI i)
  choose E hE hEq using fun i => exists_int_mem (lspan G) (hqI i)
  let f' : Fin c → MvPolynomial (Fin N) ℤ := fun i => (E i : MvPolynomial (Fin N) ℤ) * q i
  let u : Fin c → ℕ := fun i => E i * D i
  have hu : ∀ i, 0 < u i := fun i => Nat.mul_pos (hE i) (hD i)
  have hf' : ∀ i, toQZ (f' i) = (u i : MvPolynomial (Fin N) ℚ) * f i := fun i => by
    simp only [f', u, map_mul, map_natCast, hq]; push_cast; ring
  obtain ⟨Ds, s', hDs, hs'⟩ := exists_clear s
  have hspan : Ideal.span (Set.range f) ≤ (lspan (List.ofFn f')).map toQZ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hmem : toQZ (f' i) ∈ (lspan (List.ofFn f')).map toQZ :=
      Ideal.mem_map_of_mem _ (Ideal.subset_span (List.mem_ofFn.2 ⟨i, rfl⟩))
    rw [hf'] at hmem
    exact mem_of_natCast_mul (hu i) hmem
  have hg : ∀ g ∈ G, ∃ Dg : ℕ, 0 < Dg ∧
      (Dg : MvPolynomial (Fin N) ℤ) * (s' * g) ∈ lspan (List.ofFn f') := fun g hg =>
    exists_int_mem _ (by
      rw [map_mul, hs', mul_assoc]
      exact Ideal.mul_mem_left _ _ (hspan (hsI _ (Ideal.subset_span (List.mem_map_of_mem hg)))))
  choose Dg hDg hDgmem using hg
  let Dstar : ℕ := (G.attach.map fun g => Dg g.1 g.2).prod
  have hDstar : 0 < Dstar := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    obtain ⟨_, hx, hx0⟩ := List.mem_map.1 (List.prod_eq_zero_iff.1 h0)
    exact (hDg _ _).ne' hx0
  have hdvd : ∀ g (hg : g ∈ G), Dg g hg ∣ Dstar := fun g hg =>
    List.dvd_prod (List.mem_map.2 ⟨⟨g, hg⟩, List.mem_attach _ _, rfl⟩)
  let det' := (Matrix.of fun i k => pderiv (J k) (f' i)).det
  have hdet' : toQZ det' = ((∏ i, u i : ℕ) : MvPolynomial (Fin N) ℚ) *
      (Matrix.of fun i k => pderiv (J k) (f i)).det := by
    have h1 : toQZ det' = (Matrix.of fun i k => (u i : MvPolynomial (Fin N) ℚ) *
        pderiv (J k) (f i)).det := by
      rw [RingHom.map_det]; congr 1; ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      rw [show toQZ (pderiv (J k) (f' i)) = pderiv (J k) (toQZ (f' i)) from pderiv_map.symm, hf',
        show (u i : MvPolynomial (Fin N) ℚ) = C (u i : ℚ) from (map_natCast C _).symm,
        pderiv_C_mul]
    rw [h1]
    have := Matrix.det_mul_column (fun i => ((u i : ℕ) : MvPolynomial (Fin N) ℚ))
      (Matrix.of fun i k => pderiv (J k) (f i))
    simp only [Matrix.of_apply] at this
    rw [this]; push_cast; rfl
  refine ⟨⟨c, f', hEq, J, hJ, (Dstar : MvPolynomial (Fin N) ℤ) * s' * det',
    (Dstar : MvPolynomial (Fin N) ℤ) * s', ?_, ?_⟩, ?_, ?_⟩
  · have : det' * ((Dstar : MvPolynomial (Fin N) ℤ) * s') -
        (Dstar : MvPolynomial (Fin N) ℤ) * s' * det' = 0 := by ring
    rw [this]; exact Ideal.zero_mem _
  · intro g hg
    obtain ⟨k, hk⟩ := hdvd g hg
    have : (Dstar : MvPolynomial (Fin N) ℤ) * s' * det' * g =
        (det' * k) * ((Dg g hg : MvPolynomial (Fin N) ℤ) * (s' * g)) := by
      rw [show (Dstar : MvPolynomial (Fin N) ℤ) = (Dg g hg : MvPolynomial (Fin N) ℤ) * k by
        rw [hk]; push_cast; ring]
      ring
    rw [this]; exact Ideal.mul_mem_left _ _ (hDgmem g hg)
  · intro hmem
    have : ((Dstar * Ds * ∏ i, u i : ℕ) : MvPolynomial (Fin N) ℚ) *
        (s * (Matrix.of fun i k => pderiv (J k) (f i)).det) ∈ Q := by
      convert hmem using 1
      simp only [map_mul, map_natCast, hs', hdet']; push_cast; ring
    have hpos : 0 < Dstar * Ds * ∏ i, u i :=
      Nat.mul_pos (Nat.mul_pos hDstar hDs) (Finset.prod_pos fun i _ => hu i)
    rcases ‹Q.IsPrime›.mem_or_mem (mem_of_natCast_mul hpos this) with h | h
    · exact hs h
    · exact hdet h
  · intro hmem
    have h2 : (Matrix.of fun i k => pderiv (J k) (toQZ (f' i))).det = toQZ det' := by
      rw [RingHom.map_det]; congr 1; ext i k
      simp [toQZ, pderiv_map]
    rw [h2, hdet'] at hmem
    exact hdet (hIQ (mem_of_natCast_mul (Finset.prod_pos fun i _ => hu i) hmem))

/-- **(dimension)** A piece `c + n' = N` of a domain with a chart of size `n` has `n' = n`. -/
theorem piece_dim_eq {m n' : ℕ} {G : List (MvPolynomial (Fin N) ℤ)} (hmn : m + n' = N)
    (D : PieceData N G) (hc : D.c = m) (hn' : 0 < n')
    (hh : toQZ D.h ∉ lspan (G.map toQZ)) [IsDomain (MvPolynomial (Fin N) ℚ ⧸ lspan (G.map toQZ))]
    {B : Type} [CommRing B] [Algebra ℚ B]
    (eB : (MvPolynomial (Fin N) ℚ ⧸ lspan (G.map toQZ)) ≃+* B) (𝔭 : Ideal B) [𝔭.IsPrime]
    {n : ℕ} (c : Chart (Localization.AtPrime 𝔭) n) : n' = n := by
  subst hmn
  haveI : IsDomain (SmoothCert.QB G) := ‹_›
  refine dim_eq_of_piece (D.toPiece hc hn') ?_ eB 𝔭 c
  rw [PieceData.toPiece_h, SquarePiece.mkQ, Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact hh

/-- **(gluing)** Pieces with `c = m`, `m + n = N`, covering: a certificate. -/
theorem chartDim_of_cover {m n : ℕ} {G : List (MvPolynomial (Fin N) ℤ)} (hmn : m + n = N)
    (hn : 0 < n) {B : Type} [CommRing B] [Algebra ℚ B]
    (eB : (MvPolynomial (Fin N) ℚ ⧸ lspan (G.map toQZ)) ≃+* B) {K : ℕ}
    (Dk : Fin K → PieceData N G) (hc : ∀ k, (Dk k).c = m) (C : ℕ) (hC : 0 < C)
    (u : Fin K → MvPolynomial (Fin N) ℤ)
    (hcov : (C : MvPolynomial (Fin N) ℤ) - ∑ k, u k * (Dk k).h ∈ lspan G) : ChartDim B n := by
  subst hmn
  exact ⟨m, G, ⟨eB⟩, ⟨SmoothCert.mk K (fun k => (Dk k).toPiece (hc k) hn) C hC u
    (by simpa using hcov)⟩⟩

/-- Clearing denominators of a finite family simultaneously. -/
lemma exists_clear_fin {σ ι : Type*} [Fintype ι] (a : ι → MvPolynomial σ ℚ) :
    ∃ (D : ℕ) (a' : ι → MvPolynomial σ ℤ), 0 < D ∧ ∀ i, toQZ (a' i) = (D : MvPolynomial σ ℚ) * a i := by
  classical
  choose d q hd hq using fun i => exists_clear (a i)
  refine ⟨∏ i, d i, fun i => ((∏ j ∈ Finset.univ.erase i, d j : ℕ) : MvPolynomial σ ℤ) * q i,
    Finset.prod_pos fun i _ => hd i, fun i => ?_⟩
  rw [map_mul, map_natCast, hq, ← mul_assoc, ← Nat.cast_mul,
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)]


end BezoutCounterexample.Principalization.SmoothCertK

namespace BezoutCounterexample.Principalization

open SmoothCertK in
/-- **The Jacobian criterion in certificate form** (trusted primitive, K item: Stacks 00TA/00T7;
Lombardi–Quitté VI–VIII; classical Lean proof). -/
@[cprim]
theorem exists_smoothCert_of_smooth {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B]
    [Algebra.Smooth ℚ B] (hB : HasPres B) (𝔭 : Ideal B) [𝔭.IsPrime] {n : ℕ} (hn : 0 < n)
    (c : Chart (Localization.AtPrime 𝔭) n) : ChartDim B n := by
  classical
  obtain ⟨N, L, ⟨e⟩⟩ := hB
  choose DL qL hDL hqL using fun p : MvPolynomial (Fin N) ℚ => exists_clear p
  let G : List (MvPolynomial (Fin N) ℤ) := L.map qL
  have hIL : lspan (G.map toQZ) = lspan L := by
    apply le_antisymm
    · rw [lspan, Ideal.span_le]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
      rw [hqL]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span hp)
    · rw [lspan, Ideal.span_le]
      intro p hp
      have : toQZ (qL p) ∈ lspan (G.map toQZ) :=
        Ideal.subset_span (List.mem_map_of_mem (List.mem_map_of_mem hp))
      rw [hqL] at this
      exact mem_of_natCast_mul (hDL p) this
  set I := lspan (G.map toQZ)
  let eI : (MvPolynomial (Fin N) ℚ ⧸ I) ≃+* B := (Ideal.quotEquivOfEq hIL).trans e
  haveI : IsDomain (MvPolynomial (Fin N) ℚ ⧸ I) :=
    Function.Injective.isDomain (eI : (MvPolynomial (Fin N) ℚ ⧸ I) →+* B) eI.injective
  let eA : (MvPolynomial (Fin N) ℚ ⧸ I) ≃ₐ[ℚ] B := AlgEquiv.ofRingEquiv (f := eI) fun x =>
    congrFun (congrArg DFunLike.coe (Subsingleton.elim
      ((eI : (MvPolynomial (Fin N) ℚ ⧸ I) →+* B).comp (algebraMap ℚ _)) (algebraMap ℚ B))) x
  haveI : Algebra.FormallySmooth ℚ (MvPolynomial (Fin N) ℚ ⧸ I) :=
    Algebra.FormallySmooth.of_equiv eA.symm
  -- the chart at the generic point
  haveI : (⊥ : Ideal (MvPolynomial (Fin N) ℚ ⧸ I)).IsPrime := Ideal.isPrime_bot
  haveI := Ideal.comap_isPrime (eI : (MvPolynomial (Fin N) ℚ ⧸ I) →+* B) 𝔭
  have h2 : (𝔭.comap (eI : (MvPolynomial (Fin N) ℚ ⧸ I) →+* B)).primeCompl ≤
      (⊥ : Ideal (MvPolynomial (Fin N) ℚ ⧸ I)).primeCompl := fun x hx h0 => by
    rw [Ideal.mem_bot.1 h0] at hx; exact hx (Ideal.zero_mem _)
  let c₀ : Chart (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin N) ℚ ⧸ I))) n :=
    chartLe h2 (c.ofRingEquiv (ChartDim.locEquiv eI 𝔭).symm)
  -- a piece of the right dimension at every prime
  have hpiece : ∀ Q : Ideal (MvPolynomial (Fin N) ℚ), Q.IsPrime → I ≤ Q →
      ∃ D : PieceData N G, toQZ D.h ∉ Q ∧ D.c = N - n ∧ n ≤ N := by
    intro Q hQ hIQ
    obtain ⟨D, hDh, hDdet⟩ := exists_pieceData G Q hIQ
    have hlt : D.c < N := lt_of_chart (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (fun i => toQZ (D.f i)) (fun i => Ideal.Quotient.eq_zero_iff_mem.2 (toQZ_mem_lspan (D.hf i)))
      D.J D.hJ (fun h => hDdet (Ideal.Quotient.eq_zero_iff_mem.1 h)) hn c₀
    have hdim := piece_dim_eq (m := D.c) (n' := N - D.c) (by omega) D rfl (by omega)
      (fun h => hDh (hIQ h)) eI 𝔭 c
    exact ⟨D, hDh, by omega, by omega⟩
  choose Dp hDph hDpc hDpn using hpiece
  -- `n ≤ N`, from one prime
  have hIne : I ≠ ⊤ := fun h => by
    have : Nontrivial (MvPolynomial (Fin N) ℚ ⧸ I) := inferInstance
    rw [Ideal.Quotient.nontrivial_iff] at this; exact this h
  obtain ⟨Q₀, hQ₀, hIQ₀⟩ := Ideal.exists_le_maximal I hIne
  have hnN := hDpn Q₀ hQ₀.isPrime hIQ₀
  -- the cover
  let S : Set (MvPolynomial (Fin N) ℚ) :=
    {x | ∃ (Q : Ideal _) (hQ : Q.IsPrime) (hIQ : I ≤ Q), x = toQZ (Dp Q hQ hIQ).h}
  have htop : I ⊔ Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hIM : I ≤ M := le_sup_left.trans hle
    exact hDph M hM.isPrime hIM (hle (le_sup_right (a := I)
      (Ideal.subset_span ⟨M, hM.isPrime, hIM, rfl⟩)))
  obtain ⟨i₀, hi₀, r, hr, h1⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top (x := 1))
  obtain ⟨T, hTS, hrT⟩ := Submodule.mem_span_finite_of_mem_span hr
  rw [← Subtype.range_coe (s := (T : Set (MvPolynomial (Fin N) ℚ)))] at hrT
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hrT
  choose Qx hQx hIQx hxQ using fun x : (T : Set (MvPolynomial (Fin N) ℚ)) => hTS x.2
  let eT := Fintype.equivFin (T : Set (MvPolynomial (Fin N) ℚ))
  let Dk : Fin (Fintype.card (T : Set (MvPolynomial (Fin N) ℚ))) → PieceData N G :=
    fun k => Dp (Qx (eT.symm k)) (hQx _) (hIQx _)
  obtain ⟨D, a', hD, ha'⟩ := exists_clear_fin (fun k => a (eT.symm k))
  have hcovQ : toQZ ((D : MvPolynomial (Fin N) ℤ) - ∑ k, a' k * (Dk k).h) ∈ I := by
    have : toQZ ((D : MvPolynomial (Fin N) ℤ) - ∑ k, a' k * (Dk k).h) =
        (D : MvPolynomial (Fin N) ℚ) * i₀ := by
      rw [map_sub, map_natCast, map_sum]
      simp only [map_mul, ha']
      have hr' : r = ∑ k, a (eT.symm k) * toQZ (Dk k).h := by
        rw [← ha, ← eT.symm.sum_comp]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_eq_mul, hxQ]
      have h1' := h1
      rw [hr'] at h1'
      simp only [mul_assoc, ← Finset.mul_sum]
      linear_combination (-(D : MvPolynomial (Fin N) ℚ)) * h1'
    rw [this]; exact I.mul_mem_left _ hi₀
  have hcovQ' : toQZ ((D : MvPolynomial (Fin N) ℤ) - ∑ k, a' k * (Dk k).h) ∈ (lspan G).map toQZ :=
    (lspan_map_toQZ G) ▸ hcovQ
  obtain ⟨E, hE, hEmem⟩ := exists_int_mem _ hcovQ'
  refine chartDim_of_cover (m := N - n) (by omega) hn eI Dk
    (fun k => hDpc _ _ _) (E * D) (Nat.mul_pos hE hD) (fun k => (E : MvPolynomial (Fin N) ℤ) * a' k) ?_
  convert hEmem using 1
  rw [mul_sub, Finset.mul_sum]; push_cast; simp only [mul_assoc]

end BezoutCounterexample.Principalization
