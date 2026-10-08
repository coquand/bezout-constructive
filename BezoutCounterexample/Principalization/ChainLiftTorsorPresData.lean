import BezoutCounterexample.Principalization.ChainLiftTorsorStepOf
import BezoutCounterexample.Principalization.ChainLiftBridgeTower
import BezoutCounterexample.Principalization.ChainLiftStar
import BezoutCounterexample.Constructive.ChainLiftUnique

/-!
# The presentation of a torsor stage, as data (Task A C2 remainder, leaf)

`tower_torsor_stage` gives the next presentation `(M, G', e')` of a torsor stage as an existential
(integer lifts by `finite_choice`, relations by `exists_offStep`, and an isomorphism through
`RingHom.quotientKerEquivOfSurjective`, whose inverse is `Function.surjInv`). Here all of it is
data:

* `liftQ`, `liftsZ`: integer lifts of elements of a presented ring with a zero test, by the first
  `enumPoly` preimage (decided) and `clearWith` with a common denominator;
* `equivOfBijUC`: a ring isomorphism from a bijective ring map, inverse by unique choice;
* `torsorEquiv'`, `torsorEquiv'_X`: `torsorEquiv` with `equivOfBijUC` of the kernel lift;
* `TorsorPres`: the data of a torsor stage's presentation and its tower step;
* `torsorPresMN` (variables split as `m + n`, `n` the chart size) and **`torsorPresData`** (any
  `N`, transported along `N = (N - n) + n`): the presentation from `liftsZ`, `presList`
  (ChainLiftOffPresData) and `torsorEquiv'`, with chain lifting `chainLift_torsor_step_of`.

Leaf module.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive

/-! ### Integer lifts -/

section Lifts

variable {A : Type} [CommRing A] {N : ℕ} {G₀ : List (MvPolynomial (Fin N) ℚ)}
  (e : Quo G₀ ≃+* A) (hz : ∀ a : A, a = 0 ∨ a ≠ 0)

/-- `enumPoly N k` lifts `x`. -/
def LiftPred (x : A) (k : ℕ) : Prop := e (Ideal.Quotient.mk _ (enumPoly N k)) = x

/-- The lift predicate is decided by the zero test. -/
def liftDec (x : A) : DecidablePred (LiftPred e x) := fun k =>
  decOfOr ((hz (e (Ideal.Quotient.mk _ (enumPoly N k)) - x)).imp sub_eq_zero.1
    fun h h' => h (sub_eq_zero.2 h'))

theorem liftEx (x : A) : ∃ k, LiftPred e x k := by
  obtain ⟨y, rfl⟩ := e.surjective x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨k, hk⟩ := enumPoly_surjective N p
  exact ⟨k, by rw [LiftPred, hk]⟩

/-- **A rational lift** of `x`: the first `enumPoly` mapping to `x` (decided by the zero test). -/
def liftQ (x : A) : MvPolynomial (Fin N) ℚ :=
  enumPoly N (@Nat.find _ (liftDec e hz x) (liftEx e x))

theorem liftQ_spec (x : A) : e (Ideal.Quotient.mk _ (liftQ e hz x)) = x :=
  @Nat.find_spec _ (liftDec e hz x) (liftEx e x)

variable {ι : Type*} [Fintype ι]

/-- The common denominator of the lifts of a family. -/
def liftsD (x : ι → A) : ℕ := ∏ i, denOf (liftQ e hz (x i))

theorem liftsD_pos (x : ι → A) : 0 < liftsD e hz x :=
  Finset.prod_pos fun _ _ => denOf_pos _

/-- **Integer lifts of a family**, up to the common denominator `liftsD`. -/
def liftsZ (x : ι → A) (i : ι) : MvPolynomial (Fin N) ℤ :=
  clearWith (liftsD e hz x) (liftQ e hz (x i))

theorem liftsZ_spec (x : ι → A) (i : ι) :
    e (Ideal.Quotient.mk _ (toQZ (liftsZ e hz x i))) = (liftsD e hz x : A) * x i := by
  rw [liftsZ, toQZ_clearWith _ (by unfold liftsD; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)),
    map_mul,
    map_mul, liftQ_spec, map_natCast, map_natCast]

end Lifts

/-! ### Isomorphisms by unique choice -/

/-- **A ring isomorphism from a bijective ring map**, the inverse by unique choice (no
`Function.surjInv`). -/
def equivOfBijUC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) : R ≃+* S where
  toFun := f
  invFun := fun s => (uniqueChoice (P := fun r => f r = s) (by
    obtain ⟨r, hr⟩ := hf.2 s
    exact ⟨r, hr, fun r' hr' => hf.1 (hr'.trans hr.symm)⟩)).1
  left_inv := fun r => hf.1 (uniqueChoice (P := fun r' => f r' = f r) _).2
  right_inv := fun s => (uniqueChoice (P := fun r => f r = s) _).2
  map_mul' := map_mul f
  map_add' := map_add f

/-! ### The torsor isomorphism without `surjInv` -/

section Equiv

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] [Fact (Constructive.HasPres A)] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (d : ℕ) {π : A}
  (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  [Constructive.Enum A] {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ)) (e : Quo (GQ G) ≃+* A)
  (gZ : Fin (nGen hI hmax h𝔭 d + 1) → MvPolynomial (Fin (m + n)) ℤ)
  (Dg : Fin (nGen hI hmax h𝔭 d + 1) → ℕ)

/-- **`G'` presents HM's torsor**, as data: `torsorEquiv` with the inverse of the kernel lift
by unique choice. -/
def torsorEquiv' (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) (hπ0 : π ≠ 0)
    (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i)
    (G' : List (MvPolynomial (Fin ((m + n) + (1 + ((nGen hI hmax h𝔭 d + 1) +
      (nGen hI hmax h𝔭 d + 1))))) ℤ))
    (hpres : ∀ h, aeval (fvec gZ (ddeg hI hmax h𝔭 d)) h ∈ lspan (H₀ G gZ (ddeg hI hmax h𝔭 d)) ↔
      h ∈ lspan (G'.map toQZ)) :
    Quo (G'.map toQZ) ≃+* Torsor hI hmax h𝔭 d hπ :=
  (Ideal.quotEquivOfEq (ker_torsorΨ hI hmax h𝔭 d hπ G e gZ Dg hπ0 hgZ hDg G' hpres).symm).trans
    (equivOfBijUC (RingHom.kerLift (torsorΨ hI hmax h𝔭 d hπ G e Dg).toRingHom)
      ⟨RingHom.kerLift_injective _, fun u => by
        obtain ⟨p, hp⟩ := torsorΨ_surjective hI hmax h𝔭 d hπ G e Dg hd hw hDg u
        exact ⟨Ideal.Quotient.mk _ p, by rw [RingHom.kerLift_mk]; exact hp⟩⟩)

/-- `torsorEquiv'` sends the old variables to their images in `U`. -/
lemma torsorEquiv'_X (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) (hπ0 : π ≠ 0)
    (hgZ : ∀ i, toA G e (gZ i) = (Dg i : A) * genCoeff hI hmax h𝔭 d π i)
    (hDg : ∀ i, 0 < Dg i)
    (G' : List (MvPolynomial (Fin ((m + n) + (1 + ((nGen hI hmax h𝔭 d + 1) +
      (nGen hI hmax h𝔭 d + 1))))) ℤ))
    (hpres : ∀ h, aeval (fvec gZ (ddeg hI hmax h𝔭 d)) h ∈ lspan (H₀ G gZ (ddeg hI hmax h𝔭 d)) ↔
      h ∈ lspan (G'.map toQZ)) (k : Fin (m + n)) :
    torsorEquiv' hI hmax h𝔭 d hπ G e gZ Dg hd hw hπ0 hgZ hDg G' hpres
      (Ideal.Quotient.mk _ (X (Fin.castAdd _ k))) =
      algebraMap A (Torsor hI hmax h𝔭 d hπ) (e (Ideal.Quotient.mk _ (X k))) := by
  unfold torsorEquiv'
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  show RingHom.kerLift (torsorΨ hI hmax h𝔭 d hπ G e Dg).toRingHom
    (Ideal.Quotient.mk _ (X (Fin.castAdd _ k))) = _
  rw [RingHom.kerLift_mk]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, psiVec, Fin.append_left]

end Equiv

/-! ### The presentation of a torsor stage -/

/-- The next presentation of a torsor stage, with its tower step (the data of
`tower_torsor_stage`). -/
structure TorsorPres {A : Type} [CommRing A] (R : Type) [CommRing R] (ι : A →+* R) {N : ℕ}
    (G : List (MvPolynomial (Fin N) ℤ)) (e : Quo (G.map toQ) ≃+* A) where
  M : ℕ
  G' : List (MvPolynomial (Fin (N + M)) ℤ)
  e' : Quo (G'.map toQ) ≃+* R
  compat : ∀ k, e' (Ideal.Quotient.mk _ (X (Fin.castAdd M k))) = ι (e (Ideal.Quotient.mk _ (X k)))
  tower : TowerLift (PtG G) (PtG G') (fun x k => x (Fin.castAdd M k))

variable {A : SmoothGCDDomain} (S : PrincipalizationData A) [Enum A] [Fact (HasPres A)]
  (hk2 : 2 ≤ S.k)

include hk2 in
/-- A chart cover of the component has a chart, and all its charts have the chart size. -/
theorem exists_chart_n {n : ℕ} (hn : Principalization.ChartDim A n) {N : ℕ}
    (G₀ : List (MvPolynomial (Fin N) ℚ)) (e : Quo G₀ ≃+* A) :
    ∃ C : ChartCoverPtL S.I S.e S.𝔭, (∃ k, (C.D k).n = n) ∧ n ≤ N := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A
  obtain ⟨l₀, hl₀⟩ := S.h𝔭c.gensI
  obtain ⟨C, hCn, -⟩ := S.h𝔭c.exists_chartCoverPtL S.ne_bot S.hmax l₀ hl₀ n hn.exists_chart_away
  obtain ⟨k₀⟩ : Nonempty (Fin C.n) := by
    rcases Nat.eq_zero_or_pos C.n with h0 | h0
    · exfalso
      have h1 := C.one
      have : C.i = 1 := by
        rw [← h1, Finset.sum_eq_zero (fun k _ => absurd k.2 (by omega)), add_zero]
      exact S.h𝔭c.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (this ▸ C.hi))
    · exact ⟨⟨0, h0⟩⟩
  exact ⟨C, ⟨k₀, hCn k₀⟩, hCn k₀ ▸ LocDataPt.n_le G₀ e (C.D k₀)⟩

/-- **The presentation of a torsor stage**, variables split as `m + n` (`n` the chart size). -/
def torsorPresMN {m n : ℕ} (hn : Principalization.ChartDim A n)
    (G : List (MvPolynomial (Fin (m + n)) ℤ)) (e : Quo (G.map toQ) ≃+* A) :
    TorsorPres S.U (algebraMap A S.U) G e :=
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A
  let gen := genCoeff S.ne_bot S.hmax S.h𝔭c S.d S.π
  let D := liftsD e A.zeroTest gen
  let gZ := liftsZ e A.zeroTest gen
  have hgZ : ∀ i, toA G e (gZ i) = ((fun _ => D) i : A) * gen i := fun i =>
    liftsZ_spec e A.zeroTest gen i
  have hDg : ∀ i : Fin (nGen S.ne_bot S.hmax S.h𝔭c S.d + 1), 0 < (fun _ => D) i := fun _ =>
    liftsD_pos e A.zeroTest gen
  { M := 1 + ((nGen S.ne_bot S.hmax S.h𝔭c S.d + 1) + (nGen S.ne_bot S.hmax S.h𝔭c S.d + 1))
    G' := presList G gZ (ddeg S.ne_bot S.hmax S.h𝔭c S.d)
    e' := torsorEquiv' S.ne_bot S.hmax S.h𝔭c S.d S.π_mem_fil G e gZ (fun _ => D) S.d_pos S.hw
      S.π_ne_zero hgZ hDg _ (presList_spec G gZ _)
    compat := torsorEquiv'_X S.ne_bot S.hmax S.h𝔭c S.d S.π_mem_fil G e gZ (fun _ => D) S.d_pos
      S.hw S.π_ne_zero hgZ hDg _ (presList_spec G gZ _)
    tower := by
      -- before `C` is in context, so that `omega` does not use `hdim₀.choose`
      have hv1 : S.e 1 ≠ 0 := (S.e_ne_zero_iff 1).2 (by omega)
      obtain ⟨C, hdim₀, -⟩ := exists_chart_n S hk2 hn (G.map toQ) e
      have hCL := chainLift_torsor_step_of S.ne_bot S.hmax S.h𝔭c S.d S.d_pos S.hw S.π_mem_fil G e
        C hdim₀ hv1
        (by haveI : Algebra.FormallySmooth ℚ (Quo (GQ G)) :=
              Algebra.FormallySmooth.of_equiv e.symm.toRatAlgEquiv
            exact exists_conormalInj_nat G)
        gZ D (liftsD_pos e A.zeroTest gen) hgZ
      exact (TowerLift.refl (Pt := PtG G)).proj hCL }

/-- **The presentation of a torsor stage, as data**: the chart size `n` by unique choice, the
variables split as `N = (N - n) + n`, then `torsorPresMN`. -/
def torsorPresData {N : ℕ} (G : List (MvPolynomial (Fin N) ℤ)) (e : Quo (G.map toQ) ≃+* A) :
    TorsorPres S.U (algebraMap A S.U) G e :=
  let n := uniqueChoice (P := fun n => Principalization.ChartDim A n) (by
    obtain ⟨k, hk⟩ := S.hN
    exact ⟨k, hk, fun k' hk' => hk'.unique hk⟩)
  have hmn : N - n.1 + n.1 = N := by
    obtain ⟨-, -, h⟩ := exists_chart_n S hk2 n.2 (G.map toQ) e
    omega
  (hmn ▸ fun (G : List (MvPolynomial (Fin (N - n.1 + n.1)) ℤ)) e =>
    torsorPresMN S hk2 n.2 G e :
      ∀ (G : List (MvPolynomial (Fin N) ℤ)) (e : Quo (G.map toQ) ≃+* A),
        TorsorPres S.U (algebraMap A S.U) G e) G e

end BezoutCounterexample.Principalization
