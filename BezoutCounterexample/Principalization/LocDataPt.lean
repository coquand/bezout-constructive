import BezoutCounterexample.Principalization.MaxLocus
import BezoutCounterexample.Principalization.Points

/-!
# Local data of the maximal locus, quantified over explicit points (D3.4, leaf)

`LocData I v₀ 𝔪` (MaxLocus) has the same data as `LocDataPt`, but its two properties `iff` and `rf`
quantify over *all* maximal ideals `𝔪' ∌ g`; producing them needs the recentring at arbitrary maximal
ideals (classical). `LocDataPt` asks for them only at the kernels of explicit points `p : Pt A`, which
is what every constructive consumer uses (`docs/d3-design.md` §8.3: "the new lemmas use `D.iff`/`D.rf`
only at `p.ker`") and what the point producer (D3.4, `exists_centred_pos`) gives.

* `LocDataPt`, its data accessors `N`, `B`, `ctrlN`, `away`, `cB`, `RFB`, `P`, `p`;
* `LocData.toPt`: the forgetful map (instantiation at `p.ker`, constructive);
* `LocDataPt.iff_pt`, `LocDataPt.rf_pt`: the two properties, as stated for consumers.

Leaf module (nothing on the top chain imports it); the consumers switch to it in the D3.5
integration diff.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A]
  -- I4 (D3.6): the per-point instances instead of `[Algebra.Smooth ℚ A]`, so that the twins apply
  -- to the Rees algebra (`i4_of_smooth` recovers them from smoothness)
  [hI4a : ∀ q : Pt A, Fact (BezoutCounterexample.Constructive.PolyIndNoeth (Localization.AtPrime q.ker))]
  [hI4b : ∀ q : Pt A, Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker)]
  [hI4c : ∀ q : Pt A, Algebra.FormallySmooth ℚ (IsLocalRing.ResidueField (Localization.AtPrime q.ker))]

/-- **Local data of the maximal locus at `𝔪`, with properties at explicit points.** -/
structure LocDataPt (I : Ideal A) (v₀ : ℕ → ℚ) (𝔪 : Ideal A) [𝔪.IsMaximal] where
  n : ℕ
  M : Submonoid A
  g : A
  hg : g ∉ 𝔪
  ctrl : Loc.Ctrl M g
  k : ℕ
  ck : Chart (Localization M) n
  ek : Fin n → ℚ
  supp : ∀ i, ek i ≠ 0 ↔ (i : ℕ) < k
  hv : ext0 ek = v₀
  adm : I.map (algebraMap A (Localization M)) ≤ ck.RF ek 1
  inv : IsInv (Iloc I 𝔪) n ek
  cent : (Loc.transport (ctrl 𝔪 hg) ck).IsCentred
  /-- the locus on `D(g)`, at explicit points -/
  iff : ∀ (p : Pt A) (hg' : g ∉ p.ker),
    ((I ≤ p.ker ∧ InvAt I p.ker v₀) ↔ ∀ i : Fin n, (i : ℕ) < k →
      (Loc.transport (ctrl p.ker hg') ck).x i ∈ maximalIdeal (Localization.AtPrime p.ker))
  /-- the centre's weighted ideals on `D(g)`, at explicit points -/
  rf : ∀ (p : Pt A) (hg' : g ∉ p.ker),
    ∀ J' : MC (Localization.AtPrime p.ker) n, J'.Adm (Iloc I p.ker) → J'.e = ek →
      ∀ t, J'.RF t = (Loc.transport (ctrl p.ker hg') ck).RF ek t

variable [IsNoetherianRing A] in
/-- **The forgetful map**: classical local data restrict to explicit points. -/
def LocData.toPt {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) :
    LocDataPt I v₀ 𝔪 where
  n := D.n
  M := D.M
  g := D.g
  hg := D.hg
  ctrl := D.ctrl
  k := D.k
  ck := D.ck
  ek := D.ek
  supp := D.supp
  hv := D.hv
  adm := D.adm
  inv := D.inv
  cent := D.cent
  iff p hg' := D.iff p.ker hg'
  rf p hg' := D.rf p.ker hg'

namespace LocDataPt

variable {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocDataPt I v₀ 𝔪)

/-- The controlled submonoid `M ⊔ gᴺ`. -/
abbrev N : Submonoid A := D.M ⊔ Submonoid.powers D.g

/-- The basic open `D(g)` as a ring. -/
abbrev B := Localization D.N

omit [IsDomain A] hI4a hI4b hI4c in
lemma ctrlN : Loc.Ctrl D.N D.g := D.ctrl.sup

instance away : IsLocalization.Away D.g D.B := Loc.away_of_ctrl D.ctrl

/-- The chart over `D(g)`. -/
def cB : Chart D.B D.n := Loc.transport le_sup_left D.ck

/-- The weighted ideals over `D(g)`. -/
def RFB (t : ℚ) : Ideal D.B := D.cB.RF D.ek t

/-- The ideal of the maximal locus at `𝔪`, in `A_𝔪`. -/
def P : Ideal (Localization.AtPrime 𝔪) :=
  Ideal.span ((Loc.transport (D.ctrl 𝔪 D.hg) D.ck).x '' {i | (i : ℕ) < D.k})

/-- The corresponding prime of `A`. -/
def p : Ideal A := D.P.under A

omit [IsDomain A] hI4a hI4b hI4c in
/-- `iff`, as stated for consumers. -/
theorem iff_pt (p : Pt A) (hg' : D.g ∉ p.ker) :
    (I ≤ p.ker ∧ InvAt I p.ker v₀) ↔ ∀ i : Fin D.n, (i : ℕ) < D.k →
      (Loc.transport (D.ctrl p.ker hg') D.ck).x i ∈ maximalIdeal (Localization.AtPrime p.ker) :=
  D.iff p hg'

omit [IsDomain A] hI4a hI4b hI4c in
/-- `rf`, as stated for consumers. -/
theorem rf_pt (p : Pt A) (hg' : D.g ∉ p.ker) (J' : MC (Localization.AtPrime p.ker) D.n)
    (hJ' : J'.Adm (Iloc I p.ker)) (he : J'.e = D.ek) (t : ℚ) :
    J'.RF t = (Loc.transport (D.ctrl p.ker hg') D.ck).RF D.ek t :=
  D.rf p hg' J' hJ' he t

end LocDataPt

variable [IsNoetherianRing A] in
omit [IsDomain A] hI4a hI4b hI4c in
/-- The forgetful map preserves the data (the derived objects agree definitionally). -/
lemma LocData.toPt_g {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) :
    D.toPt.g = D.g ∧ D.toPt.ek = D.ek ∧ D.toPt.n = D.n := ⟨rfl, rfl, rfl⟩

end BezoutCounterexample.Principalization
