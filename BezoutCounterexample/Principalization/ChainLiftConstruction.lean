import Mathlib
import BezoutCounterexample.Construction
import BezoutCounterexample.Principalization.ChainLiftStar
import BezoutCounterexample.Constructive.ChainLiftUnique
import BezoutCounterexample.Principalization.ChainLiftEnum
import BezoutCounterexample.Principalization.ChainLiftGcd
import BezoutCounterexample.Principalization.ChainLiftComplexity
import BezoutCounterexample.Principalization.StageMp
import BezoutCounterexample.Principalization.ReesPt
import BezoutCounterexample.Constructive.ChainLiftCanonComp
import BezoutCounterexample.Principalization.ChainLiftTorsorPresData
import BezoutCounterexample.Principalization.ChartAtBot

/-!
# Construction 5.1 with presentations and chain lifting

The variant of `Construction` in which every stage `A_n` carries an integer presentation
`ℚ[Y₁ … Y_{N_n}] ⧸ (G_n) ≃ A_n`, an index map `σ_n : Fin 2 → Fin N_n` with
`Y_{σ_n 0} ↦ x`, `Y_{σ_n 1} ↦ y`, and a chain-lifting tower from the plane (`G_0 = []`) to the
real points of `G_n` along `w ↦ w ∘ σ_n` (`TowerLift`). The steps are those of `Construction`
(gcd extraction, then Proposition 4.6), with `principalization_star_tower` in place of
`principalization_star`; there are no compact sets.

`TowerConstruction.R` is the direct limit; it is a Bézout domain (`R.isDomain`, `R.isBezout`),
by the proofs of `Construction`.
-/

noncomputable section

namespace BezoutCounterexample

open Principalization Constructive MvPolynomial Construction

/-- The output of Proposition 4.6 with presentations and chain lifting. -/
structure TowerResult (A : SmoothGCDDomain) (I : Ideal A) {N : ℕ}
    (G : List (MvPolynomial (Fin N) ℤ)) (e : Quo (G.map toQ) ≃+* A) where
  A' : SmoothGCDDomain
  f : A →ₐ[ℚ] A'
  N' : ℕ
  G' : List (MvPolynomial (Fin N') ℤ)
  e' : Quo (G'.map toQ) ≃+* A'
  σ : Fin N → Fin N'
  injective : Function.Injective f
  principal : (I.map f).IsPrincipal
  compat : ∀ k, e' (Ideal.Quotient.mk _ (X (σ k))) = f (e (Ideal.Quotient.mk _ (X k)))
  tower : TowerLift (PtG G) (PtG G') (fun x => x ∘ σ)

section TowerFix

/-! ### Composition of results -/

/-- The result for the unit ideal: nothing changes. -/
def TowerResult.top (B : SmoothGCDDomain) {N : ℕ} (G : List (MvPolynomial (Fin N) ℤ))
    (e : Quo (G.map toQ) ≃+* B) : TowerResult B ⊤ G e where
  A' := B
  f := AlgHom.id ℚ B
  N' := N
  G' := G
  e' := e
  σ := id
  injective := Function.injective_id
  principal := ⟨⟨1, by simp⟩⟩
  compat := fun _ => rfl
  tower := TowerLift.refl

/-- **One step and the rest**, as data (`towerConclusion_of_step`). -/
def TowerResult.ofStep {B B₁ : SmoothGCDDomain} {𝔟 : Ideal B} {N N₁ : ℕ}
    {G : List (MvPolynomial (Fin N) ℤ)} {e : Quo (G.map toQ) ≃+* B}
    (f : B →ₐ[ℚ] B₁) (𝔟₁ : Ideal B₁) (α : B₁) (hinj : Function.Injective f)
    (hmap : 𝔟.map f = Ideal.span {α} * 𝔟₁)
    (G₁ : List (MvPolynomial (Fin N₁) ℤ)) (e₁ : Quo (G₁.map toQ) ≃+* B₁) (σ₁ : Fin N → Fin N₁)
    (he₁ : ∀ k, e₁ (Ideal.Quotient.mk _ (X (σ₁ k))) = f (e (Ideal.Quotient.mk _ (X k))))
    (T₁ : TowerLift (PtG G) (PtG G₁) (fun x => x ∘ σ₁))
    (D : TowerResult B₁ 𝔟₁ G₁ e₁) : TowerResult B 𝔟 G e where
  A' := D.A'
  f := D.f.comp f
  N' := D.N'
  G' := D.G'
  e' := D.e'
  σ := D.σ ∘ σ₁
  injective := D.injective.comp hinj
  principal := by
    obtain ⟨⟨t, ht⟩⟩ := D.principal
    refine ⟨⟨D.f α * t, ?_⟩⟩
    have : (𝔟.map (D.f.comp f) : Ideal D.A') = (𝔟.map f).map D.f :=
      (Ideal.map_map (f : B →+* B₁) (D.f : B₁ →+* D.A')).symm
    rw [this, hmap, Ideal.map_mul, ht, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
  compat := fun k => by simp only [Function.comp_apply, AlgHom.comp_apply, D.compat, he₁]
  tower := T₁.trans D.tower

/-! ### The complexity is unique -/

/-- The number of components depends only on the ideal. -/
theorem NumComp.congr {A : Type} [CommRing A] {l l' : List A} (h : lspan l = lspan l') {k : ℕ}
    (hk : NumComp l k) : NumComp l' k := by
  obtain ⟨Cs, hC, hlen⟩ := hk
  refine ⟨Cs, ?_, hlen⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hC
  exact ⟨fun C hC => h ▸ h1 C hC, h2, fun C hC => h ▸ h3 C hC, fun Q hQ => h ▸ h4 Q hQ, h5,
    fun x hx => h ▸ h6 x hx, fun h1' => h7 (h ▸ h1')⟩

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B]

/-- **The complexity is unique** (maximal invariant: `IsMaxInv.unique`; count: `NumComp`). -/
theorem existsUnique_isComplexity (hp : HasPres B) {𝔟 : Ideal B} (h𝔟 : 𝔟 ≠ ⊥) (htop : 𝔟 ≠ ⊤)
    {N : ℕ} (hN : ChartDim B N) (gens : List B) (hgens : 𝔟 = lspan gens) :
    ∃! μ, IsComplexity 𝔟 μ := by
  obtain ⟨μ, hμ⟩ := exists_isComplexity hp h𝔟 htop hN gens hgens
  refine ⟨μ, hμ, fun μ' hμ' => ?_⟩
  have h1 : μ'.1 = μ.1 := hμ'.1.unique hμ'.2.1 hμ.1 hμ.2.1
  obtain ⟨Pg, hPg, hc⟩ := hμ.2.2
  obtain ⟨Pg', hPg', hc'⟩ := hμ'.2.2
  have h2 : lspan Pg' = lspan Pg := by rw [← hPg', ← hPg, h1]
  exact Prod.ext h1 (NumComp.unique (NumComp.congr h2 hc') hc)

/-! ### Search helpers -/

/-- The first nonzero element of a list, or all are zero (zero test). -/
def firstNonzero (hz : ∀ x : B, x = 0 ∨ x ≠ 0) :
    (l : List B) → PSum {x // x ∈ l ∧ x ≠ 0} (∀ x ∈ l, x = 0)
  | [] => PSum.inr fun _ h => absurd h (List.not_mem_nil)
  | a :: l =>
    haveI := decOfOr (hz a)
    if ha : a = 0 then
      match firstNonzero hz l with
      | PSum.inl x => PSum.inl ⟨x.1, List.mem_cons_of_mem _ x.2.1, x.2.2⟩
      | PSum.inr h => PSum.inr fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact ha
          · exact h y hy
    else PSum.inl ⟨a, List.mem_cons_self, ha⟩

/-! ### The recursion -/

/-- The motive: a result for every stage with complexity `μ`. -/
def TowerMotive (Nd : ℕ) (μ : (ℕ → ℚ) × ℕ) : Type 1 :=
  ∀ (B : SmoothGCDDomain) (𝔟 : Ideal B) (m : ℕ), 𝔟 ≠ ⊥ → StarC Nd 𝔟 m →
    (∃ gens : List B, 𝔟 = lspan gens) → (𝔟 ≠ ⊤ → IsComplexity 𝔟 μ) →
    ∀ (N : ℕ) (G : List (MvPolynomial (Fin N) ℤ)) (e : Quo (G.map toQ) ≃+* B),
      TowerResult B 𝔟 G e

/-- `𝔟 = ⊤` is decided by (G). -/
def topDec (B : SmoothGCDDomain) (𝔟 : Ideal B) (hg : ∃ gens : List B, 𝔟 = lspan gens) :
    Decidable (𝔟 = ⊤) :=
  decOfOr (by
    obtain ⟨gs, rfl⟩ := hg
    rcases B.pres.mem_dec gs 1 with h | h
    · exact Or.inl ((Ideal.eq_top_iff_one _).2 h)
    · exact Or.inr fun h' => h ((Ideal.eq_top_iff_one _).1 h'))

/-- The recursive call on a smaller stage: the `⊤` test, then the complexity by unique choice. -/
def TowerMotive.call {Nd : ℕ} {μ : (ℕ → ℚ) × ℕ}
    (ih : ∀ μ₁, ComplexityLT Nd μ₁ μ → TowerMotive Nd μ₁) (hΓ : μ.1 ∈ ΓN Nd)
    (B₁ : SmoothGCDDomain) (𝔟₁ : Ideal B₁) (m₁ : ℕ) (h𝔟₁ : 𝔟₁ ≠ ⊥) (hstar₁ : StarC Nd 𝔟₁ m₁)
    (hg₁ : ∃ gens : List B₁, 𝔟₁ = lspan gens)
    (hdec : ∀ μ₁, IsComplexity 𝔟₁ μ₁ → μ₁.1 ≺ μ.1 ∨ (μ₁.1 = μ.1 ∧ μ₁.2 < μ.2))
    (N₁ : ℕ) (G₁ : List (MvPolynomial (Fin N₁) ℤ)) (e₁ : Quo (G₁.map toQ) ≃+* B₁) :
    TowerResult B₁ 𝔟₁ G₁ e₁ :=
  haveI := topDec B₁ 𝔟₁ hg₁
  if htop₁ : 𝔟₁ = ⊤ then htop₁ ▸ TowerResult.top B₁ G₁ e₁
  else
    let μ₁ := uniqueChoice (by
      obtain ⟨k₁, hk₁, -⟩ := hstar₁.dim_le
      obtain ⟨g₁, hg₁⟩ := hg₁
      exact existsUnique_isComplexity B₁.pres h𝔟₁ htop₁ hk₁ g₁ hg₁)
    ih μ₁.1 ⟨by
        obtain ⟨g₁, hg₁⟩ := hg₁
        exact μ₁.2.mem_ΓN h𝔟₁ hstar₁ g₁ hg₁, hΓ, hdec μ₁.1 μ₁.2⟩
      B₁ 𝔟₁ m₁ h𝔟₁ hstar₁ hg₁ (fun _ => μ₁.2) N₁ G₁ e₁

/-- `span {x} = lspan [x]`. -/
lemma span_singleton_eq_lspan {A : Type} [CommRing A] (x : A) :
    (Ideal.span {x} : Ideal A) = lspan [x] := by
  rw [lspan]; congr 1; ext z; simp

/-- **One step of the recursion**, as data: the `⊤` test, the Rees data from canonical choices,
then the divisorial step (`k = 1`) or the torsor step, and the recursive call. -/
def towerStep (Nd : ℕ) (μ : (ℕ → ℚ) × ℕ)
    (ih : ∀ μ₁, ComplexityLT Nd μ₁ μ → TowerMotive Nd μ₁) : TowerMotive Nd μ :=
  fun B 𝔟 m h𝔟 hstar hg hμ' N G e =>
  haveI := topDec B 𝔟 hg
  if htop : 𝔟 = ⊤ then htop ▸ TowerResult.top B G e
  else
  letI E : Enum B := Enum.ofPres (G.map toQ) e
  haveI : Fact (HasPres B) := ⟨B.pres⟩
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℚ B
  have hμ : IsComplexity 𝔟 μ := hμ' htop
  have hΓ : μ.1 ∈ ΓN Nd := by obtain ⟨gs, hgs⟩ := hg; exact hμ.mem_ΓN h𝔟 hstar gs hgs
  -- canonical generators of `𝔟` and of the locus at points
  let gs := canonGens Enum.en Enum.hen B.pres.mem_dec 𝔟 hg
  have hgs : 𝔟 = lspan gs := (lspan_canonGens _ _ _ 𝔟 hg).symm
  have hbd : ∀ (𝔪 : Ideal B) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt 𝔟 𝔪 v → ∀ i, Nd + m ≤ i →
      v i = 0 := fun 𝔪 _ v hv i hi => by
    obtain ⟨k, hk, hkN⟩ := hstar.dim_le
    exact invAt_bounded hk hv i (by omega)
  have hb₀ : ∀ i, Nd + m ≤ i → μ.1 i = 0 := fun i hi => by
    obtain ⟨q, -, hv⟩ := hμ.2.1
    exact hbd q.ker μ.1 hv i hi
  have hPgex : ∃ L : List B, locusPt 𝔟 μ.1 = lspan L := hμ.2.2.imp fun _ h => h.1
  let Pg := canonGens Enum.en Enum.hen B.pres.mem_dec (locusPt 𝔟 μ.1) hPgex
  have hPg : locusPt 𝔟 μ.1 = lspan Pg := (lspan_canonGens _ _ _ _ hPgex).symm
  have h1 : (1 : B) ∉ lspan Pg := by
    obtain ⟨q, hq, hv⟩ := hμ.2.1
    intro h
    rw [← hPg] at h
    exact (Pt.ker_isMaximal q).ne_top ((Ideal.eq_top_iff_one _).2 (h q hq hv))
  -- the canonical component and the common denominator
  let P := canonComp Enum.en Enum.hen B.pres Pg h1
  have hP : LocusComp 𝔟 μ.1 (lspan P.gens) := LocusComp.of_comp hPg hbd hb₀ ⟨gs, hgs⟩
    (hstar.dim_le.imp fun _ h => h.1.exists_chart_away) P
  let R : ReesData B := ⟨𝔟, h𝔟, htop, lspan P.gens, μ.1, hμ.1, hP, commonDen μ.1 (Nd + m),
    one_le_commonDen _ _, commonDen_spec hb₀, gs, hgs, hstar.dim_le.imp fun _ h => h.1, hμ.2.1⟩
  have h𝔭p : R.𝔭.IsPrime ∧ R.I ≤ R.𝔭 := ⟨R.𝔭_isPrime, R.I_le_𝔭⟩
  have h𝔭ne : R.𝔭 ≠ ⊥ := fun h => R.ne_bot (eq_bot_iff.2 (h ▸ h𝔭p.2))
  if hk : R.k = 1 then
    -- the divisorial step: `δ` is the first `en n` with `𝔭 = (en n)`
    have hex : ∃ n, R.𝔭 = Ideal.span {Enum.en n} := by
      obtain ⟨k₀, hk₀, -⟩ := hstar.dim_le
      obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.1
        (IsNoetherian.noetherian (R.𝔭 : Submodule B B))
      obtain ⟨δ, hδ⟩ := Constructive.exists_isGcdFam B.hasGcd a
      have he0 : R.e 0 ≠ 0 := (R.e_ne_zero_iff 0).2 (by omega)
      have he1 : R.e 1 = 0 := by
        by_contra h; have := (R.e_ne_zero_iff 1).1 h; omega
      have h𝔭δ : R.𝔭 = Ideal.span {δ} :=
        div_eq_span_G_ptL R.ne_bot gs hgs (PrincipalizationData.hchart_of_chartDim hk₀) R.hmax
          R.h𝔭c B.hasGcd B.zeroTest he0 he1 a ha hδ
      obtain ⟨n, rfl⟩ := Enum.hen δ
      exact ⟨n, h𝔭δ⟩
    haveI : DecidablePred fun n => R.𝔭 = Ideal.span {Enum.en n} := fun n => decOfOr (by
      show lspan P.gens = _ ∨ ¬ lspan P.gens = _
      rw [span_singleton_eq_lspan]
      rcases B.pres.le_dec P.gens [Enum.en n] with h | h
      · rcases B.pres.le_dec [Enum.en n] P.gens with h' | h'
        · exact Or.inl (le_antisymm h h')
        · exact Or.inr fun heq => h' heq.ge
      · exact Or.inr fun heq => h heq.le)
    let δ := Enum.en (Nat.find hex)
    have h𝔭δ : R.𝔭 = Ideal.span {δ} := Nat.find_spec hex
    have hδ0 : δ ≠ 0 := by
      intro h0; exact h𝔭ne (by rw [h𝔭δ, h0, Ideal.span_singleton_eq_bot])
    have hδp : Prime δ := (Ideal.span_singleton_prime hδ0).1 (h𝔭δ ▸ h𝔭p.1)
    let S : PrincipalizationData B := ⟨R, δ, hδ0, fun _ => hδp,
      h𝔭δ ▸ Ideal.mem_span_singleton_self δ⟩
    let a := uniqueChoice (P := fun a : ℕ => 0 < a ∧ S.e = fun i => if i = 0 then 1 / (a : ℚ) else 0)
      (by
        obtain ⟨a, ha0, he⟩ := S.divisorial_e_pt hk
        refine ⟨a, ⟨ha0, he⟩, fun a' ⟨_, he'⟩ => ?_⟩
        have h0 := congrFun (he'.symm.trans he) 0
        simp only [ite_true, one_div, inv_inj] at h0
        exact_mod_cast h0)
    have ha : S.e 0 = 1 / (a.1 : ℚ) := (congrFun a.2.2 0).trans (by simp)
    have hmap : Ideal.map (AlgHom.id ℚ B) 𝔟 = Ideal.span {S.π ^ a.1} * S.divI₁ a.1 := by
      change Ideal.map (RingHom.id B) 𝔟 = _
      rw [Ideal.map_id]; exact S.divisorial_I_eq hk ha
    have h𝔟₁ : S.divI₁ a.1 ≠ ⊥ := fun h => h𝔟 (eq_bot_iff.2 (by
      have := S.divisorial_I_eq hk ha
      rw [h, Ideal.mul_bot] at this
      exact this.le))
    TowerResult.ofStep (AlgHom.id ℚ B) (S.divI₁ a.1) (S.π ^ a.1) Function.injective_id hmap G e
      id (fun _ => rfl) TowerLift.refl
      (TowerMotive.call ih hΓ B (S.divI₁ a.1) m h𝔟₁ (S.length_control_divisorial hstar hk ha)
        (Constructive.exists_gens_of_map_eq_mul (RingHom.id B) hgs (pow_ne_zero a.1 hδ0)
          (by rw [Ideal.map_id]; exact S.divisorial_I_eq hk ha))
        (fun μ₁ hμ₁ => by
          obtain ⟨-, hq₁, Pg₁, hPg₁, hc₁⟩ := hμ₁
          obtain ⟨Pg₀, hPg₀, hc₀⟩ := hμ.2.2
          exact PrincipalizationData.divisorial_decrease_mp S hk ha hq₁ hPg₀ hPg₁ hc₀ hc₁) N G e)
  else
    -- the torsor step: `π` is the first nonzero canonical generator of `𝔭`
    match firstNonzero B.zeroTest P.gens with
    | PSum.inr hall => False.elim (h𝔭ne (by
        show lspan P.gens = ⊥
        rw [lspan, Ideal.span_eq_bot]
        exact fun x hx => hall x hx))
    | PSum.inl π =>
      have hπ𝔭 : π.1 ∈ R.𝔭 := Ideal.subset_span π.2.1
      have hk2' : 2 ≤ R.k := by have := R.one_le_k; omega
      let S : PrincipalizationData B := ⟨R, π.1, π.2.2, fun h => absurd h hk, hπ𝔭⟩
      have hk2 : 2 ≤ S.k := hk2'
      have hspec := S.torsor_spec hk2
      have hI₁ : S.I₁ ≠ ⊥ :=
        torsorI_ne_bot S.ne_bot S.hmax S.h𝔭c S.d_pos S.π_mem_fil S.π_ne_zero
      haveI : IsDomain S.U := PrincipalizationData.isDomain_U S
      let T := torsorPresData S hk2 G e
      TowerResult.ofStep (B₁ := S.torsorSGD B.hasGcd B.zeroTest B.dvdDec B.pres hk2)
        (IsScalarTower.toAlgHom ℚ B S.U) S.I₁ (S.sU ^ S.d) hspec.2.2.1 hspec.2.2.2.2 T.G' T.e'
        (Fin.castAdd T.M) T.compat T.tower
        (TowerMotive.call ih hΓ (S.torsorSGD B.hasGcd B.zeroTest B.dvdDec B.pres hk2) S.I₁
          (m + S.ℓ + 1) hI₁ (S.length_control_torsor hstar hk2)
          (Constructive.exists_gens_of_map_eq_mul (algebraMap B S.U) hgs
            (pow_ne_zero _ hspec.2.2.2.1.ne_zero) hspec.2.2.2.2)
          (fun μ₁ hμ₁ => by
            obtain ⟨l₁, hl₁⟩ := Constructive.exists_gens_of_map_eq_mul (algebraMap B S.U) hgs
              (pow_ne_zero _ hspec.2.2.2.1.ne_zero) hspec.2.2.2.2
            obtain ⟨-, hq₁, Pg₁, hPg₁, hc₁⟩ := hμ₁
            obtain ⟨Pg₀, hPg₀, hc₀⟩ := hμ.2.2
            exact PrincipalizationData.torsor_decrease_mp S hk2 hq₁ l₁ hl₁ hPg₀ hPg₁ hc₀ hc₁) _ T.G' T.e')

/-- **Proposition 4.6 with presentations, as data**: `WellFounded.fix` of `towerStep` on the
complexity order. -/
def towerResult' (Nd : ℕ) (μ : (ℕ → ℚ) × ℕ) : TowerMotive Nd μ :=
  (complexityLT_wf Nd).fix (C := TowerMotive Nd) (towerStep Nd) μ

/-- **The data of `principalization_star_tower`, without choice** (Task A C2): the chart size
and the initial complexity by unique choice, then `towerResult'` (well-founded recursion on the
complexity; every datum by unique choice or a decided search, the torsor presentation from
`torsorPresData`). The generators of `I` enter only through a Prop (`hgens`). -/
def towerResult (A : SmoothGCDDomain) (I : Ideal A) (hI : I ≠ ⊥)
    (hgens : ∃ gens : List A, I = lspan gens) {N : ℕ} (G : List (MvPolynomial (Fin N) ℤ))
    (e : Quo (G.map toQ) ≃+* A) : TowerResult A I G e :=
  haveI := topDec A I hgens
  if htop : I = ⊤ then htop ▸ TowerResult.top A G e
  else
    let Nd := uniqueChoice (P := fun n => ChartDim A n) (by
      rcases Principalization.eq_top_or_exists_chartDim_bot A.pres hI with h | ⟨n, hn⟩
      · exact absurd h htop
      · exact ⟨n, hn, fun n' hn' => hn'.unique hn⟩)
    let μ := uniqueChoice (by
      obtain ⟨gs, hgs⟩ := hgens
      exact existsUnique_isComplexity A.pres hI htop Nd.2 gs hgs)
    towerResult' Nd.1 μ.1 A I 0 hI (star_initial Nd.2 I) hgens (fun _ => μ.2) N G e


end TowerFix

namespace TowerConstruction

/-- The data at stage `n`: the ring, its presentation, the coordinates of `x, y`, the map from
`A₀`, the tower from the plane, and the pairs `e i j`. -/
structure Stage where
  A : SmoothGCDDomain
  N : ℕ
  G : List (MvPolynomial (Fin N) ℤ)
  eq : Quo (G.map toQ) ≃+* A
  σ : Fin 2 → Fin N
  base : A₀ →+* A
  compat : ∀ k, eq (Ideal.Quotient.mk _ (X (σ k))) = base (X k)
  tower : TowerLift (PtG ([] : List (MvPolynomial (Fin 2) ℤ))) (PtG G) (fun x => x ∘ σ)
  e : ℕ → ℕ → A × A

def Stage.pair (S : Stage) (n : ℕ) : S.A × S.A :=
  S.e (pairing.symm n).1 (pairing.symm n).2

/-- The step for `a = 0` or `b = 0`: nothing changes. -/
def trivialStep (S : Stage) (a b : S.A) (h : a = 0 ∨ b = 0) :
    TowerResult S.A (Ideal.span {a, b}) S.G S.eq where
  A' := S.A
  f := AlgHom.id ℚ S.A
  N' := S.N
  G' := S.G
  e' := S.eq
  σ := id
  injective := Function.injective_id
  principal := by
    rw [Ideal.map_span, Set.image_pair]
    rcases h with rfl | rfl
    · exact ⟨⟨b, show _ = Ideal.span {b} by simp⟩⟩
    · exact ⟨⟨a, show _ = Ideal.span {a} by rw [Set.pair_comm]; simp⟩⟩
  compat := fun _ => rfl
  tower := TowerLift.refl

lemma lspan_pair {A : Type*} [CommRing A] (a b : A) :
    (Ideal.span {a, b} : Ideal A) = lspan [a, b] := by
  rw [lspan]; congr 1; ext z; simp

/-- The step for `a, b ≠ 0`: gcd extraction, then Proposition 4.6 with chain lifting. The gcd
is unique only up to units, so its ideal `P` is extracted by unique choice and Proposition 4.6 is
applied to the coprime part `(a, b) : P`, whose generators stay in a Prop. -/
def principalizationStep (S : Stage) (a b : S.A) (_ha : a ≠ 0) (hb : b ≠ 0) :
    TowerResult S.A (Ideal.span {a, b}) S.G S.eq :=
  let P := uniqueChoice (existsUnique_gcdIdeal a b)
  let D := towerResult S.A (coprimePart a b P.1) (coprimePart_ne_bot P.2 hb)
    (by
      obtain ⟨g, a', b', h1, h2, h3, h4⟩ := P.2.exists_gen hb
      exact ⟨[a', b'], (coprimePart_eq_span h1 h2 h3 h4).trans (lspan_pair _ _)⟩) S.G S.eq
  { A' := D.A'
    f := D.f
    N' := D.N'
    G' := D.G'
    e' := D.e'
    σ := D.σ
    injective := D.injective
    principal := by
      obtain ⟨g, hg⟩ := D.principal
      obtain ⟨⟨p, hp⟩⟩ := P.2.1
      have hP := congrArg (Ideal.map D.f) hp
      refine ⟨⟨D.f p * g, ?_⟩⟩
      rw [span_eq_mul_coprimePart P.2 hb, Ideal.map_mul, hg, hP, Ideal.submodule_span_eq,
        Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]
    compat := D.compat
    tower := D.tower }

/-- The step: the case split `a = 0 ∨ b = 0` is decided by the zero test of the stage, read as
`Decidable` by unique choice (`decOfOr`), not by `Classical.propDecidable`. -/
def step (S : Stage) (a b : S.A) : TowerResult S.A (Ideal.span {a, b}) S.G S.eq :=
  @dite _ (a = 0 ∨ b = 0) (decOfOr (orDec (S.A.zeroTest a) (S.A.zeroTest b)))
    (fun h => trivialStep S a b h)
    (fun h => principalizationStep S a b (not_or.1 h).1 (not_or.1 h).2)

/-- `ℚ[Y₀, Y₁] ⧸ (0) ≃ A₀`. -/
def eq₀ : Quo (([] : List (MvPolynomial (Fin 2) ℤ)).map toQ) ≃+* A₀ :=
  (Ideal.quotEquivOfEq (by simp [lspan])).trans (RingEquiv.quotientBot _)

/-- **An explicit enumeration of pairs of a presented stage** (Task A, C1): `enumQuo` transported
along the presentation; replaces `chooseSurj`. -/
def enumVia {B : Type*} [CommRing B] {N : ℕ} (G : List (MvPolynomial (Fin N) ℤ))
    (e : Quo (G.map toQ) ≃+* B) (k : ℕ) : B × B :=
  Prod.map e e (enumQuo (G.map toQ) k)

theorem enumVia_surjective {B : Type*} [CommRing B] {N : ℕ} (G : List (MvPolynomial (Fin N) ℤ))
    (e : Quo (G.map toQ) ≃+* B) : Function.Surjective (enumVia G e) := by
  rintro ⟨x, y⟩
  obtain ⟨k, hk⟩ := enumQuo_surjective (G.map toQ) (e.symm x, e.symm y)
  exact ⟨k, by simp [enumVia, hk]⟩

lemma eq₀_mk (p : MvPolynomial (Fin 2) ℚ) : eq₀ (Ideal.Quotient.mk _ p) = p := by
  simp [eq₀]

def initialStage : Stage where
  A := A₀SGD
  N := 2
  G := []
  eq := eq₀
  σ := id
  base := RingHom.id _
  compat := fun k => eq₀_mk _
  tower := TowerLift.refl
  e _ := enumVia [] eq₀

def nextStage (n : ℕ) (S : Stage) : Stage where
  A := (step S (S.pair n).1 (S.pair n).2).A'
  N := (step S (S.pair n).1 (S.pair n).2).N'
  G := (step S (S.pair n).1 (S.pair n).2).G'
  eq := (step S (S.pair n).1 (S.pair n).2).e'
  σ := (step S (S.pair n).1 (S.pair n).2).σ ∘ S.σ
  base := ((step S (S.pair n).1 (S.pair n).2).f : S.A →+* _).comp S.base
  compat k := by
    rw [Function.comp_apply, (step S (S.pair n).1 (S.pair n).2).compat, S.compat]; rfl
  tower := S.tower.trans (step S (S.pair n).1 (S.pair n).2).tower
  e i j :=
    if i ≤ n then
      Prod.map (step S (S.pair n).1 (S.pair n).2).f (step S (S.pair n).1 (S.pair n).2).f (S.e i j)
    else enumVia (step S (S.pair n).1 (S.pair n).2).G' (step S (S.pair n).1 (S.pair n).2).e' j

lemma nextStage_e_of_le (n : ℕ) (S : Stage) {i : ℕ} (h : i ≤ n) (j : ℕ) :
    (nextStage n S).e i j = Prod.map (step S (S.pair n).1 (S.pair n).2).f
      (step S (S.pair n).1 (S.pair n).2).f (S.e i j) := by
  simp only [nextStage, h, ite_true]

lemma nextStage_e_succ (n : ℕ) (S : Stage) (j : ℕ) :
    (nextStage n S).e (n + 1) j =
      enumVia (step S (S.pair n).1 (S.pair n).2).G' (step S (S.pair n).1 (S.pair n).2).e' j := by
  simp [nextStage]

def stage (n : ℕ) : Stage := Nat.rec initialStage (fun n S => nextStage n S) n

abbrev A (n : ℕ) : SmoothGCDDomain := (stage n).A

def η (i : ℕ) : ℕ → A i × A i := (stage i).e i

def pairAt (n : ℕ) : A n × A n := (stage n).pair n

abbrev stepAt (n : ℕ) : TowerResult (A n) (Ideal.span {(pairAt n).1, (pairAt n).2})
    (stage n).G (stage n).eq :=
  step (stage n) (pairAt n).1 (pairAt n).2

def incl (n : ℕ) : A n →ₐ[ℚ] A (n + 1) := (stepAt n).f

theorem incl_injective (n : ℕ) : Function.Injective (incl n) := (stepAt n).injective

theorem span_pairAt_map_isPrincipal (n : ℕ) :
    ((Ideal.span {(pairAt n).1, (pairAt n).2} : Ideal (A n)).map (incl n)).IsPrincipal :=
  (stepAt n).principal

/-! ### The composite maps `A_i → A_j` (as in `Construction`) -/

def inclLEFun {i j : ℕ} (h : i ≤ j) (a : A i) : A j :=
  Nat.leRecOn h (fun {k} (b : A k) => incl k b) a

lemma inclLEFun_self (i : ℕ) (a : A i) : inclLEFun (le_refl i) a = a :=
  Nat.leRecOn_self _

lemma inclLEFun_succ {i j : ℕ} (h : i ≤ j) (a : A i) :
    inclLEFun (h.trans (Nat.le_succ j)) a = incl j (inclLEFun h a) :=
  Nat.leRecOn_succ h _

lemma inclLEFun_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : A i) :
    inclLEFun (hij.trans hjk) a = inclLEFun hjk (inclLEFun hij a) :=
  Nat.leRecOn_trans hij hjk _

def inclLE {i j : ℕ} (h : i ≤ j) : A i →+* A j where
  toFun := inclLEFun h
  map_one' := by
    induction j, h using Nat.le_induction with
    | base => exact inclLEFun_self i 1
    | succ k hik ih => rw [inclLEFun_succ hik, ih, map_one]
  map_mul' a b := by
    induction j, h using Nat.le_induction with
    | base => simp only [inclLEFun_self]
    | succ k hik ih => rw [inclLEFun_succ hik, inclLEFun_succ hik, inclLEFun_succ hik, ih,
        map_mul]
  map_zero' := by
    induction j, h using Nat.le_induction with
    | base => exact inclLEFun_self i 0
    | succ k hik ih => rw [inclLEFun_succ hik, ih, map_zero]
  map_add' a b := by
    induction j, h using Nat.le_induction with
    | base => simp only [inclLEFun_self]
    | succ k hik ih => rw [inclLEFun_succ hik, inclLEFun_succ hik, inclLEFun_succ hik, ih,
        map_add]

lemma inclLE_self (i : ℕ) (a : A i) : inclLE (le_refl i) a = a := inclLEFun_self i a

lemma inclLE_succ {i j : ℕ} (h : i ≤ j) (a : A i) :
    inclLE (h.trans (Nat.le_succ j)) a = incl j (inclLE h a) := inclLEFun_succ h a

lemma inclLE_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : A i) :
    inclLE (hij.trans hjk) a = inclLE hjk (inclLE hij a) := inclLEFun_trans hij hjk a

lemma inclLE_succ_self (n : ℕ) (a : A n) : inclLE (Nat.le_succ n) a = incl n a := by
  rw [← inclLE_self n a, ← inclLE_succ (le_refl n), inclLE_self]

lemma inclLE_injective {i j : ℕ} (h : i ≤ j) : Function.Injective (inclLE h) :=
  Nat.leRecOn_injective h _ (fun k => incl_injective k)

instance directedSystem :
    DirectedSystem (fun n => (A n : Type)) fun _ _ h => ⇑(inclLE h) where
  map_self i a := inclLE_self i a
  map_map _ _ _ hij hjk a := (inclLE_trans hij hjk a).symm

/-- `A₀ ↪ A_n`. -/
def ι (n : ℕ) : A₀ →+* A n := inclLE (Nat.zero_le n)

lemma ι_succ (n : ℕ) (a : A₀) : ι (n + 1) a = incl n (ι n a) :=
  inclLE_succ (Nat.zero_le n) a

/-- The map from `A₀` carried by the stages is `ι`. -/
theorem base_eq (n : ℕ) (a : A₀) : (stage n).base a = ι n a := by
  induction n with
  | zero => exact (inclLE_self 0 a).symm
  | succ n ih =>
    rw [ι_succ, ← ih]
    rfl

theorem η_surjective (i : ℕ) : Function.Surjective (η i) := by
  cases i with
  | zero => exact enumVia_surjective [] eq₀
  | succ n =>
    have : η (n + 1) = enumVia (stage (n + 1)).G (stage (n + 1)).eq :=
      funext fun j => nextStage_e_succ n (stage n) j
    rw [this]
    exact enumVia_surjective _ _

theorem e_eq {i : ℕ} (j : ℕ) {n : ℕ} (h : i ≤ n) :
    (stage n).e i j = Prod.map (inclLE h) (inclLE h) (η i j) := by
  induction n, h using Nat.le_induction with
  | base => ext <;> simp [η, inclLE_self]
  | succ k hik ih =>
    have h1 : (stage (k + 1)).e i j = Prod.map (incl k) (incl k) ((stage k).e i j) :=
      nextStage_e_of_le k (stage k) hik j
    rw [h1, ih]
    ext <;> simp only [Prod.map_fst, Prod.map_snd] <;> exact (inclLE_succ hik _).symm

theorem pairAt_eq (i j : ℕ) :
    pairAt (pairing (i, j)) =
      Prod.map (inclLE (left_le_pairing i j)) (inclLE (left_le_pairing i j)) (η i j) := by
  have h := e_eq j (left_le_pairing i j)
  rw [pairAt, Stage.pair, Equiv.symm_apply_apply]
  exact h

/-! ## The ring `R = ⋃ A_n` -/

def R : Type := Ring.DirectLimit (fun n => (A n : Type)) fun _ _ h => ⇑(inclLE h)

namespace R

instance : CommRing R := inferInstanceAs (CommRing (Ring.DirectLimit _ _))

def of (n : ℕ) : A n →+* R := Ring.DirectLimit.of (fun n => (A n : Type)) _ n

lemma of_inclLE {i j : ℕ} (h : i ≤ j) (a : A i) : of j (inclLE h a) = of i a :=
  Ring.DirectLimit.of_f (G := fun n => (A n : Type)) (f := fun _ _ h => ⇑(inclLE h)) h a

lemma of_incl (n : ℕ) (a : A n) : of (n + 1) (incl n a) = of n a := by
  rw [← inclLE_succ_self, of_inclLE]

lemma of_injective (n : ℕ) : Function.Injective (of n) :=
  Ring.DirectLimit.of_injective (G := fun n => (A n : Type)) (fun _ _ h => inclLE h)
    (fun _ _ h => inclLE_injective h) n

lemma exists_of (r : R) : ∃ n a, of n a = r := Ring.DirectLimit.exists_of r

lemma exists_of_fin (k : ℕ) (v : Fin k → R) :
    ∃ (n : ℕ) (w : Fin k → A n), ∀ t, of n (w t) = v t := by
  induction k with
  | zero => exact ⟨0, Fin.elim0, fun t => Fin.elim0 t⟩
  | succ k ih =>
    obtain ⟨n, w, hw⟩ := ih (fun t => v t.castSucc)
    obtain ⟨m, a, ha⟩ := exists_of (v (Fin.last k))
    refine ⟨max n m, Fin.lastCases (inclLE (le_max_right n m) a)
      (fun t => inclLE (le_max_left n m) (w t)), fun t => ?_⟩
    induction t using Fin.lastCases with
    | last => simp only [Fin.lastCases_last, of_inclLE, ha]
    | cast t => simp only [Fin.lastCases_castSucc, of_inclLE, hw]

def ι : A₀ →+* R := of 0

lemma of_ι (n : ℕ) (a : A₀) : of n (TowerConstruction.ι n a) = ι a :=
  of_inclLE (Nat.zero_le n) a

instance : Nontrivial R := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have : of 0 0 = of 0 1 := by simpa using h
  exact zero_ne_one (of_injective 0 this)

instance isDomain : IsDomain R := by
  have : NoZeroDivisors R := ⟨fun {a b} hab => by
      obtain ⟨n, w, hw⟩ := exists_of_fin 2 ![a, b]
      have ha : of n (w 0) = a := hw 0
      have hb : of n (w 1) = b := hw 1
      have : w 0 * w 1 = 0 := by
        apply of_injective n
        rw [map_mul, ha, hb, hab, map_zero]
      rcases mul_eq_zero.1 this with h | h
      · left; rw [← ha, h, map_zero]
      · right; rw [← hb, h, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

instance isBezout : IsBezout R := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro a b
  obtain ⟨i, w, hw⟩ := exists_of_fin 2 ![a, b]
  obtain ⟨j, hj⟩ := η_surjective i (w 0, w 1)
  set n := pairing (i, j)
  have hpair : pairAt n = (inclLE (left_le_pairing i j) (w 0),
      inclLE (left_le_pairing i j) (w 1)) := by
    rw [pairAt_eq, hj]
    rfl
  obtain ⟨g, hg⟩ := span_pairAt_map_isPrincipal n
  have hg' : (Ideal.span {incl n (inclLE (left_le_pairing i j) (w 0)),
      incl n (inclLE (left_le_pairing i j) (w 1))} : Ideal (A (n + 1))) = Ideal.span {g} := by
    refine Eq.trans ?_ hg
    rw [Ideal.map_span, Set.image_pair, hpair]
  have hmap := congrArg (Ideal.map (of (n + 1))) hg'
  rw [Ideal.map_span, Ideal.map_span, Set.image_pair, Set.image_singleton, of_incl, of_incl,
    of_inclLE, of_inclLE, hw 0, hw 1] at hmap
  exact ⟨⟨of (n + 1) g, by simpa using hmap⟩⟩

end R

end TowerConstruction

end BezoutCounterexample
