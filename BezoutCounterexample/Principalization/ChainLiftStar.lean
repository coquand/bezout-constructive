import Mathlib
import BezoutCounterexample.PrincipalizationStar
import BezoutCounterexample.Principalization.ChainLiftBridgeTower

/-!
# Proposition 4.6 with presentations and chain lifting (`principalization_star_tower`)

The induction of `principalization_star`, carrying in addition an integer presentation
`e : ℚ[Y₁ … Y_N] ⧸ (G) ≃ B` of the current ring. The conclusion (`TowerConclusion`) gives, besides
the injection `f : B ↪ B'` making `𝔟 B'` principal, an integer presentation `e'` of `B'` with
`N'` variables, an index map `σ : Fin N → Fin N'` with `e' (Y_{σ k}) = f (e (Y_k))` (the old
variables are among the new ones), and a tower of chain-lifting steps from the real points of
`G` to those of `G'` along the projection `x ↦ x ∘ σ`.

* divisorial step (`k = 1`): `B` is unchanged (`f = id`), nothing is added to the tower;
* torsor step (`k ≥ 2`): `tower_torsor_stage` with the chart cover `LocusComp.exists_chartCoverPt`,
  the presentation of `U` from `torsorEquiv`.

No compact sets: chain lifting replaces the monotone surjections `K' → K`.
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization Constructive MvPolynomial

/-- The conclusion of Proposition 4.6 with presentations and chain lifting. -/
def TowerConclusion (B : SmoothGCDDomain) (𝔟 : Ideal B) {N : ℕ}
    (G : List (MvPolynomial (Fin N) ℤ)) (e : Quo (G.map toQ) ≃+* B) : Prop :=
  ∃ (B' : SmoothGCDDomain) (f : B →ₐ[ℚ] B') (N' : ℕ) (G' : List (MvPolynomial (Fin N') ℤ))
    (e' : Quo (G'.map toQ) ≃+* B') (σ : Fin N → Fin N'),
    Function.Injective f ∧ (𝔟.map f).IsPrincipal ∧
      (∀ k, e' (Ideal.Quotient.mk _ (X (σ k))) = f (e (Ideal.Quotient.mk _ (X k)))) ∧
      TowerLift (PtG G) (PtG G') (fun x => x ∘ σ)

theorem towerConclusion_top (B : SmoothGCDDomain) {N : ℕ} (G : List (MvPolynomial (Fin N) ℤ))
    (e : Quo (G.map toQ) ≃+* B) : TowerConclusion B ⊤ G e :=
  ⟨B, AlgHom.id ℚ B, N, G, e, id, Function.injective_id, ⟨⟨1, by simp⟩⟩, fun _ => rfl,
    TowerLift.refl⟩

/-- One step and the rest (`conclusion_of_step` with presentations). -/
theorem towerConclusion_of_step {B B₁ : SmoothGCDDomain} {𝔟 : Ideal B} {N N₁ : ℕ}
    {G : List (MvPolynomial (Fin N) ℤ)} {e : Quo (G.map toQ) ≃+* B}
    (f : B →ₐ[ℚ] B₁) (𝔟₁ : Ideal B₁) (α : B₁) (hinj : Function.Injective f)
    (hmap : 𝔟.map f = Ideal.span {α} * 𝔟₁)
    (G₁ : List (MvPolynomial (Fin N₁) ℤ)) (e₁ : Quo (G₁.map toQ) ≃+* B₁) (σ₁ : Fin N → Fin N₁)
    (he₁ : ∀ k, e₁ (Ideal.Quotient.mk _ (X (σ₁ k))) = f (e (Ideal.Quotient.mk _ (X k))))
    (T₁ : TowerLift (PtG G) (PtG G₁) (fun x => x ∘ σ₁))
    (h : TowerConclusion B₁ 𝔟₁ G₁ e₁) : TowerConclusion B 𝔟 G e := by
  obtain ⟨B', g, N', G', e', σ₂, hginj, ⟨⟨t, ht⟩⟩, he', T₂⟩ := h
  refine ⟨B', g.comp f, N', G', e', σ₂ ∘ σ₁, hginj.comp hinj, ⟨⟨g α * t, ?_⟩⟩, fun k => ?_,
    T₁.trans T₂⟩
  · have : (𝔟.map (g.comp f) : Ideal B') = (𝔟.map f).map g :=
      (Ideal.map_map (f : B →+* B₁) (g : B₁ →+* B')).symm
    rw [this, hmap, Ideal.map_mul, ht, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
  · simp only [Function.comp_apply, AlgHom.comp_apply, he', he₁]

/-- **Proposition 4.6 with presentations and chain lifting.** For every triple `(B, 𝔟, m)`
satisfying `(⋆_N)`, with explicit generators of `𝔟` and an integer presentation `e` of `B`, there
is an injection `B ↪ B'` making `𝔟 B'` principal, with an integer presentation of `B'` extending
that of `B` and a chain-lifting tower between their real points. -/
theorem principalization_star_tower (Nd : ℕ) (B : SmoothGCDDomain) (𝔟 : Ideal B) (m : ℕ)
    (h𝔟 : 𝔟 ≠ ⊥) (hstar : StarC Nd 𝔟 m) (gens : List B) (hgens : 𝔟 = Constructive.lspan gens)
    {N : ℕ} (G : List (MvPolynomial (Fin N) ℤ)) (e : Quo (G.map toQ) ≃+* B) :
    TowerConclusion B 𝔟 G e := by
  suffices H : ∀ μ : (ℕ → ℚ) × ℕ, ∀ (B : SmoothGCDDomain) (𝔟 : Ideal B) (m : ℕ),
      𝔟 ≠ ⊥ → StarC Nd 𝔟 m → (∃ gens : List B, 𝔟 = Constructive.lspan gens) →
      IsComplexity 𝔟 μ → ∀ {N : ℕ} (G : List (MvPolynomial (Fin N) ℤ))
      (e : Quo (G.map toQ) ≃+* B), TowerConclusion B 𝔟 G e by
    by_cases htop : 𝔟 = ⊤
    · subst htop; exact towerConclusion_top B G e
    obtain ⟨k, hk, -⟩ := hstar.dim_le
    obtain ⟨μ, hμ⟩ := exists_isComplexity B.pres h𝔟 htop hk gens hgens
    exact H μ B 𝔟 m h𝔟 hstar ⟨gens, hgens⟩ hμ G e
  intro μ
  induction μ using (complexityLT_wf Nd).induction with
  | h μ ih =>
    intro B 𝔟 m h𝔟 hstar hgs hμ N G e
    haveI : Fact (Constructive.HasPres B) := ⟨B.pres⟩
    obtain ⟨_E⟩ := Constructive.HasPres.nonempty_enum B.pres
    letI := _E
    obtain ⟨gs, hgs⟩ := hgs
    -- the unit ideal is principal
    by_cases htop : 𝔟 = ⊤
    · subst htop; exact towerConclusion_top B G e
    have hΓ := hμ.mem_ΓN h𝔟 hstar gs hgs
    -- the recursive call, on the complexity at points of `𝔟₁`
    have hrec : ∀ (B₁ : SmoothGCDDomain) (𝔟₁ : Ideal B₁) (m₁ : ℕ), 𝔟₁ ≠ ⊥ →
        StarC Nd 𝔟₁ m₁ → (∃ gens : List B₁, 𝔟₁ = Constructive.lspan gens) →
        (∀ μ₁, IsComplexity 𝔟₁ μ₁ → μ₁.1 ≺ μ.1 ∨ (μ₁.1 = μ.1 ∧ μ₁.2 < μ.2)) →
        ∀ {N₁ : ℕ} (G₁ : List (MvPolynomial (Fin N₁) ℤ)) (e₁ : Quo (G₁.map toQ) ≃+* B₁),
          TowerConclusion B₁ 𝔟₁ G₁ e₁ := by
      intro B₁ 𝔟₁ m₁ h𝔟₁ hstar₁ hg₁ hdec N₁ G₁ e₁
      by_cases htop₁ : 𝔟₁ = ⊤
      · subst htop₁; exact towerConclusion_top B₁ G₁ e₁
      obtain ⟨g₁, hg₁⟩ := hg₁
      obtain ⟨k₁, hk₁, -⟩ := hstar₁.dim_le
      obtain ⟨μ₁, hμ₁⟩ := exists_isComplexity B₁.pres h𝔟₁ htop₁ hk₁ g₁ hg₁
      exact ih μ₁ ⟨hμ₁.mem_ΓN h𝔟₁ hstar₁ g₁ hg₁, hΓ, hdec μ₁ hμ₁⟩ B₁ 𝔟₁ m₁ h𝔟₁ hstar₁
        ⟨g₁, hg₁⟩ hμ₁ G₁ e₁
    obtain ⟨hμe, hμq, Pg, hPg, hc⟩ := hμ
    -- a component of the locus at points (`exists_comp_data`), a common denominator and a prime
    -- element
    have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℚ B
    obtain ⟨k₀, hk₀, -⟩ := hstar.dim_le
    obtain ⟨e', he', hq', -, Pg', -, P, hP⟩ := exists_comp_data B.pres h𝔟 htop hk₀ gs hgs
    obtain rfl : e' = μ.1 := he'.unique hq' hμe hμq
    obtain ⟨d, hd1, hd⟩ := exists_common_denominator (fun i hi => eq_zero_of_mem_ΓN hΓ hi)
    let R : ReesData B := ⟨𝔟, h𝔟, htop, Constructive.lspan P.gens, μ.1, hμe, hP, d, hd1, hd, gs, hgs,
      hstar.dim_le.imp fun _ h => h.1, hμq⟩
    have h𝔭p : R.𝔭.IsPrime ∧ R.I ≤ R.𝔭 := ⟨R.𝔭_isPrime, R.I_le_𝔭⟩
    have h𝔭ne : R.𝔭 ≠ ⊥ := fun h => R.ne_bot (eq_bot_iff.2 (h ▸ h𝔭p.2))
    by_cases hk : R.k = 1
    · -- the divisorial step (Lemma 4.1): the ring is unchanged
      obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.1
        (IsNoetherian.noetherian (R.𝔭 : Submodule B B))
      obtain ⟨δ, hδ⟩ := Constructive.exists_isGcdFam B.hasGcd a
      have he0 : R.e 0 ≠ 0 := (R.e_ne_zero_iff 0).2 (by omega)
      have he1 : R.e 1 = 0 := by
        by_contra h; have := (R.e_ne_zero_iff 1).1 h; omega
      have h𝔭δ : R.𝔭 = Ideal.span {δ} :=
        div_eq_span_G_ptL R.ne_bot gs hgs (PrincipalizationData.hchart_of_chartDim hk₀) R.hmax R.h𝔭c
          B.hasGcd B.zeroTest he0 he1 a ha hδ
      have hδ0 : δ ≠ 0 := by rintro rfl; exact h𝔭ne (by rw [h𝔭δ, Ideal.span_singleton_eq_bot])
      have hδp : Prime δ := (Ideal.span_singleton_prime hδ0).1 (h𝔭δ ▸ h𝔭p.1)
      let S : PrincipalizationData B := ⟨R, δ, hδ0, fun _ => hδp,
        h𝔭δ ▸ Ideal.mem_span_singleton_self δ⟩
      obtain ⟨a, ha0, he⟩ := S.divisorial_e_pt hk
      have ha : S.e 0 = 1 / (a : ℚ) := by rw [he]; simp
      have hmap : Ideal.map (AlgHom.id ℚ B) 𝔟 = Ideal.span {S.π ^ a} * S.divI₁ a := by
        change Ideal.map (RingHom.id B) 𝔟 = _
        rw [Ideal.map_id]; exact S.divisorial_I_eq hk ha
      refine towerConclusion_of_step (AlgHom.id ℚ B) (S.divI₁ a) (S.π ^ a) Function.injective_id
        hmap G e id (fun _ => rfl) TowerLift.refl ?_
      have h𝔟₁ : S.divI₁ a ≠ ⊥ := fun h => h𝔟 (eq_bot_iff.2 (by
        have := S.divisorial_I_eq hk ha
        rw [h, Ideal.mul_bot] at this
        exact this.le))
      exact hrec B (S.divI₁ a) m h𝔟₁ (S.length_control_divisorial hstar hk ha)
        (Constructive.exists_gens_of_map_eq_mul (RingHom.id B) hgs (pow_ne_zero a hδ0)
          (by rw [Ideal.map_id]; exact S.divisorial_I_eq hk ha))
        (fun μ₁ hμ₁ => by
          obtain ⟨-, hq₁, Pg₁, hPg₁, hc₁⟩ := hμ₁
          exact S.divisorial_decrease_mp hk ha hq₁ hPg hPg₁ hc hc₁) G e
    · -- the torsor step (Lemmas 4.2, 4.3, 4.5) with its chain-lifting tower
      obtain ⟨π, hπ𝔭, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔭ne
      have hk2' : 2 ≤ R.k := by have := R.one_le_k; omega
      let S : PrincipalizationData B := ⟨R, π, hπ0, fun h => absurd h hk, hπ𝔭⟩
      have hk2 : 2 ≤ S.k := hk2'
      obtain ⟨-, -, hinj, hsp, hmap⟩ := S.torsor_spec hk2
      have hI₁ : S.I₁ ≠ ⊥ :=
        torsorI_ne_bot S.ne_bot S.hmax S.h𝔭c S.d_pos S.π_mem_fil S.π_ne_zero
      haveI : IsDomain S.U := PrincipalizationData.isDomain_U S
      obtain ⟨l₁, hl₁⟩ := Constructive.exists_gens_of_map_eq_mul (algebraMap B S.U) hgs
        (pow_ne_zero _ hsp.ne_zero) hmap
      -- the chart cover of the component at explicit points (I1, `LocusComp.exists_chartCoverPt`)
      haveI : Fact (Constructive.HasPres B) := ⟨B.pres⟩
      obtain ⟨C⟩ := S.h𝔭c.exists_chartCoverPt S.ne_bot S.hmax
      obtain ⟨M, G₁, e₁, he₁, T₁⟩ := tower_torsor_stage S.ne_bot S.hmax S.h𝔭c S.d_pos S.hw
        S.π_mem_fil S.π_ne_zero (TowerLift.refl (Pt := PtG G)) e C
        ((S.e_ne_zero_iff 1).2 (by omega))
      exact towerConclusion_of_step (B₁ := S.torsorSGD B.hasGcd B.zeroTest B.dvdDec B.pres hk2)
        (IsScalarTower.toAlgHom ℚ B S.U) S.I₁ (S.sU ^ S.d) hinj hmap G₁ e₁ (Fin.castAdd M)
        he₁ T₁
        (hrec (S.torsorSGD B.hasGcd B.zeroTest B.dvdDec B.pres hk2) S.I₁ (m + S.ℓ + 1) hI₁
          (S.length_control_torsor hstar hk2) ⟨l₁, hl₁⟩
          (fun μ₁ hμ₁ => by
            obtain ⟨-, hq₁, Pg₁, hPg₁, hc₁⟩ := hμ₁
            exact S.torsor_decrease_mp hk2 hq₁ l₁ hl₁ hPg hPg₁ hc hc₁) G₁ e₁)

end BezoutCounterexample
