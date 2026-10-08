import BezoutCounterexample.SphereBundle
import BezoutCounterexample.Constructive.GensTransform
import BezoutCounterexample.Principalization.StageMp
import BezoutCounterexample.Principalization.StarCPt
import BezoutCounterexample.Principalization.ChartAtBot

/-!
# The proof of Proposition 4.6

Fix `N`. We prove the stronger assertion of the proof of Proposition 4.6
(`principalization_star`): for every triple `(B, 𝔟, m)` satisfying `(⋆_N)`, with `B` a smooth
finitely generated factorial `ℚ`-domain, and every compact set `K ⊂ Spec(B)(ℝ)`, there are an
injection `B ↪ B'` and a compact set `K' ⊂ Spec(B')(ℝ)` such that `𝔟 B'` is principal and the
induced map `K' → K` is a monotone surjection. Proposition 4.6 is the case `(A, I, 0)`, `N = dim A`
(`PrincipalizationExtension.lean`).

If `𝔟 = B`, take `B' = B` and `K' = K`. For `𝔟 ≠ B` we argue by well-founded induction on the pair
`(maxinv(𝔟), c(𝔟))`, ordered lexicographically, with `⪯` on the first entry and the usual order
on `ℕ` on the second (`ComplexityLT`). This is well-founded by Theorem 3.3(5), because all
invariants of ideals in triples satisfying `(⋆_N)` have at most `N` nonzero entries
(`complexityLT_wf`). Let `k` be the number of nonzero entries of `maxinv(𝔟)`, choose a component of
the maximal locus of `𝔟`, and apply the divisorial step (Lemma 4.1) if `k = 1` or the torsor step
(Lemmas 4.2, 4.3, 4.5) if `k ≥ 2`. By Lemmas 4.1, 4.3 and 4.4, the new triple `(B₁, 𝔟₁, m₁)`
satisfies `(⋆_N)`, and either `𝔟₁ = B₁` or its complexity is strictly smaller. In either case the
assertion holds for `(B₁, 𝔟₁, m₁)` and `K₁`; composing (Lemma 2.2) gives the assertion for
`(B, 𝔟, m)` and `K`.
-/

noncomputable section

namespace BezoutCounterexample

open IsLocalRing Principalization

/-! ## The well-founded complexity -/

/-- The weight vectors in `Γ` with at most `N` nonzero entries. -/
def ΓN (N : ℕ) : Set (ℕ → ℚ) := {e ∈ Γ | {i | e i ≠ 0}.encard ≤ N}

/-- The lexicographic order on complexities `(maxinv(𝔟), c(𝔟))`: `⪯` on the first entry and the
usual order on `ℕ` on the second (restricted to `Γ_N × ℕ`). -/
def ComplexityLT (N : ℕ) (p q : (ℕ → ℚ) × ℕ) : Prop :=
  p.1 ∈ ΓN N ∧ q.1 ∈ ΓN N ∧ (p.1 ≺ q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2))

/-- The complexity order is well-founded (Theorem 3.3(5)). -/
theorem complexityLT_wf (N : ℕ) : WellFounded (ComplexityLT N) := by
  have hΓ : WellFounded (fun a b : ΓN N => a.1 ≺ b.1) := Γ_wellFoundedOn N
  have hwf : WellFounded (Prod.Lex (fun a b : ΓN N => a.1 ≺ b.1) (· < · : ℕ → ℕ → Prop)) :=
    WellFounded.prod_lex hΓ wellFounded_lt
  have H : ∀ q : ΓN N × ℕ, Acc (ComplexityLT N) (q.1.1, q.2) := by
    intro q
    induction q using hwf.induction with
    | h q ih =>
      refine ⟨_, fun r hr => ?_⟩
      obtain ⟨hr1, -, hlt⟩ := hr
      have := ih (⟨r.1, hr1⟩, r.2) (by
        rcases hlt with h | ⟨h, h'⟩
        · exact Prod.Lex.left _ _ h
        · have hq : (⟨r.1, hr1⟩ : ΓN N) = q.1 := Subtype.ext h
          rw [hq]
          exact Prod.Lex.right _ h')
      exact this
  -- no case split on `p.1 ∈ ΓN N`: every predecessor `r` carries `r.1 ∈ ΓN N` (Task A, C8)
  exact ⟨fun p => ⟨_, fun r hr => H (⟨r.1, hr.1⟩, r.2)⟩⟩

/-- An element of `Γ` with at most `N` nonzero entries vanishes from index `N` on. -/
theorem eq_zero_of_mem_ΓN {N : ℕ} {e : ℕ → ℚ} (he : e ∈ ΓN N) {i : ℕ} (hi : N ≤ i) : e i = 0 := by
  by_contra h
  have hprop : ∀ j, e j = 0 → ∀ l, j ≤ l → e l = 0 := by
    intro j hj l hl
    induction l, hl using Nat.le_induction with
    | base => exact hj
    | succ l _ ih => exact he.1.2 l ih
  have hall : ∀ j ≤ i, e j ≠ 0 := fun j hj h0 => h (hprop j h0 i hj)
  have hsub : (Finset.range (i + 1) : Set ℕ) ⊆ {j | e j ≠ 0} := fun j hj =>
    hall j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  have h1 := Set.encard_le_encard hsub
  rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range] at h1
  have h2 := h1.trans he.2
  norm_cast at h2
  omega

/-- A common denominator of a weight vector with finitely many nonzero entries. -/
theorem exists_common_denominator {e : ℕ → ℚ} {N : ℕ} (he : ∀ i, N ≤ i → e i = 0) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ i, ∃ w : ℤ, (d : ℚ) * e i = w := by
  refine ⟨∏ i ∈ Finset.range N, (e i).den, Nat.one_le_iff_ne_zero.2
    (Finset.prod_ne_zero_iff.2 fun i _ => (e i).den_ne_zero), fun i => ?_⟩
  by_cases hi : i < N
  · exact dvd_den_mul_int (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi))
  · exact ⟨0, by rw [he i (not_lt.1 hi), mul_zero, Int.cast_zero]⟩

/-! ## The stronger assertion -/

/-- The conclusion of Proposition 4.6 for `(B, 𝔟, K)`. -/
def PrincipalizationConclusion (B : SmoothGCDDomain) (𝔟 : Ideal B) (K : Set (RealPt B)) :
    Prop :=
  ∃ (B' : SmoothGCDDomain) (f : B →ₐ[ℚ] B') (K' : Set (RealPt B')),
    Function.Injective f ∧ (𝔟.map f).IsPrincipal ∧ IsCompact K' ∧
      IsMonotoneSurjOn (RealPt.comap (f : B →+* B')) K' K

theorem conclusion_top (B : SmoothGCDDomain) (K : Set (RealPt B)) (hK : IsCompact K) :
    PrincipalizationConclusion B ⊤ K :=
  ⟨B, AlgHom.id ℚ B, K, Function.injective_id, ⟨⟨1, by simp⟩⟩, hK, IsMonotoneSurjOn.id K⟩

/-- One step and the rest: if `𝔟 B₁ = α 𝔟₁` for an injection `f : B ↪ B₁` and a monotone surjection
`K₁ → K`, then the conclusion for `(B₁, 𝔟₁, K₁)` gives the conclusion for `(B, 𝔟, K)`. -/
theorem conclusion_of_step {B B₁ : SmoothGCDDomain} {𝔟 : Ideal B} {K : Set (RealPt B)}
    (f : B →ₐ[ℚ] B₁) (K₁ : Set (RealPt B₁)) (𝔟₁ : Ideal B₁) (α : B₁)
    (hinj : Function.Injective f) (hmap : 𝔟.map f = Ideal.span {α} * 𝔟₁)
    (hmono : IsMonotoneSurjOn (RealPt.comap (f : B →+* B₁)) K₁ K)
    (h : PrincipalizationConclusion B₁ 𝔟₁ K₁) : PrincipalizationConclusion B 𝔟 K := by
  obtain ⟨B', g, K', hginj, ⟨⟨t, ht⟩⟩, hK', hgmono⟩ := h
  refine ⟨B', g.comp f, K', hginj.comp hinj, ⟨⟨g α * t, ?_⟩⟩, hK', ?_⟩
  · have : (𝔟.map (g.comp f) : Ideal B') = (𝔟.map f).map g :=
      (Ideal.map_map (f : B →+* B₁) (g : B₁ →+* B')).symm
    rw [this, hmap, Ideal.map_mul, ht, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
  · exact IsMonotoneSurjOn.trans hK' hmono hgmono

/-- The complexity of an ideal in a triple satisfying `(⋆_N)` lies in `Γ_N`. -/
theorem maxinv_mem_ΓN {N m : ℕ} {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B]
    [Algebra.Smooth ℚ B] {𝔟 : Ideal B} (h𝔟 : 𝔟 ≠ ⊥) (htop : 𝔟 ≠ ⊤) (hstar : StarC N 𝔟 m) :
    maxinv 𝔟 ∈ ΓN N := by
  obtain ⟨⟨𝔪, h𝔪, h𝔟𝔪, hinv⟩, -⟩ := maxinv_spec h𝔟 htop
  rw [← hinv]
  refine ⟨inv_mem_Γ h𝔟 h𝔟𝔪, ?_⟩
  have h1 := hstar.numNonzero_inv_le h𝔟 𝔪 h𝔟𝔪
  rw [← (finite_support_inv h𝔟 h𝔟𝔪).cast_ncard_eq]
  exact_mod_cast h1

/-- **The complexity at points lies in `Γ_N`** under `(⋆_N)` (`IsMaxInv.mem_Γ`, `StarC.eq_zero_pt` at
the attaining point; replaces `maxinv_mem_ΓN` in the recursion). -/
theorem IsComplexity.mem_ΓN {N m : ℕ} {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B]
    [Algebra.Smooth ℚ B] {𝔟 : Ideal B} (h𝔟 : 𝔟 ≠ ⊥) (hstar : StarC N 𝔟 m)
    (gens : List B) (hgens : 𝔟 = Constructive.lspan gens) {μ : (ℕ → ℚ) × ℕ}
    (hμ : IsComplexity 𝔟 μ) : μ.1 ∈ ΓN N := by
  obtain ⟨-, ⟨q, hq, hv⟩, -⟩ := hμ
  refine ⟨InvAt.mem_Γ_pt h𝔟 gens hgens q hq hv, ?_⟩
  have hnn := hstar.numNonzero_le_pt h𝔟 gens hgens q hq hv
  obtain ⟨k, hk, -⟩ := hstar.dim_le
  have hfin : {i | μ.1 i ≠ 0}.Finite := (Finset.range k).finite_toSet.subset fun i hi =>
    Finset.mem_coe.2 (Finset.mem_range.2
      ((Nat.lt_or_ge i k).resolve_right fun h => hi (invAt_bounded hk hv i h)))
  rw [← hfin.cast_ncard_eq]
  exact_mod_cast hnn

/-- **The stronger assertion** in the proof of Proposition 4.6: for every triple `(B, 𝔟, m)`
satisfying `(⋆_N)` with `B` a smooth finitely generated `ℚ`-domain with gcds, and every compact set
`K ⊂ Spec(B)(ℝ)`, there are an injection `B ↪ B'` and a compact `K' ⊂ Spec(B')(ℝ)` such that `𝔟 B'`
is principal and `K' → K` is a monotone surjection. -/
theorem principalization_star (N : ℕ) (B : SmoothGCDDomain) (𝔟 : Ideal B) (m : ℕ)
    (h𝔟 : 𝔟 ≠ ⊥) (hstar : StarC N 𝔟 m) (gens : List B) (hgens : 𝔟 = Constructive.lspan gens)
    (K : Set (RealPt B)) (hK : IsCompact K) :
    PrincipalizationConclusion B 𝔟 K := by
  suffices H : ∀ μ : (ℕ → ℚ) × ℕ, ∀ (B : SmoothGCDDomain) (𝔟 : Ideal B) (m : ℕ),
      𝔟 ≠ ⊥ → StarC N 𝔟 m → (∃ gens : List B, 𝔟 = Constructive.lspan gens) →
      IsComplexity 𝔟 μ → ∀ K : Set (RealPt B),
      IsCompact K → PrincipalizationConclusion B 𝔟 K by
    by_cases htop : 𝔟 = ⊤
    · subst htop; exact conclusion_top B K hK
    obtain ⟨k, hk, -⟩ := hstar.dim_le
    obtain ⟨μ, hμ⟩ := exists_isComplexity B.pres h𝔟 htop hk gens hgens
    exact H μ B 𝔟 m h𝔟 hstar ⟨gens, hgens⟩ hμ K hK
  intro μ
  induction μ using (complexityLT_wf N).induction with
  | h μ ih =>
    intro B 𝔟 m h𝔟 hstar hgs hμ K hK
    haveI : Fact (Constructive.HasPres B) := ⟨B.pres⟩
    obtain ⟨_E⟩ := Constructive.HasPres.nonempty_enum B.pres
    letI := _E
    obtain ⟨gs, hgs⟩ := hgs
    -- the unit ideal is principal
    by_cases htop : 𝔟 = ⊤
    · subst htop; exact conclusion_top B K hK
    have hΓ := hμ.mem_ΓN h𝔟 hstar gs hgs
    -- the recursive call, on the complexity at points of `𝔟₁`
    have hrec : ∀ (B₁ : SmoothGCDDomain) (𝔟₁ : Ideal B₁) (m₁ : ℕ), 𝔟₁ ≠ ⊥ →
        StarC N 𝔟₁ m₁ → (∃ gens : List B₁, 𝔟₁ = Constructive.lspan gens) →
        (∀ μ₁, IsComplexity 𝔟₁ μ₁ → μ₁.1 ≺ μ.1 ∨ (μ₁.1 = μ.1 ∧ μ₁.2 < μ.2)) →
        ∀ K₁ : Set (RealPt B₁), IsCompact K₁ → PrincipalizationConclusion B₁ 𝔟₁ K₁ := by
      intro B₁ 𝔟₁ m₁ h𝔟₁ hstar₁ hg₁ hdec K₁ hK₁
      by_cases htop₁ : 𝔟₁ = ⊤
      · subst htop₁; exact conclusion_top B₁ K₁ hK₁
      obtain ⟨g₁, hg₁⟩ := hg₁
      obtain ⟨k₁, hk₁, -⟩ := hstar₁.dim_le
      obtain ⟨μ₁, hμ₁⟩ := exists_isComplexity B₁.pres h𝔟₁ htop₁ hk₁ g₁ hg₁
      exact ih μ₁ ⟨hμ₁.mem_ΓN h𝔟₁ hstar₁ g₁ hg₁, hΓ, hdec μ₁ hμ₁⟩ B₁ 𝔟₁ m₁ h𝔟₁ hstar₁
        ⟨g₁, hg₁⟩ hμ₁ K₁ hK₁
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
    · -- the divisorial step (Lemma 4.1); `π` is the gcd of generators of `𝔭` (`div_eq_span_G_ptL`)
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
      refine conclusion_of_step (AlgHom.id ℚ B) K (S.divI₁ a) (S.π ^ a) Function.injective_id
        ?_ (IsMonotoneSurjOn.id K) ?_
      · change Ideal.map (RingHom.id B) 𝔟 = _
        rw [Ideal.map_id]; exact S.divisorial_I_eq hk ha
      · have h𝔟₁ : S.divI₁ a ≠ ⊥ := fun h => h𝔟 (eq_bot_iff.2 (by
          have := S.divisorial_I_eq hk ha
          rw [h, Ideal.mul_bot] at this
          exact this.le))
        exact hrec B (S.divI₁ a) m h𝔟₁ (S.length_control_divisorial hstar hk ha)
          (Constructive.exists_gens_of_map_eq_mul (RingHom.id B) hgs (pow_ne_zero a hδ0)
            (by rw [Ideal.map_id]; exact S.divisorial_I_eq hk ha))
          (fun μ₁ hμ₁ => by
            obtain ⟨-, hq₁, Pg₁, hPg₁, hc₁⟩ := hμ₁
            exact S.divisorial_decrease_mp hk ha hq₁ hPg hPg₁ hc hc₁) K hK
    · -- the torsor step (Lemmas 4.2, 4.3, 4.5); any nonzero `π ∈ 𝔭` will do
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
      obtain ⟨hK₁, hmono, -, -⟩ := S.sphere_bundle hk2 hK
      exact conclusion_of_step (B₁ := S.torsorSGD B.hasGcd B.zeroTest B.dvdDec B.pres hk2)
        (IsScalarTower.toAlgHom ℚ B S.U) (S.sphereBundle K) S.I₁ (S.sU ^ S.d) hinj hmap hmono
        (hrec (S.torsorSGD B.hasGcd B.zeroTest B.dvdDec B.pres hk2) S.I₁ (m + S.ℓ + 1) hI₁
          (S.length_control_torsor hstar hk2) ⟨l₁, hl₁⟩
          (fun μ₁ hμ₁ => by
            obtain ⟨-, hq₁, Pg₁, hPg₁, hc₁⟩ := hμ₁
            exact S.torsor_decrease_mp hk2 hq₁ l₁ hl₁ hPg hPg₁ hc hc₁) _ hK₁)

end BezoutCounterexample
