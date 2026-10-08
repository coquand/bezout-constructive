import BezoutCounterexample.Principalization.Cover

/-!
# Components of the maximal locus without minimal primes (leaf; plan (P2), (P3))

MaxLocus describes the components of the maximal locus as the minimal primes of
`locusIdeal I v₀ = ⋂_{𝔪 ∈ maxLocus} 𝔪`, and proves the facts it needs about them by
`by_contra`/`by_cases` on membership in maximal ideals, Zorn (`exists_le_maximal`,
`minimalPrimes`) and the Jacobson property. Each of these proves a *positive* statement about
all maximal ideals from per-point case analysis, which is the double-negation shift.

Here:

* `locusIdealS` — the `¬¬`-closed locus ideal `{f | ∀ 𝔪 ∈ maxLocus, ¬¬ f ∈ 𝔪}` (classically equal
  to `locusIdeal`). Membership is proved pointwise under `¬¬`, so no case split is needed.
* `JacS A` — the Jacobson property in the form the effective Nullstellensatz provides for a prime
  of a f.t. `ℚ`-algebra: if `f` is `¬¬`-in every maximal ideal above `p`, then `f ∈ p`.
  `jacS_of_classical` is the classical source (`IsJacobsonRing`); this is (P2), the one place to
  swap.
* `mem_maxLocus_of_le_S` — the maximal locus is closed, with the stable bound `¬ (v < v₀)` of
  `exists_maxInv_C`. The only case analysis is on the stable goal `v = v₀` (decidable equality of
  `ℚ`, `invAt_of_nn`), together with `nn_le_total`.
* The components are the explicit primes `D.p` of local data `D : LocData I v₀ 𝔪` (no minimal
  primes, no Zorn): `LocData.locusIdealS_le_p`, `LocData.p_le_of_le` (so `D.p` is minimal over
  `locusIdealS`), `LocData.eq_p_S` (two local data whose points lie on the same component give the
  same prime), `LocData.mem_of_le_p_S` (`V(D.p)` lies in the maximal locus: the `hZ` input of
  `compF_map_C`), `LocData.not_not_eq_of_sup_ne_top` (components meeting at a point coincide).
* The filtration of a component: `pow_le_compF_S`, `compF_one_div_S` (no Zorn: the point of `D`
  is used), `compF_map_of_not_le_S` (with an explicit `π ∈ D.p \ 𝔪₀`), and `compF_map_S` (from
  `compF_map_C`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- Excluded middle under `¬¬`. -/
theorem nn_em (P : Prop) : ¬¬ (P ∨ ¬ P) := fun h => h (Or.inr fun p => h (Or.inl p))

/-- The `¬¬`-closed ideal of the maximal locus. -/
def locusIdealS (I : Ideal A) (v₀ : ℕ → ℚ) : Ideal A where
  carrier := {f | ∀ 𝔪 ∈ maxLocus I v₀, ¬¬ f ∈ 𝔪}
  add_mem' := fun ha hb 𝔪 h𝔪 h =>
    ha 𝔪 h𝔪 fun ha => hb 𝔪 h𝔪 fun hb => h (add_mem ha hb)
  zero_mem' := fun _ _ h => h (zero_mem _)
  smul_mem' := fun c _ hx 𝔪 h𝔪 h => hx 𝔪 h𝔪 fun hx => h (Ideal.mul_mem_left _ c hx)

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma mem_locusIdealS {I : Ideal A} {v₀ : ℕ → ℚ} {f : A} :
    f ∈ locusIdealS I v₀ ↔ ∀ 𝔪 ∈ maxLocus I v₀, ¬¬ f ∈ 𝔪 := Iff.rfl

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma le_locusIdealS (I : Ideal A) (v₀ : ℕ → ℚ) : I ≤ locusIdealS I v₀ :=
  fun _ ha _ ⟨_, hI𝔪, _⟩ h => h (hI𝔪 ha)

/-- **Jacobson, in Nullstellensatz form**: an element `¬¬`-contained in every maximal ideal above
a prime `p` lies in `p`. -/
def JacS (A : Type) [CommRing A] : Prop :=
  ∀ (p : Ideal A) [p.IsPrime] (f : A), (∀ (𝔪 : Ideal A) [𝔪.IsMaximal], p ≤ 𝔪 → ¬¬ f ∈ 𝔪) → f ∈ p

omit [IsDomain A] in
/-- Classical source of `JacS` (`IsJacobsonRing`); to be replaced by the effective
Nullstellensatz. -/
theorem jacS_of_classical : JacS A := by
  intro p _ f hf
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ)
  have hj : p.jacobson = p := IsJacobsonRing.out inferInstance (inferInstance : p.IsPrime).isRadical
  rw [← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro 𝔪 ⟨hp𝔪, h𝔪⟩
  by_contra h
  exact hf 𝔪 hp𝔪 h

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- `InvAt` at a fixed value is stable: equality of rational sequences is `¬¬`-stable. -/
theorem invAt_of_nn {I 𝔪 : Ideal A} [𝔪.IsPrime] {v v₀ : ℕ → ℚ} (hv : InvAt I 𝔪 v)
    (h : ¬¬ v = v₀) : InvAt I 𝔪 v₀ := by
  have he : v = v₀ := funext fun i =>
    Decidable.byContradiction fun hi => h fun he => hi (congrFun he i)
  rwa [he] at hv

/-- **The maximal locus is closed**, with the stable bound `¬ (v < v₀)`: no `by_contra` on
membership, no `by_cases`. -/
theorem mem_maxLocus_of_le_S {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
    (hmaxS : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → ¬ toLex v < toLex v₀)
    (𝔪 : Ideal A) [𝔪.IsMaximal] (hle : locusIdealS I v₀ ≤ 𝔪) : I ≤ 𝔪 ∧ InvAt I 𝔪 v₀ := by
  have hI𝔪 : I ≤ 𝔪 := (le_locusIdealS I v₀).trans hle
  refine ⟨hI𝔪, ?_⟩
  obtain ⟨v, hv⟩ := exists_invAt hI 𝔪 hI𝔪
  refine invAt_of_nn hv fun hne => nn_le_total (toLex v) (toLex v₀) fun h => ?_
  rcases h with h | h
  · exact hmaxS 𝔪 hI𝔪 v hv (lt_of_le_of_ne h fun h' => hne (toLex.injective h'))
  · have hlt : toLex v₀ < toLex v := lt_of_le_of_ne h fun h' => hne (toLex.injective h').symm
    obtain ⟨g, hg, hgv⟩ := invAt_semicont hI 𝔪 hI𝔪 hv
    refine hg (hle fun 𝔪'' ⟨h𝔪'', _, hv''⟩ hg'' => ?_)
    exact lt_irrefl _ (hlt.trans_le (hgv 𝔪'' hg'' v₀ hv''))

namespace LocData

variable [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal]
  (D : LocData I v₀ 𝔪)

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- `g aᵢ` lies in the `¬¬`-closed ideal of the maximal locus. -/
lemma g_mul_num_mem_S (i : Fin D.n) (hi : (i : ℕ) < D.k) (a : A) (m : D.M)
    (hx : D.ck.x i = IsLocalization.mk' (Localization D.M) a m) :
    D.g * a ∈ locusIdealS I v₀ := by
  rintro 𝔪'' ⟨h𝔪'', hI'', hv''⟩ hn
  refine nn_em (D.g ∈ 𝔪'') fun h => ?_
  rcases h with hg'' | hg''
  · exact hn (Ideal.mul_mem_right _ _ hg'')
  · refine hn (Ideal.mul_mem_left _ _ ?_)
    have := (D.iff 𝔪'' hg'').1 ⟨hI'', hv''⟩ i hi
    rw [D.transport_x_mk' _ i a m hx,
      IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime 𝔪'') 𝔪''] at this
    exact this

omit [Algebra.Smooth ℚ A] [IsNoetherianRing A] [IsDomain A] in
/-- The chart functions lie in the extension of any ideal containing `locusIdealS`. -/
lemma P_le_map_S {𝔮 : Ideal A} (h𝔮 : locusIdealS I v₀ ≤ 𝔮) :
    D.P ≤ 𝔮.map (algebraMap A (Localization.AtPrime 𝔪)) := by
  rw [P, Ideal.span_le]
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨a, m, hx⟩ := D.exists_num i
  rw [SetLike.mem_coe, D.transport_x_mk' _ i a m hx,
    IsLocalization.mk'_mem_map_algebraMap_iff 𝔪.primeCompl]
  exact ⟨D.g, D.hg, h𝔮 (D.g_mul_num_mem_S i hi a m hx)⟩

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- **`D.p` is minimal over `locusIdealS`**: it lies below every prime between. -/
lemma p_le_of_le {𝔮 : Ideal A} [𝔮.IsPrime] (h1 : locusIdealS I v₀ ≤ 𝔮) (h2 : 𝔮 ≤ 𝔪) :
    D.p ≤ 𝔮 := by
  intro a ha
  have h := D.P_le_map_S h1 ha
  rw [← under_map_atPrime h2]
  exact h

omit [IsDomain A] [IsNoetherianRing A] in
/-- The `¬¬`-closed locus ideal lies in `D.p` (Jacobson in the form `JacS`). -/
theorem locusIdealS_le_p (hJ : JacS A) : locusIdealS I v₀ ≤ D.p := by
  intro f hf
  have hgf : D.g * f ∈ D.p := by
    refine hJ D.p _ fun 𝔪' _ hp𝔪' hn => nn_em (D.g ∈ 𝔪') fun h => ?_
    rcases h with hg' | hg'
    · exact hn (Ideal.mul_mem_right _ _ hg')
    · obtain ⟨hI', hv'⟩ := D.mem_of_p_le 𝔪' hg' hp𝔪'
      exact hf 𝔪' ⟨‹_›, hI', hv'⟩ fun h => hn (Ideal.mul_mem_left _ _ h)
  rcases (inferInstance : D.p.IsPrime).mem_or_mem hgf with h | h
  · exact absurd (D.p_le h) D.hg
  · exact h

omit [IsDomain A] [IsNoetherianRing A] in
/-- **Two local data on the same component give the same prime.** -/
theorem eq_p_S (hJ : JacS A) {𝔪' : Ideal A} [𝔪'.IsMaximal] (D' : LocData I v₀ 𝔪')
    (h : D.p ≤ 𝔪') : D.p = D'.p := by
  have h1 : D'.p ≤ D.p := D'.p_le_of_le (D.locusIdealS_le_p hJ) h
  exact le_antisymm (D.p_le_of_le (D'.locusIdealS_le_p hJ) (h1.trans D.p_le)) h1

omit [IsNoetherianRing A] in
/-- **`V(D.p)` lies in the maximal locus** (the `hZ` input of `compF_map_C`). -/
theorem mem_of_le_p_S (hI : I ≠ ⊥) (hJ : JacS A)
    (hmaxS : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → ¬ toLex v < toLex v₀)
    (𝔪' : Ideal A) [𝔪'.IsMaximal] (h : D.p ≤ 𝔪') : I ≤ 𝔪' ∧ InvAt I 𝔪' v₀ :=
  mem_maxLocus_of_le_S hI hmaxS 𝔪' ((D.locusIdealS_le_p hJ).trans h)

/-- **Components meeting at a point coincide** (`¬¬`, from `NNMax`). -/
theorem not_not_eq_of_sup_ne_top (hI : I ≠ ⊥) (hJ : JacS A) (hNS : NNMax A)
    (hmaxS : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → ¬ toLex v < toLex v₀)
    {𝔪₁ : Ideal A} [𝔪₁.IsMaximal] (D₁ : LocData I v₀ 𝔪₁) (hne : D.p ⊔ D₁.p ≠ ⊤) :
    ¬¬ D.p = D₁.p := by
  intro hpq
  refine hNS _ hne fun ⟨𝔪', h𝔪', hle⟩ => ?_
  have hZ := D.mem_of_le_p_S hI hJ hmaxS 𝔪' (le_sup_left.trans hle)
  obtain ⟨D'⟩ := LocData.nonempty hI 𝔪' hZ.1 hZ.2
  exact hpq ((D.eq_p_S hJ D' (le_sup_left.trans hle)).trans
    (D₁.eq_p_S hJ D' (le_sup_right.trans hle)).symm)

end LocData

/-! ### The filtration of the component `V(D.p)` -/

variable [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ} (hJ : JacS A)
  (hmaxS : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → ¬ toLex v < toLex v₀)
  {𝔪₁ : Ideal A} [𝔪₁.IsMaximal] (D₁ : LocData I v₀ 𝔪₁)
  {d : ℕ} (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
include hI hJ hmaxS hd hw

/-- Powers of the component prime lie in the filtration. -/
theorem pow_le_compF_S (N : ℕ) : D₁.p ^ N ≤ compF I D₁.p (N / d) := by
  intro f hf
  rw [mem_compF]
  intro 𝔪 _ h𝔭𝔪
  have hZ := D₁.mem_of_le_p_S hI hJ hmaxS 𝔪 h𝔭𝔪
  obtain ⟨D⟩ := LocData.nonempty hI 𝔪 hZ.1 hZ.2
  have hp : D₁.p = D.p := D₁.eq_p_S hJ D h𝔭𝔪
  have h1 : algebraMap A (Localization.AtPrime 𝔪) f ∈ (D₁.p ^ N).map (algebraMap A _) :=
    Ideal.mem_map_of_mem _ hf
  rw [Ideal.map_pow, hp, D.map_p] at h1
  exact D.P_pow_le hI hd hw N h1

/-- The first step of the component filtration is the component prime (no Zorn: the point of
`D₁` is used). -/
theorem compF_one_div_S : compF I D₁.p (1 / d) = D₁.p := by
  apply le_antisymm
  · intro f hf
    have h1 := mem_compF.1 hf 𝔪₁ D₁.p_le
    rw [D₁.cRF_eq_transport hI] at h1
    have h2 := Chart.RF_le_span _ D₁.ek (by positivity) h1
    have hset : {i | D₁.ek i ≠ 0} = {i : Fin D₁.n | (i : ℕ) < D₁.k} := by
      ext i; exact D₁.supp i
    rw [hset, ← LocData.P, ← D₁.map_p] at h2
    rw [← under_map_atPrime D₁.p_le]
    exact h2
  · have := pow_le_compF_S hI hJ hmaxS D₁ hd hw 1
    rwa [pow_one, Nat.cast_one] at this

/-- Away from `V(D.p)` the component filtration is trivial (with an explicit `π ∈ D.p \ 𝔪₀`). -/
theorem compF_map_of_not_le_S (𝔪₀ : Ideal A) [𝔪₀.IsMaximal] {π : A} (hπ : π ∈ D₁.p)
    (hπ𝔪 : π ∉ 𝔪₀) (t : ℚ) :
    (compF I D₁.p t).map (algebraMap A (Localization.AtPrime 𝔪₀)) = ⊤ := by
  obtain ⟨N, hN⟩ := exists_nat_ge (t * d)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hmem : π ^ N ∈ compF I D₁.p t := by
    refine compF_antitone ?_ hI (fun 𝔪 _ h𝔭𝔪' => ?_)
      (pow_le_compF_S hI hJ hmaxS D₁ hd hw N (Ideal.pow_mem_pow hπ N))
    · rw [le_div_iff₀ hdq]; exact hN
    · have hZ := D₁.mem_of_le_p_S hI hJ hmaxS 𝔪 h𝔭𝔪'
      exact ⟨hZ.1, v₀, hZ.2⟩
  have hu : IsUnit (algebraMap A (Localization.AtPrime 𝔪₀) (π ^ N)) :=
    IsLocalization.map_units _ (⟨π ^ N, 𝔪₀.primeCompl.pow_mem hπ𝔪 N⟩ : 𝔪₀.primeCompl)
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmem) hu

omit hd hw in
/-- **The filtration of `V(D.p)` localizes to the maximal centres**, from a cover. -/
theorem compF_map_S (hcov : (1 : A) ∈ D₁.p ⊔ Ideal.span {g | CertC I v₀ D₁.p g})
    (𝔪₀ : Ideal A) [𝔪₀.IsMaximal] (h𝔭𝔪 : D₁.p ≤ 𝔪₀) (t : ℚ) :
    (compF I D₁.p t).map (algebraMap A (Localization.AtPrime 𝔪₀)) = cRF I 𝔪₀ t :=
  compF_map_C hI (D₁.mem_of_le_p_S hI hJ hmaxS) hcov 𝔪₀ h𝔭𝔪 t

end BezoutCounterexample.Principalization
