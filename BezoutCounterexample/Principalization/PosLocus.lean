import BezoutCounterexample.Principalization.MaxLocusPtCore
import BezoutCounterexample.Principalization.PosWire

/-!
# Generators of the locus ideal, positively (option 2, (A); leaf, read-only on coll-8a's files)

Replaces the classical `exists_locusIdeal_gens` (generators of `locusIdeal I v₀` from
`IsNoetherianRing A`) by a positive construction, under the LocData standard: points are explicit
(`HasPres.exists_point`), Noetherian finite generation is used only inside `LocData`.

* `LocGens I v₀ g a`: on `D(g)` the maximal locus is `V(a)` (`g aᵢ ∈ locusIdeal`, and every point of
  `D(g) ∩ V(a)` lies in the locus).
* `LocData.exists_locGens`: a chart of local data gives local generators (its numerators).
* `exists_locGens_step`: at an explicit point of `V(I + (l))`, compute the invariant `v`; if
  `v = v₀` (decided: supports are bounded by the chart size `N`), the local data give `LocGens`, otherwise the
  semicontinuity neighbourhood `D(g)` misses the locus (`LocGens g [1]`).
* `exists_locusIdeal_gens_pos`: bar induction (`Constructive.exists_cover`) gives a cover
  `1 ∈ I + (g₁, …, g_r)` with `LocGens gⱼ aⱼ`, and
  `locusIdeal I v₀ = {x | ∀ j, x/1 ∈ √(aⱼ) A[1/gⱼ]}`, explicit by `HasPres.exists_radical` and
  `HasPres.exists_gens_of_charts`. `⊆`: if `x/1 ∉ √(aⱼ) A[1/gⱼ]`, i.e. `1 ∉ (aⱼ) A[1/(gⱼ x)]`
  (decided by `mem_dec`), an explicit point of `A[1/(gⱼ x)]` is a locus point not containing `x`.
  `⊇`: `gⱼ x ∈ 𝔪` for every locus point `𝔪` and every `j`, and `x ∈ 𝔪` by the cover.

Classical steps (all of the kind used in `Principalization`): those inside `LocData`
(`LocData.nonempty`, `exists_invAt`, `invAt_semicont`, `LocData.g_mul_num_mem`) and one `by_contra`
on membership in a maximal ideal (`locGens_of_ne`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing

section Aux

/-- Finite choice over a list. -/
lemma exists_pairs {α β : Type*} (P : α → β → Prop) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, P a b) →
      ∃ ps : List (α × β), ps.map Prod.fst = l ∧ ∀ p ∈ ps, P p.1 p.2
  | [], _ => ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨ps, hps, hP⟩ := exists_pairs P l fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨(a, b) :: ps, by rw [List.map_cons, hps], fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hb
    · exact hP p hp

/-- Membership of `x/1` in an extended ideal of `R[1/g]`. -/
lemma exists_pow_mul_mem_of_away {R : Type*} [CommRing R] (g : R) (L : Type*) [CommRing L]
    [Algebra R L] [IsLocalization.Away g L] {J : Ideal R} {x : R}
    (h : algebraMap R L x ∈ J.map (algebraMap R L)) : ∃ n : ℕ, g ^ n * x ∈ J := by
  obtain ⟨⟨⟨a, ha⟩, ⟨_, n, rfl⟩⟩, hx⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g) L).1 h
  simp only at hx
  rw [← map_mul] at hx
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers g) L).1 hx
  refine ⟨k + n, ?_⟩
  simp only at hk
  rw [pow_add, mul_assoc, mul_comm (g ^ n) x, hk]
  exact J.mul_mem_left _ ha

/-- `x/1 = (g x)/1 · g⁻¹` in `R[1/g]`. -/
lemma algebraMap_mem_of_mul_mem {R : Type*} [CommRing R] (g : R) (L : Type*) [CommRing L]
    [Algebra R L] [IsLocalization.Away g L] {J : Ideal R} {x : R} (h : g * x ∈ J) :
    algebraMap R L x ∈ J.map (algebraMap R L) := by
  have : algebraMap R L x = algebraMap R L (g * x) * IsLocalization.Away.invSelf g := by
    rw [map_mul, mul_comm (algebraMap R L g), mul_assoc, IsLocalization.Away.mul_invSelf,
      mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h)

/-- `x · (l) ⊆ 𝔪` from the generators. -/
lemma lspan_le_comap_mul {R : Type*} [CommRing R] (x : R) (l : List R) (J : Ideal R)
    (h : ∀ a ∈ l, x * a ∈ J) : ∀ y ∈ Constructive.lspan l, x * y ∈ J := by
  have hle : Constructive.lspan l ≤ Submodule.comap (LinearMap.mulLeft R x) J := by
    rw [Constructive.lspan, Ideal.span_le]
    intro a ha
    exact h a ha
  intro y hy
  exact hle hy

end Aux

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ}

/-- **Local generators of the maximal locus** on `D(g)`: the locus is `V(a) ∩ D(g)`. -/
def LocGens (I : Ideal A) (v₀ : ℕ → ℚ) (g : A) (a : List A) : Prop :=
  (∀ b ∈ a, g * b ∈ locusIdeal I v₀) ∧
    ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], g ∉ 𝔪 → (∀ b ∈ a, b ∈ 𝔪) → I ≤ 𝔪 ∧ InvAt I 𝔪 v₀

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- **Local data give local generators**: the numerators of the first `k` chart functions. -/
theorem LocData.exists_locGens {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) :
    ∃ a : List A, LocGens I v₀ D.g a := by
  obtain ⟨f, hf⟩ := exists_fun_fin
    (fun i (am : A × D.M) => D.ck.x i = IsLocalization.mk' (Localization D.M) am.1 am.2)
    (fun i => by obtain ⟨a, m, h⟩ := D.exists_num i; exact ⟨(a, m), h⟩)
  refine ⟨((List.finRange D.n).filter (fun i : Fin D.n => decide ((i : ℕ) < D.k))).map
    (fun i => (f i).1),
    ?_, ?_⟩
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    have hik : (i : ℕ) < D.k := by simpa using (List.mem_filter.1 hi).2
    exact D.g_mul_num_mem i hik _ _ (hf i)
  · intro 𝔪' _ hg' hall
    rw [D.iff 𝔪' hg']
    intro i hi
    rw [D.transport_x_mk' _ i _ _ (hf i),
      IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime 𝔪') 𝔪']
    exact hall _ (List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_finRange i, decide_eq_true hi⟩,
      rfl⟩)

omit [IsDomain A] [Algebra.Smooth ℚ A] [IsNoetherianRing A] in
/-- **A neighbourhood missing the locus**: if the invariant `v ≠ v₀` at `𝔪` bounds the invariants
on `D(g)` from below, the locus does not meet `D(g)`. -/
theorem locGens_of_ne
    (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
    {𝔪 : Ideal A} [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪) {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) (hne : v ≠ v₀)
    {g : A} (hbound : ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], g ∉ 𝔪' → ∀ v', InvAt I 𝔪' v' →
      toLex v ≤ toLex v') : LocGens I v₀ g [1] := by
  refine ⟨fun b hb => ?_, fun 𝔪' _ _ hall => ?_⟩
  · rw [List.mem_singleton] at hb
    subst hb
    rw [mul_one, mem_locusIdeal]
    rintro 𝔪'' ⟨h𝔪'', -, hv''⟩
    by_contra hg''
    exact hne (toLex.injective (le_antisymm (hbound 𝔪'' hg'' v₀ hv'') (hmax 𝔪 hI𝔪 v hv)))
  · exact absurd ((Ideal.eq_top_iff_one _).2 (hall 1 List.mem_cons_self))
      (Ideal.IsMaximal.ne_top inferInstance)

omit [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] in
/-- Classical generators of an ideal (`IsNoetherianRing`): the input datum `I` of the
principalization, the classical input that remains once the locus ideal is explicit. -/
theorem exists_ideal_gens (I : Ideal A) : ∃ gens : List A, I = Constructive.lspan gens := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  refine ⟨s.toList, ?_⟩
  rw [Constructive.lspan]
  conv_lhs => rw [← hs]
  congr 1
  ext x
  simp

variable (hI : I ≠ ⊥)
  (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
  {N : ℕ} (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0)
  (hb₀ : ∀ i, N ≤ i → v₀ i = 0)
include hI hmax hbd hb₀

/-- **One step of the cover**: at an explicit point of `V(I + (l))`, a neighbourhood with local
generators of the locus. -/
theorem exists_locGens_step (hp : HasPres A) (gens : List A) (hgens : I = Constructive.lspan gens)
    (l : List A) (h1 : (1 : A) ∉ I ⊔ Constructive.lspan l) :
    ∃ g, (∃ a, LocGens I v₀ g a) ∧ g ∉ I ⊔ Constructive.lspan l := by
  obtain ⟨L, _, _, _, z, -, hz⟩ :=
    explicitNS_of_hasPres hp (gens ++ l) fun h => h1 (lspan_append_le hgens h)
  have := ker_isMaximal z
  have hle := sup_le_ker hgens z hz
  have hI𝔪 : I ≤ RingHom.ker z := le_sup_left.trans hle
  obtain ⟨v, hv⟩ := exists_invAt hI _ hI𝔪
  obtain ⟨g, hg, hbound⟩ := invAt_semicont hI _ hI𝔪 hv
  rcases eq_or_ne_bounded (hbd _ _ hv) hb₀ with heq | hne
  · obtain ⟨D⟩ := LocData.nonempty hI _ hI𝔪 (heq ▸ hv)
    exact ⟨D.g, D.exists_locGens, fun h => D.hg (hle h)⟩
  · exact ⟨g, ⟨[1], locGens_of_ne hmax hI𝔪 hv hne hbound⟩, fun h => hg (hle h)⟩

/-- **Generators of the locus ideal, positively**: from a presentation of `A`, generators of `I`
and a bound `N` on the supports of the invariants. Replaces the classical
`exists_locusIdeal_gens`. -/
theorem exists_locusIdeal_gens_pos (hp : HasPres A) (gens : List A)
    (hgens : I = Constructive.lspan gens) :
    ∃ Pg : List A, locusIdeal I v₀ = Constructive.lspan Pg := by
  have hdec : ∀ l : List A, (1 : A) ∈ I ⊔ Constructive.lspan l ∨
      (1 : A) ∉ I ⊔ Constructive.lspan l := fun l => by
    rw [hgens, ← lspan_append_eq]; exact hp.mem_dec _ 1
  obtain ⟨l, hl, h1⟩ := Constructive.exists_cover I (indNoeth_quotient_of_hasPres hp I)
    (fun g => ∃ a, LocGens I v₀ g a) hdec
    fun l _ hl1 => exists_locGens_step hI hmax hbd hb₀ hp gens hgens l hl1
  -- local generators and their radicals, for each element of the cover
  obtain ⟨ps, hps, hP⟩ := exists_pairs
    (fun g (aR : List A × List A) => LocGens I v₀ g aR.1 ∧
      Constructive.lspan aR.2 = (Constructive.lspan aR.1).radical) l fun g hg => by
    obtain ⟨a, ha⟩ := hl g hg
    obtain ⟨R, hR⟩ := hp.exists_radical a
    exact ⟨(a, R), ha, hR⟩
  set gf : Fin ps.length → A := fun k => (ps.get k).1
  obtain ⟨Pg, hPg⟩ := hp.exists_gens_of_charts gf
    (fun k => (ps.get k).2.2.map (algebraMap A (Localization.Away (gf k))))
  refine ⟨Pg, le_antisymm (fun x hx => (hPg x).2 fun k => ?_) fun x hx => ?_⟩
  · -- `⊆`: the explicit point of `A[1/(g x)]`
    have hk := hP _ (List.get_mem ps k)
    set g := gf k
    set a := (ps.get k).2.1
    rw [lspan_map, hk.2]
    refine algebraMap_mem_of_mul_mem g _ ?_
    let Lc := Localization.Away (g * x)
    have hpc := hp.away (g * x) Lc
    rcases hpc.mem_dec (a.map (algebraMap A Lc)) 1 with h | h
    · rw [lspan_map, ← map_one (algebraMap A Lc)] at h
      obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_away (g * x) Lc h
      exact ⟨n, by rwa [mul_one] at hn⟩
    · exfalso
      obtain ⟨L, _, _, _, z, -, hz, -⟩ := hpc.exists_point _ h
      let zA : A →+* L := z.comp (algebraMap A Lc)
      have := ker_isMaximal zA.toRatAlgHom
      have hgx : g * x ∉ RingHom.ker zA.toRatAlgHom := by
        rw [RingHom.mem_ker]
        exact ((IsLocalization.Away.algebraMap_isUnit (g * x)).map z).ne_zero
      have hg : g ∉ RingHom.ker zA.toRatAlgHom := fun h' => hgx (Ideal.mul_mem_right _ _ h')
      have ha : ∀ b ∈ a, b ∈ RingHom.ker zA.toRatAlgHom := fun b hb => by
        rw [RingHom.mem_ker]; exact hz _ (List.mem_map_of_mem hb)
      obtain ⟨hI', hv'⟩ := hk.1.2 _ hg ha
      exact hgx (Ideal.mul_mem_left _ _ ((mem_locusIdeal.1 hx) _ ⟨this, hI', hv'⟩))
  · -- `⊇`: `g x ∈ 𝔪` for each element `g` of the cover
    rw [mem_locusIdeal]
    rintro 𝔪 ⟨h𝔪, hI𝔪, hv𝔪⟩
    have hgx : ∀ g ∈ l, x * g ∈ 𝔪 := by
      intro g hg
      rw [← hps] at hg
      obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hg
      obtain ⟨k, rfl⟩ := List.get_of_mem hp'
      have hk := hP _ (List.get_mem ps k)
      have hx' := (hPg x).1 hx k
      rw [lspan_map, hk.2] at hx'
      obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_away (gf k) _ hx'
      obtain ⟨M, hM⟩ := hn
      have hga := lspan_le_comap_mul (gf k) _ 𝔪
        (fun b hb => (mem_locusIdeal.1 (hk.1.1 b hb)) 𝔪 ⟨h𝔪, hI𝔪, hv𝔪⟩) _ hM
      rw [mul_comm x]
      rcases h𝔪.isPrime.mem_or_mem hga with h | h
      · exact Ideal.mul_mem_right _ _ h
      · rcases h𝔪.isPrime.mem_or_mem (h𝔪.isPrime.mem_of_pow_mem _ h) with h | h
        · exact Ideal.mul_mem_right _ _ (h𝔪.isPrime.mem_of_pow_mem _ h)
        · exact Ideal.mul_mem_left _ _ h
    obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 h1
    have : x = x * i + x * y := by rw [← mul_add, hiy, mul_one]
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hI𝔪 hi)) (lspan_le_comap_mul x l 𝔪 hgx y hy)

omit hbd hb₀ in
/-- The same, with the support bound read off the chart at a point where `v₀` is attained (chart
sizes are constant on a domain, `invAt_bounded_of_chart`; no dimension theory). -/
theorem exists_locusIdeal_gens_attained (hp : HasPres A) (gens : List A)
    (hgens : I = Constructive.lspan gens) {𝔪₀ : Ideal A} [𝔪₀.IsMaximal] (hv₀ : InvAt I 𝔪₀ v₀) :
    ∃ Pg : List A, locusIdeal I v₀ = Constructive.lspan Pg := by
  obtain ⟨n, e, ⟨⟨J, -, -⟩, -⟩, -⟩ := id hv₀
  have hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, n ≤ i → v i = 0 :=
    fun _ _ _ hv => invAt_bounded_of_chart J.c hv
  exact exists_locusIdeal_gens_pos hI hmax hbd (hbd _ _ hv₀) hp gens hgens

end BezoutCounterexample.Principalization
