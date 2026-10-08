import BezoutCounterexample.Principalization.DivisorialPt
import BezoutCounterexample.Principalization.ReesPres
import BezoutCounterexample.Principalization.ReesVertex

/-!
# Lemma 4.3 (the torsor decrease) at points (D3.5, leaf)

`PrincipalizationData.torsor_invariant` (top level, `Torsor.lean`) compares `maxinv(I₁)` with
`maxinv(I)` by `by_cases`, identifies the components of `I₁ = I_w U` with the `𝔭' U`, `𝔭' ≠ 𝔭`,
through `components_eq_of` (Jacobson, `IsJacobsonRing.out'`), and counts them with `Set.ncard`.
Here, on the torsor `U` of `TorsorInv` and with the maximal invariant as a relation
(`docs/d3-design.md` §5, D3.5; rewrite-tasks C8), everything is read off explicit points:

* `Pt.comap`: the point of `A` under a point of `U` (`ker` is the contraction);
* `torsor_locus_down`, `torsor_locus_up`: a point `q` of `U` lies in the locus of `I₁` (with
  invariant `v₀`) iff `s ∉ q` and `q ∩ A` lies in the locus of `I` (from `torsor_invAt`, with
  `InvAt.unique`);
* `exists_torsorY_not_mem_map_pt`, `torsor_comp_isPrime_pt`: the other components stay prime on
  `U` (point forms of `exists_torsorY_not_mem_map`, `torsor_comp_isPrime`; the generator of `F₁`
  outside `𝔭'` is found by a search decided by (G), not by `by_contra`);
* `torsor_locusPt_le_map`, `torsor_mem_locusPt_of_forall`: `locusPt I₁ v₀ = ⋂_{𝔭' ≠ 𝔭} 𝔭' U`
  (both inclusions, elementwise);
* `torsor_count_pt`: with `NumComp`, `k₁ < k` (the components of `I₁` are the `𝔭' U`, `𝔭' ≠ 𝔭`;
  `exists_le_of_forall_mem` finds the `𝔭' U` below a prime above `⋂ 𝔭' U` by a decided search);
* `torsor_decrease_pt`: `v₁ ≺ v₀ ∨ (v₁ = v₀ ∧ k₁ < k)` for `IsMaxInv I₁ v₁` and `NumComp`.

These replace `components_eq_of`, `minimalPrimes_sInf_subset`/`torsor_count` and the
`by_cases` of `torsor_invariant` on the path. Leaf module; no `classical`, no `by_contra`, no
`Set.ncard`. `torsor_invAt` itself (group C of the D3.5 plan) is used as it is.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing IsLocalization LaurentPolynomial

/-! ### Points under a ring map -/

section PtComap

variable {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

/-- The point of `A` under a point of `B`. -/
def Pt.comap (f : A →+* B) (q : Pt B) : Pt A :=
  ⟨q.L, (q.z.toRingHom.comp f).toRatAlgHom, q.dec⟩

lemma Pt.ker_comap (f : A →+* B) (q : Pt B) : (q.comap f).ker = q.ker.comap f := by
  ext x
  rw [Ideal.mem_comap, Pt.mem_ker, Pt.mem_ker]
  rfl

end PtComap

/-! ### A prime above an intersection contains a member (decided search) -/

section Search

variable {R : Type} [CommRing R]

/-- **A prime containing `⋂ Jᵢ` (over the good indices) contains some good `Jᵢ`**, by a search
decided by (G): otherwise the product of witnesses `xᵢ ∈ Jᵢ ∖ P` lies in `⋂ Jᵢ ∖ P`. -/
theorem exists_le_of_forall_mem (hp : HasPres R) {ι : Type*} {Dg : List R}
    (hD : (lspan Dg).IsPrime) (good : ι → Prop) (hgood : ∀ i, good i ∨ ¬ good i)
    (J : ι → List R) (Is : List ι)
    (h : ∀ y, (∀ i ∈ Is, good i → y ∈ lspan (J i)) → y ∈ lspan Dg) :
    ∃ i ∈ Is, good i ∧ lspan (J i) ≤ lspan Dg := by
  have key : ∀ Is : List ι, (∃ i ∈ Is, good i ∧ lspan (J i) ≤ lspan Dg) ∨
      ∃ x, x ∉ lspan Dg ∧ ∀ i ∈ Is, good i → x ∈ lspan (J i) := by
    intro Is
    induction Is with
    | nil =>
      exact Or.inr ⟨1, (Ideal.ne_top_iff_one _).1 hD.ne_top,
        fun _ hi => absurd hi List.not_mem_nil⟩
    | cons i Is ih =>
      rcases ih with ⟨i', hi', hg, hle⟩ | ⟨x, hx, hxJ⟩
      · exact Or.inl ⟨i', List.mem_cons_of_mem _ hi', hg, hle⟩
      rcases hgood i with hg | hg
      · rcases (HasPres.le_dec hp) (J i) Dg with hle | hle
        · exact Or.inl ⟨i, List.mem_cons_self .., hg, hle⟩
        · -- a generator of `J i` outside `P`
          rcases list_exists_or_forall (P := fun z => z ∉ lspan Dg)
            (fun z => ((HasPres.mem_dec hp) Dg z).elim (fun h => Or.inr fun h' => h' h) Or.inl) (J i) with
            ⟨z, hz, hzD⟩ | hall
          · refine Or.inr ⟨x * z, fun hxz => (hD.mem_or_mem hxz).elim hx hzD, ?_⟩
            intro i' hi' hg'
            rcases List.mem_cons.1 hi' with rfl | hi'
            · exact Ideal.mul_mem_left _ _ (Ideal.subset_span hz)
            · exact Ideal.mul_mem_right _ _ (hxJ i' hi' hg')
          · exfalso
            refine hle ?_
            rw [lspan, Ideal.span_le]
            intro z hz
            rcases (HasPres.mem_dec hp) Dg z with h | h
            · exact h
            · exact absurd h (hall z hz)
      · refine Or.inr ⟨x, hx, fun i' hi' hg' => ?_⟩
        rcases List.mem_cons.1 hi' with rfl | hi'
        · exact absurd hg' hg
        · exact hxJ i' hi' hg'
  rcases key Is with h' | ⟨x, hx, hxJ⟩
  · exact h'
  · exact absurd (h x hxJ) hx

end Search

/-! ### The torsor at points -/

section TorsorPt

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] [hpA : Fact (HasPres A)]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  (hπ0 : π ≠ 0)

include hd hw hπ0 in
/-- **Points of the new locus lie off `s`, over the old locus.** -/
theorem torsor_locus_down [Fact (Constructive.HasPres A)] [Constructive.Enum A] [Fact (∃ k, ChartDim A k)] (q : Pt (Torsor hI hmax h𝔭 d hπ))
    (hIq : torsorI hI hmax h𝔭 hd hπ ≤ q.ker) (hv : InvAt (torsorI hI hmax h𝔭 hd hπ) q.ker v₀) :
    torsorS hI hmax h𝔭 hπ ∉ q.ker ∧
      I ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker ∧
      ¬ 𝔭 ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker ∧
      InvAt I (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker v₀ := by
  rcases torsor_invAt hI hmax h𝔭 hd hw hπ hπ0 q.ker hIq hv with ⟨-, hlt⟩ | ⟨hs, hI', h𝔭', hv'⟩
  · exact absurd hlt (lt_irrefl _)
  · have hk := Pt.ker_comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) q
    exact ⟨hs, hI'.trans hk.ge, fun h => h𝔭' (h.trans hk.le), InvAt.congr_pt hk.symm hv'⟩

include hd hw hπ0 in
/-- **Points off `s` over the old locus lie in the new locus.** -/
theorem torsor_locus_up [Fact (Constructive.HasPres A)] [Constructive.Enum A] [Fact (∃ k, ChartDim A k)] (q : Pt (Torsor hI hmax h𝔭 d hπ))
    (hs : torsorS hI hmax h𝔭 hπ ∉ q.ker)
    (hIq : I ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker)
    (hv : InvAt I (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker v₀) :
    torsorI hI hmax h𝔭 hd hπ ≤ q.ker ∧ InvAt (torsorI hI hmax h𝔭 hd hπ) q.ker v₀ := by
  have : IsDomain (Torsor hI hmax h𝔭 d hπ) := torsor_isDomain hI hmax h𝔭 hπ hπ0
  have : Algebra.Smooth ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_smooth hI hmax h𝔭 hd hw hπ
  have hP := q.ker_isMaximal.isPrime
  have hle : torsorI hI hmax h𝔭 hd hπ ≤ q.ker := by
    have h1 : I.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) ≤ q.ker :=
      Ideal.map_le_iff_le_comap.2 (hIq.trans (Pt.ker_comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) q).le)
    rw [torsor_map_eq hI hmax h𝔭 hd hπ] at h1
    intro f hf
    rcases hP.mem_or_mem (h1 (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hf)) with h | h
    · exact absurd (hP.mem_of_pow_mem d h) hs
    · exact h
  refine ⟨hle, ?_⟩
  obtain ⟨v, hv'⟩ := exists_invAt (torsorI_ne_bot hI hmax h𝔭 hd hπ hπ0) q.ker hle
  rcases torsor_invAt hI hmax h𝔭 hd hw hπ hπ0 q.ker hle hv' with ⟨hs', -⟩ | ⟨-, -, -, hv''⟩
  · exact absurd hs' hs
  · have h' : InvAt I (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker v :=
      InvAt.congr_pt (Pt.ker_comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) q).symm hv''
    obtain rfl : v = v₀ := h'.unique hv
    exact hv'

include hd hw hπ0 in
/-- The old locus ideal maps into the new one. -/
theorem torsor_map_locusPt_le [Fact (Constructive.HasPres A)] [Constructive.Enum A] [Fact (∃ k, ChartDim A k)] :
    (locusPt I v₀).map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) ≤
      locusPt (torsorI hI hmax h𝔭 hd hπ) v₀ := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx q hIq hv
  obtain ⟨-, hI', -, hv'⟩ := torsor_locus_down hI hmax h𝔭 hd hw hπ hπ0 q hIq hv
  have := hx _ hI' hv'
  rw [Pt.ker_comap] at this
  exact this

include hd hw in
/-- **A generator of `F₁` off another component** (point form of `exists_torsorY_not_mem_map`;
the generator is found by a search over the generators of `F₁`, decided by (G)). -/
lemma exists_torsorY_not_mem_map_pt [Fact (Constructive.HasPres A)] [Constructive.Enum A] {𝔭' : Ideal A} (h𝔭' : LocusComp I v₀ 𝔭') (hne : 𝔭 ≠ 𝔭') :
    ∃ l, torsorY hI hmax h𝔭 d hπ l ∉
      𝔭'.map (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d))) := by
  have hF1 : ¬ (compFil hI hmax h𝔭 d).F 1 ≤ 𝔭' := by
    intro hle
    rw [compFil_F, show ((1 : ℤ) : ℚ) / d = 1 / d by push_cast; ring,
      h𝔭.compFPt_one_divP hI hmax hd hw] at hle
    have := h𝔭.sup_eq_topP hI hmax h𝔭' hne
    rw [sup_eq_right.2 hle] at this
    exact h𝔭'.isPrime.ne_top this
  obtain ⟨C, hC, -⟩ := h𝔭'.gens
  set l₀ := gensF hI hmax h𝔭 d 1
  have hmem : ∀ g, g ∈ gensF hI hmax h𝔭 d 1 ↔ g ∈ l₀ := fun g => Iff.rfl
  obtain ⟨g, hg, hg'⟩ : ∃ g ∈ gensF hI hmax h𝔭 d 1, g ∉ 𝔭' := by
    rcases list_exists_or_forall (P := fun x => x ∉ 𝔭')
      (fun x => ((HasPres.mem_dec hpA.out) C x).elim (fun h => Or.inr fun h' => h' (hC ▸ h))
        fun h => Or.inl (hC ▸ h)) l₀ with ⟨g, hg, hg'⟩ | hall
    · exact ⟨g, (hmem g).2 hg, hg'⟩
    · exfalso
      apply hF1
      rw [← span_gensF, Ideal.span_le]
      intro x hx
      rcases (HasPres.mem_dec hpA.out) C x with h | h
      · exact hC ▸ h
      · exact absurd (hC ▸ h) (hall x ((hmem x).1 hx))
  obtain ⟨l, hl1, hl2⟩ := exists_index hI hmax h𝔭 (π := π) le_rfl (by exact_mod_cast hd) hg
  refine ⟨l, fun hmem' => hg' ?_⟩
  rw [map_eq_ker_reesRed _ _ (compFil_sup_eq_top_pt hI hmax h𝔭 hd hw h𝔭' hne),
    RingHom.mem_ker] at hmem'
  have h1 := congrArg (fun p => p.coeff 1) hmem'
  simp only [reesRed_coeff] at h1
  have h2 : ((torsorY hI hmax h𝔭 d hπ l : ReesAlg (compFil hI hmax h𝔭 d)) : A[T;T⁻¹]).coeff 1 = g := by
    simp [torsorY, hl1, hl2, coeff_C_mul_T]
  have h3 : Ideal.Quotient.mk 𝔭' g = 0 := by
    rw [← h2]; simpa using h1
  exact Ideal.Quotient.eq_zero_iff_mem.1 h3

include hd hw in
/-- **The other components stay prime on the torsor** (point form of `torsor_comp_isPrime`). -/
theorem torsor_comp_isPrime_pt [Fact (Constructive.HasPres A)] [Constructive.Enum A] {𝔭' : Ideal A} (h𝔭' : LocusComp I v₀ 𝔭') (hne : 𝔭 ≠ 𝔭') :
    (𝔭'.map (algebraMap A (Torsor hI hmax h𝔭 d hπ))).IsPrime := by
  have := h𝔭'.isPrime
  have : (𝔭'.map (algebraMap A (ReesAlg (compFil hI hmax h𝔭 d)))).IsPrime :=
    isPrime_map_rees _ _ (compFil_sup_eq_top_pt hI hmax h𝔭 hd hw h𝔭' hne)
  obtain ⟨l, hl⟩ := exists_torsorY_not_mem_map_pt hI hmax h𝔭 hd hw hπ h𝔭' hne
  rw [IsScalarTower.algebraMap_eq A (ReesAlg (compFil hI hmax h𝔭 d)) (Torsor hI hmax h𝔭 d hπ),
    ← Ideal.map_map]
  exact Jou.isPrime_map _ hl

include hd hw in
/-- `𝔭 U` and `𝔭' U` are comaximal. -/
theorem torsor_map_sup_eq_top [Fact (Constructive.HasPres A)] [Constructive.Enum A] {𝔭' : Ideal A} (h𝔭' : LocusComp I v₀ 𝔭') (hne : 𝔭 ≠ 𝔭') :
    𝔭.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) ⊔
      𝔭'.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) = ⊤ := by
  rw [← Ideal.map_sup, h𝔭.sup_eq_topP hI hmax h𝔭' hne, Ideal.map_top]

include hd hw in
/-- `s ∉ 𝔭' U` for another component `𝔭'`. -/
theorem torsor_s_not_mem_map [Fact (Constructive.HasPres A)] [Constructive.Enum A] {𝔭' : Ideal A} (h𝔭' : LocusComp I v₀ 𝔭') (hne : 𝔭 ≠ 𝔭') :
    torsorS hI hmax h𝔭 hπ ∉ 𝔭'.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
  intro hs
  have hP := torsor_comp_isPrime_pt hI hmax h𝔭 hd hw hπ h𝔭' hne
  have h1 : 𝔭.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) ≤
      𝔭'.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) :=
    Ideal.map_le_iff_le_comap.2 (le_comap_of_s_mem hI hmax h𝔭 hd hw hπ _ hs)
  have h2 := torsor_map_sup_eq_top hI hmax h𝔭 hd hw hπ h𝔭' hne
  rw [sup_eq_right.2 h1] at h2
  exact hP.ne_top h2

include hd hw hπ0 in
/-- **The new locus lies in `𝔭' U`** for every other component `𝔭'`: at a point of `V(𝔭' U)`
off `s · y` (`exists_pt_away` on the presented torsor), `y` would vanish. -/
theorem torsor_locusPt_le_map [Fact (Constructive.HasPres A)] [Constructive.Enum A] [Fact (∃ k, ChartDim A k)] {𝔭' : Ideal A} (h𝔭' : LocusComp I v₀ 𝔭') (hne : 𝔭 ≠ 𝔭') :
    locusPt (torsorI hI hmax h𝔭 hd hπ) v₀ ≤ 𝔭'.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
  have hU : HasPres (Torsor hI hmax h𝔭 d hπ) := hasPres_torsor hI hmax h𝔭 hd hw hpA.out hπ
  have hP := torsor_comp_isPrime_pt hI hmax h𝔭 hd hw hπ h𝔭' hne
  have hs := torsor_s_not_mem_map hI hmax h𝔭 hd hw hπ h𝔭' hne
  obtain ⟨C, hC, -⟩ := h𝔭'.gens
  have hCU : 𝔭'.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) =
      lspan (C.map (algebraMap A (Torsor hI hmax h𝔭 d hπ))) := by
    rw [lspan_map, hC]
  intro y hy
  rcases (HasPres.mem_dec hU) (C.map (algebraMap A (Torsor hI hmax h𝔭 d hπ))) y with h | h
  · exact hCU ▸ h
  · exfalso
    rw [← hCU] at h
    have hsy : ∀ k : ℕ, (torsorS hI hmax h𝔭 hπ * y) ^ k ∉
        lspan (C.map (algebraMap A (Torsor hI hmax h𝔭 d hπ))) := fun k hk =>
      (hP.mem_or_mem (hP.mem_of_pow_mem k (hCU ▸ hk))).elim hs h
    obtain ⟨q, hq, hqy⟩ := (HasPres.exists_pt_away hU) _ _ hsy
    rw [← hCU] at hq
    have hp : 𝔭' ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker := by
      rw [Pt.ker_comap]; exact Ideal.map_le_iff_le_comap.1 hq
    obtain ⟨hIp, hv⟩ := h𝔭'.mem hI hmax _ hp
    have hsq : torsorS hI hmax h𝔭 hπ ∉ q.ker := fun h' => hqy (Ideal.mul_mem_right _ _ h')
    obtain ⟨h₁, hv₁⟩ := torsor_locus_up hI hmax h𝔭 hd hw hπ hπ0 q hsq hIp hv
    exact hqy (Ideal.mul_mem_left _ _ (hy q h₁ hv₁))

include hd hw hπ0 in
/-- **`⋂_{𝔭' ≠ 𝔭} 𝔭' U` lies in the new locus**: a point of the new locus lies over a point of the
old locus off `𝔭`, hence above some other component. -/
theorem torsor_mem_locusPt_of_forall [Fact (Constructive.HasPres A)] [Constructive.Enum A] [Fact (∃ k, ChartDim A k)] {Pg : List A} (hPg : locusPt I v₀ = lspan Pg)
    {Cs : List (List A)} (hC : IsCompList Pg Cs) {y : Torsor hI hmax h𝔭 d hπ}
    (hy : ∀ C ∈ Cs, lspan C ≠ 𝔭 → y ∈ (lspan C).map (algebraMap A (Torsor hI hmax h𝔭 d hπ))) :
    y ∈ locusPt (torsorI hI hmax h𝔭 hd hπ) v₀ := by
  intro q hIq hv
  obtain ⟨-, hI', h𝔭q, hv'⟩ := torsor_locus_down hI hmax h𝔭 hd hw hπ hπ0 q hIq hv
  have hL : lspan Pg ≤ (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).ker :=
    hPg ▸ fun f hf => hf _ hI' hv'
  obtain ⟨C, hCm, hCq⟩ := hC.exists_le (Pt.ker_isMaximal _).isPrime hL
  have hne : lspan C ≠ 𝔭 := fun h' => h𝔭q (h' ▸ hCq)
  have := hy C hCm hne
  rw [Pt.ker_comap] at hCq
  exact Ideal.map_le_iff_le_comap.2 hCq this

include hd hw hπ0 in
/-- **The number of components drops on the torsor** (the `NumComp` form of `torsor_count`). -/
theorem torsor_count_pt [Fact (Constructive.HasPres A)] [Constructive.Enum A] [Fact (∃ k, ChartDim A k)] {Pg : List A} (hPg : locusPt I v₀ = lspan Pg)
    {Pg₁ : List (Torsor hI hmax h𝔭 d hπ)}
    (hPg₁ : locusPt (torsorI hI hmax h𝔭 hd hπ) v₀ = lspan Pg₁) {k k₁ : ℕ} (hk : NumComp Pg k)
    (hk₁ : NumComp Pg₁ k₁) : k₁ < k := by
  have hU : HasPres (Torsor hI hmax h𝔭 d hπ) := hasPres_torsor hI hmax h𝔭 hd hw hpA.out hπ
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  obtain ⟨Cs, hC, rfl⟩ := hk
  obtain ⟨Ds, hD, rfl⟩ := hk₁
  obtain ⟨G, hG, -⟩ := h𝔭.gens
  have hgood : ∀ C : List A, lspan C ≠ 𝔭 ∨ ¬ lspan C ≠ 𝔭 := fun C => by
    rcases (HasPres.le_dec hpA.out) C G with h1 | h1
    · rcases (HasPres.le_dec hpA.out) G C with h2 | h2
      · exact Or.inr fun h' => h' (hG ▸ le_antisymm h1 h2)
      · exact Or.inl fun h' => h2 (hG ▸ h' ▸ le_rfl)
    · exact Or.inl fun h' => h1 (hG ▸ h' ▸ le_rfl)
  have hcomp : ∀ C ∈ Cs, LocusComp I v₀ (lspan C) := fun C hCm =>
    hC.locusComp hPg hbd hb₀ h𝔭.gensI h𝔭.chartn hCm
  -- each component of `I₁` is `𝔭' U` for another component `𝔭'` of `I`
  have hmap : ∀ D ∈ Ds, ∃ C ∈ Cs, lspan C ≠ 𝔭 ∧
      lspan D = (lspan C).map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
    intro D hDm
    have hDp := hD.isPrime hDm
    obtain ⟨C, hCm, hCg, hCD⟩ := exists_le_of_forall_mem hU hDp (fun C => lspan C ≠ 𝔭) hgood
      (fun C => C.map (algebraMap A (Torsor hI hmax h𝔭 d hπ))) Cs fun y hy =>
        hD.le D hDm (hPg₁ ▸ torsor_mem_locusPt_of_forall hI hmax h𝔭 hd hw hπ hπ0 hPg hC
          fun C hCm hCg => lspan_map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) C ▸ hy C hCm hCg)
    rw [lspan_map] at hCD
    have hne : 𝔭 ≠ lspan C := fun h' => hCg h'.symm
    have hle : lspan Pg₁ ≤ (lspan C).map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) :=
      hPg₁ ▸ torsor_locusPt_le_map hI hmax h𝔭 hd hw hπ hπ0 (hcomp C hCm) hne
    exact ⟨C, hCm, hCg, (hD.minimal D hDm _ (torsor_comp_isPrime_pt hI hmax h𝔭 hd hw hπ
      (hcomp C hCm) hne) hle hCD).symm⟩
  -- `𝔭` is a component of `I`
  obtain ⟨C₀, hC₀m, hC₀⟩ := hC.exists_eq_of_mem_minimalPrimes (hPg ▸ h𝔭.min)
  have hsub : 𝔭.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) :: Ds.map lspan ⊆
      Cs.map fun C => (lspan C).map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) := by
    intro P hP
    rcases List.mem_cons.1 hP with rfl | hP
    · exact List.mem_map.2 ⟨C₀, hC₀m, by rw [hC₀]⟩
    · obtain ⟨D, hDm, rfl⟩ := List.mem_map.1 hP
      obtain ⟨C, hCm, -, hDC⟩ := hmap D hDm
      exact List.mem_map.2 ⟨C, hCm, hDC.symm⟩
  have hnd : (𝔭.map (algebraMap A (Torsor hI hmax h𝔭 d hπ)) :: Ds.map lspan).Nodup := by
    refine List.nodup_cons.2 ⟨fun h' => ?_, hD.nodup_map⟩
    obtain ⟨D, hDm, hD𝔭⟩ := List.mem_map.1 h'
    obtain ⟨C, hCm, hCg, hDC⟩ := hmap D hDm
    have hne : 𝔭 ≠ lspan C := fun h'' => hCg h''.symm
    have h2 := torsor_map_sup_eq_top hI hmax h𝔭 hd hw hπ (hcomp C hCm) hne
    rw [← hD𝔭, hDC, sup_idem] at h2
    exact (torsor_comp_isPrime_pt hI hmax h𝔭 hd hw hπ (hcomp C hCm) hne).ne_top h2
  have := hnd.length_le_of_subset hsub
  rw [List.length_cons, List.length_map, List.length_map] at this
  omega

include hd hw hπ0 in
/-- **Lemma 4.3 at points**: `v₁ ≺ v₀`, or `v₁ = v₀` and the number of components drops. At the
point where `v₁` is attained, either `s ∈ 𝔪₁` and `v₁ ≺ v₀` outright, or `𝔪₁` lies over a point of
`A` and `v₁` has the support bound of `I` (`weight_le_dec`). -/
theorem torsor_decrease_pt [Fact (Constructive.HasPres A)] [Constructive.Enum A] [Fact (∃ k, ChartDim A k)] {v₁ : ℕ → ℚ} (he₁ : IsMaxInv (torsorI hI hmax h𝔭 hd hπ) v₁)
    {Pg : List A} (hPg : locusPt I v₀ = lspan Pg) {Pg₁ : List (Torsor hI hmax h𝔭 d hπ)}
    (hPg₁ : locusPt (torsorI hI hmax h𝔭 hd hπ) v₁ = lspan Pg₁) {k k₁ : ℕ} (hk : NumComp Pg k)
    (hk₁ : NumComp Pg₁ k₁) : v₁ ≺ v₀ ∨ (v₁ = v₀ ∧ k₁ < k) := by
  obtain ⟨N, hbd, hb₀⟩ := h𝔭.bd
  obtain ⟨⟨𝔪₁, _, hI₁, hv₁⟩, -⟩ := he₁
  have hle : v₁ ⪯ v₀ := torsor_inv_ge hI hmax h𝔭 hd hw hπ hπ0 𝔪₁ hI₁ hv₁
  rcases torsor_invAt hI hmax h𝔭 hd hw hπ hπ0 𝔪₁ hI₁ hv₁ with ⟨-, hlt⟩ | ⟨-, -, -, hv'⟩
  · exact Or.inl ⟨hle, fun h => (lt_irrefl _) (h ▸ hlt)⟩
  · have : Algebra.FiniteType ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_finiteType hI hmax h𝔭 hd hw hπ
    have : (𝔪₁.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).IsMaximal :=
      comap_isMaximal_of_finiteType 𝔪₁
    rcases weight_le_dec (hbd _ v₁ hv') hb₀ hle with h | rfl
    · exact Or.inl h
    · exact Or.inr ⟨rfl, torsor_count_pt hI hmax h𝔭 hd hw hπ hπ0 hPg hPg₁ hk hk₁⟩

end TorsorPt

end BezoutCounterexample.Principalization
