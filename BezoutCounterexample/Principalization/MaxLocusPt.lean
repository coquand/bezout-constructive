import BezoutCounterexample.Principalization.MaxLocusPtCore
import BezoutCounterexample.Principalization.PosLocus
import BezoutCounterexample.Principalization.LocDataPtProd

/-!
# The maximal locus at explicit points: charts and generators (D3.3a, `docs/d3-design.md` §8.3)

The core (`locusPt`, `LocusComp`, the point forms of the MaxLocus lemmas) is in `MaxLocusPtCore.lean`.
Here:

* `LocData.RFB_map_eq_pt`, `LocData.exists_pow_mul_mem_pt`: spreading between charts at points
  (replaces the Jacobson argument of `LocData.exists_pow_mul_mem`).
* `LocGensPt`, `exists_locusPt_gens_pos`: generators of the locus ideal at points.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing IsLocalization

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-! ### Spreading between charts, at points (replaces the Jacobson argument of
`LocData.exists_pow_mul_mem`) -/

namespace LocData

variable [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal]
  (D : LocData I v₀ 𝔪)

omit [IsNoetherianRing A] in
/-- **Two charts give the same ideals at a common explicit point** (`RFB_map_eq` at points, the
locus decided by `locus_dec_pt`). -/
lemma RFB_map_eq_pt (hI : I ≠ ⊥) {𝔪₁ : Ideal A} [𝔪₁.IsMaximal] (D₁ : LocData I v₀ 𝔪₁)
    (p : Pt A) (hg : D.g ∉ p.ker) (hg₁ : D₁.g ∉ p.ker) (t : ℚ) :
    (D.RFB t).map (Loc.map (D.ctrlN p.ker hg)) = (D₁.RFB t).map (Loc.map (D₁.ctrlN p.ker hg₁)) := by
  rcases D.locus_dec_pt p hg with ⟨hI', hv'⟩ | ⟨i, hi, hu⟩
  · rw [D.RFB_map_of_mem hI hg hI' hv', D₁.RFB_map_of_mem hI hg₁ hI' hv']
  · have hZ : ¬ (I ≤ p.ker ∧ InvAt I p.ker v₀) := fun hZ =>
      (IsLocalRing.notMem_maximalIdeal.2 hu) ((D.iff p.ker hg).1 hZ i hi)
    rw [D.RFB_map_eq_top_of_isUnit hg i hi hu t]
    rcases D₁.locus_dec_pt p hg₁ with hZ₁ | ⟨i₁, hi₁, hu₁⟩
    · exact absurd hZ₁ hZ
    · rw [D₁.RFB_map_eq_top_of_isUnit hg₁ i₁ hi₁ hu₁ t]

omit [IsNoetherianRing A] in
/-- **Spreading a membership** from one chart to another, up to a power of `g`, at explicit points
(replaces `LocData.exists_pow_mul_mem`): contract `RFB₁` to `A` (`exists_contract`), decide
`g g₁ ∈ √((N₁ : b))`; otherwise an explicit point of `V((N₁ : b)) ∩ D(g g₁)` contradicts the
equality of the two charts' ideals there. -/
lemma exists_pow_mul_mem_pt [hpA : Fact (HasPres A)] (hI : I ≠ ⊥) {𝔪₁ : Ideal A} [𝔪₁.IsMaximal]
    (D₁ : LocData I v₀ 𝔪₁) (b : A) (t : ℚ) (hb : algebraMap A D.B b ∈ D.RFB t) :
    ∃ N : ℕ, algebraMap A D₁.B (D.g ^ N * b) ∈ D₁.RFB t := by
  have hp : HasPres A := hpA.out
  obtain ⟨l, hl⟩ := D₁.cB.RF_eq_lspan D₁.ek D₁.inv.nonneg t
  obtain ⟨N₁, hN₁⟩ := HasPres.exists_contract hp D₁.g D₁.B l
  have hRFB : ∀ y : A, algebraMap A D₁.B y ∈ D₁.RFB t ↔ y ∈ lspan N₁ := fun y => by
    rw [LocData.RFB, hl]; exact hN₁ y
  obtain ⟨C, hC⟩ := HasPres.exists_colon hp N₁ [b]
  have hb1 : lspan [b] = Ideal.span {b} := by rw [lspan]; congr 1; ext z; simp
  have hCb : ∀ y, y ∈ lspan C ↔ y * b ∈ lspan N₁ := fun y => by
    rw [hC y]
    constructor
    · exact fun h => h b (hb1 ▸ Ideal.mem_span_singleton_self b)
    · intro hy z hz
      rw [hb1] at hz
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      rw [mul_left_comm]
      exact Ideal.mul_mem_left _ _ hy
  obtain ⟨R, hR⟩ := hp.exists_radical C
  rcases hp.mem_dec R (D.g * D₁.g) with h | h
  · rw [hR] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have h1 := (hRFB _).2 ((hCb _).1 hk)
    have he : (D.g * D₁.g) ^ k * b = D₁.g ^ k * (D.g ^ k * b) := by ring
    rw [he, map_mul, map_pow] at h1
    exact (Ideal.unit_mul_mem_iff_mem _
      ((IsLocalization.Away.algebraMap_isUnit D₁.g).pow k)).1 h1
  · exfalso
    have hk : ∀ k : ℕ, (D.g * D₁.g) ^ k ∉ lspan C := fun k hk => h (hR ▸ ⟨k, hk⟩)
    obtain ⟨p, hCp, hgg⟩ := HasPres.exists_pt_away hp C (D.g * D₁.g) hk
    have hg : D.g ∉ p.ker := fun h => hgg (Ideal.mul_mem_right _ _ h)
    have hg₁ : D₁.g ∉ p.ker := fun h => hgg (Ideal.mul_mem_left _ _ h)
    have h1 : algebraMap A (Localization.AtPrime p.ker) b ∈
        (D₁.RFB t).map (Loc.map (D₁.ctrlN p.ker hg₁)) := by
      rw [← D.RFB_map_eq_pt hI D₁ p hg hg₁, ← D.map_algebraMap_B hg]
      exact Ideal.mem_map_of_mem _ hb
    obtain ⟨y, hy, hyb⟩ := D₁.exists_of_mem_map hg₁ _ h1
    exact hy (hCp ((hCb y).2 ((hRFB _).1 hyb)))

end LocData

/-! ### Generators of the locus ideal at points (point form of `exists_locusIdeal_gens_pos`) -/

/-- **Local generators of the maximal locus at points** on `D(g)`. -/
def LocGensPt (I : Ideal A) (v₀ : ℕ → ℚ) (g : A) (a : List A) : Prop :=
  (∀ b ∈ a, g * b ∈ locusPt I v₀) ∧
    ∀ p : Pt A, g ∉ p.ker → (∀ b ∈ a, b ∈ p.ker) → I ≤ p.ker ∧ InvAt I p.ker v₀

omit [IsDomain A] [Algebra.Smooth ℚ A] in
theorem LocData.exists_locGensPt [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A}
    [𝔪.IsMaximal] (D : LocData I v₀ 𝔪) : ∃ a : List A, LocGensPt I v₀ D.g a := by
  obtain ⟨a, -, h1, h2⟩ := D.exists_heads
  exact ⟨a, h1, h2⟩

omit [IsDomain A] [Algebra.Smooth ℚ A] in
/-- **A neighbourhood missing the locus**, at points (replaces `locGens_of_ne`). -/
theorem locGensPt_of_ne {I : Ideal A} {v₀ : ℕ → ℚ}
    (hmax : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal], I ≤ 𝔪 → ∀ v, InvAt I 𝔪 v → toLex v₀ ≤ toLex v)
    {𝔪 : Ideal A} [𝔪.IsMaximal] (hI𝔪 : I ≤ 𝔪) {v : ℕ → ℚ} (hv : InvAt I 𝔪 v) (hne : v ≠ v₀)
    {g : A} (hbound : ∀ (𝔪' : Ideal A) [𝔪'.IsMaximal], g ∉ 𝔪' → ∀ v', InvAt I 𝔪' v' →
      toLex v ≤ toLex v') : LocGensPt I v₀ g [1] := by
  refine ⟨fun b hb => ?_, fun p _ hall => ?_⟩
  · rw [List.mem_singleton] at hb
    subst hb
    rw [mul_one]
    intro q _ hvq
    rcases q.mem_ker_dec g with h | h
    · exact h
    · exact absurd (toLex.injective (le_antisymm (hbound q.ker h v₀ hvq) (hmax 𝔪 hI𝔪 v hv))) hne
  · exact absurd ((Ideal.eq_top_iff_one _).2 (hall 1 List.mem_cons_self))
      (Ideal.IsMaximal.ne_top inferInstance)

section Gens

variable [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {N : ℕ} (hbd : ∀ (𝔪 : Ideal A) [𝔪.IsMaximal] (v : ℕ → ℚ), InvAt I 𝔪 v → ∀ i, N ≤ i → v i = 0)
  (hb₀ : ∀ i, N ≤ i → v₀ i = 0)
include hI hmax hbd hb₀

/-- **One step of the cover**, at points. -/
theorem exists_locGensPt_step (hp : HasPres A) (gens : List A) (hgens : I = lspan gens)
    (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n))
    (l : List A) (h1 : (1 : A) ∉ I ⊔ lspan l) :
    ∃ g, (∃ a, LocGensPt I v₀ g a) ∧ g ∉ I ⊔ lspan l := by
  obtain ⟨p, hp'⟩ := HasPres.exists_pt hp (gens ++ l) fun h => h1 (lspan_append_le hgens h)
  have hle : I ⊔ lspan l ≤ p.ker := by
    rw [hgens, ← lspan_append_eq]; exact hp'
  have hI𝔪 : I ≤ p.ker := le_sup_left.trans hle
  -- D3.8 (E2): invariant, semicontinuity and local data at the point (`_ptL`, `LocDataPt`)
  obtain ⟨v, hv, g, hg, hbound⟩ := exists_invAt_semicont_ptL hI gens hgens hchart p hI𝔪
  rcases eq_or_ne_bounded (hbd _ _ hv) hb₀ with heq | hne
  · obtain ⟨f₀, hf₀, n₀, ⟨c₀⟩⟩ := hchart p
    obtain ⟨D⟩ := LocDataPt.nonempty hI gens hgens p hI𝔪 (heq ▸ hv) hf₀ c₀
    obtain ⟨a, -, ha1, ha2⟩ := D.exists_heads
    exact ⟨D.g, ⟨a, ha1, ha2⟩, fun h => D.hg (hle h)⟩
  · -- `locGensPt_of_ne`, with the bound at explicit points
    refine ⟨g, ⟨[1], fun b hb => ?_, fun p' _ hall => ?_⟩, fun h => hg (hle h)⟩
    · rw [List.mem_singleton] at hb
      subst hb
      rw [mul_one]
      intro q _ hvq
      rcases q.mem_ker_dec g with h | h
      · exact h
      · exact absurd (toLex.injective (le_antisymm (hbound q h v₀ hvq) (hmax _ hI𝔪 v hv))) hne
    · exact absurd ((Ideal.eq_top_iff_one _).2 (hall 1 List.mem_cons_self))
        (Ideal.IsMaximal.ne_top inferInstance)

/-- **Generators of the locus ideal at points**, from a presentation of `A`, generators of `I`
and the support bound (point form of `exists_locusIdeal_gens_pos`). -/
theorem exists_locusPt_gens_pos (hp : HasPres A) (gens : List A) (hgens : I = lspan gens)
    (hchart : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ ∃ n : ℕ, Nonempty (Chart (Localization.Away f) n)) :
    ∃ Pg : List A, locusPt I v₀ = lspan Pg := by
  have hdec : ∀ l : List A, (1 : A) ∈ I ⊔ lspan l ∨ (1 : A) ∉ I ⊔ lspan l := fun l => by
    rw [hgens, ← lspan_append_eq]; exact hp.mem_dec _ 1
  obtain ⟨l, hl, h1⟩ := exists_cover I (indNoeth_quotient_of_hasPres hp I)
    (fun g => ∃ a, LocGensPt I v₀ g a) hdec
    fun l _ hl1 => exists_locGensPt_step hI hmax hbd hb₀ hp gens hgens hchart l hl1
  obtain ⟨ps, hps, hP⟩ := exists_pairs
    (fun g (aR : List A × List A) => LocGensPt I v₀ g aR.1 ∧
      lspan aR.2 = (lspan aR.1).radical) l fun g hg => by
    obtain ⟨a, ha⟩ := hl g hg
    obtain ⟨R, hR⟩ := hp.exists_radical a
    exact ⟨(a, R), ha, hR⟩
  set gf : Fin ps.length → A := fun k => (ps.get k).1
  obtain ⟨Pg, hPg⟩ := hp.exists_gens_of_charts gf
    (fun k => (ps.get k).2.2.map (algebraMap A (Localization.Away (gf k))))
  refine ⟨Pg, le_antisymm (fun x hx => (hPg x).2 fun k => ?_) fun x hx => ?_⟩
  · -- `⊆`: decide `g x ∈ √(a)`; otherwise an explicit point of `V(a) ∩ D(g x)`
    have hk := hP _ (List.get_mem ps k)
    set g := gf k
    set a := (ps.get k).2.1
    rw [lspan_map, hk.2]
    refine algebraMap_mem_of_mul_mem g _ ?_
    rcases hp.mem_dec (ps.get k).2.2 (g * x) with h | h
    · rwa [hk.2] at h
    · exfalso
      have hpow : ∀ n : ℕ, (g * x) ^ n ∉ lspan a := fun n hn => h (hk.2 ▸ ⟨n, hn⟩)
      obtain ⟨p, hap, hgx⟩ := HasPres.exists_pt_away hp a (g * x) hpow
      have hg : g ∉ p.ker := fun h' => hgx (Ideal.mul_mem_right _ _ h')
      obtain ⟨hI', hv'⟩ := hk.1.2 p hg fun b hb => hap (Ideal.subset_span hb)
      exact hgx (Ideal.mul_mem_left _ _ (hx p hI' hv'))
  · -- `⊇`: `g x ∈ p.ker` for each element `g` of the cover, at each point of the locus
    intro p hIp hvp
    have hgx : ∀ g ∈ l, x * g ∈ p.ker := by
      intro g hg
      rw [← hps] at hg
      obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hg
      obtain ⟨k, rfl⟩ := List.get_of_mem hq'
      have hk := hP _ (List.get_mem ps k)
      have hx' := (hPg x).1 hx k
      rw [lspan_map, hk.2] at hx'
      obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_away (gf k) _ hx'
      obtain ⟨M, hM⟩ := hn
      have hga := lspan_le_comap_mul (gf k) _ p.ker
        (fun b hb => hk.1.1 b hb p hIp hvp) _ hM
      rw [mul_comm x]
      have hpr : p.ker.IsPrime := inferInstance
      rcases hpr.mem_or_mem hga with h | h
      · exact Ideal.mul_mem_right _ _ h
      · rcases hpr.mem_or_mem (hpr.mem_of_pow_mem _ h) with h | h
        · exact Ideal.mul_mem_right _ _ (hpr.mem_of_pow_mem _ h)
        · exact Ideal.mul_mem_left _ _ h
    obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 h1
    have : x = x * i + x * y := by rw [← mul_add, hiy, mul_one]
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hIp hi)) (lspan_le_comap_mul x l p.ker hgx y hy)

end Gens

end BezoutCounterexample.Principalization
