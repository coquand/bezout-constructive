import BezoutCounterexample.Principalization.LocDataPt
import BezoutCounterexample.Principalization.MaxLocusPtCore

/-!
# The API of `LocDataPt` (D3.4 (e), leaf)

The lemmas of `LocData` (MaxLocus, MaxLocusPtCore) that use `iff`/`rf` only at explicit points,
restated for `LocDataPt` (same proofs, `D.iff p` for `D.iff p.ker`): the prime `D.p`,
`p_le`, `map_p`, `exists_num`, `transport_x_mk'`, `num_mem_p`, `mem_of_p_le`,
`g_mul_num_mem_pt`, `exists_heads`, `locusPt_le_p`, `P_le_map_pt`, `p_le_of_le_pt`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization Constructive

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

namespace LocDataPt

variable {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] (D : LocDataPt I v₀ 𝔪)

instance : D.P.IsPrime := Chart.IsCentred.span_x_isPrime _ D.cent D.k

instance : D.p.IsPrime := Ideal.comap_isPrime _ _

lemma P_le_max : D.P ≤ maximalIdeal (Localization.AtPrime 𝔪) := by
  rw [P, Ideal.span_le]
  rintro _ ⟨i, -, rfl⟩
  exact D.cent.x_mem i

lemma p_le : D.p ≤ 𝔪 := by
  intro a ha
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a]
  exact D.P_le_max ha

lemma map_p : D.p.map (algebraMap A (Localization.AtPrime 𝔪)) = D.P :=
  IsLocalization.map_under (M := 𝔪.primeCompl) (S := Localization.AtPrime 𝔪) D.P

/-- Numerators of the chart functions. -/
lemma exists_num (i : Fin D.n) : ∃ (a : A) (m : D.M),
    D.ck.x i = IsLocalization.mk' (Localization D.M) a m := by
  obtain ⟨⟨a, m⟩, h⟩ := IsLocalization.mk'_surjective D.M (D.ck.x i)
  exact ⟨a, m, h.symm⟩

lemma transport_x_mk' {N : Submonoid A} (h : D.M ≤ N) (i : Fin D.n) (a : A) (m : D.M)
    (hx : D.ck.x i = IsLocalization.mk' (Localization D.M) a m) :
    (Loc.transport h D.ck).x i = IsLocalization.mk' (Localization N) a ⟨m, h m.2⟩ := by
  rw [Loc.transport_x, hx, Loc.map_mk']

/-- The numerators of the first `k` chart functions lie in `𝔭`. -/
lemma num_mem_p (i : Fin D.n) (hi : (i : ℕ) < D.k) (a : A) (m : D.M)
    (hx : D.ck.x i = IsLocalization.mk' (Localization D.M) a m) : a ∈ D.p := by
  show algebraMap A _ a ∈ D.P
  have h1 : (Loc.transport (D.ctrl 𝔪 D.hg) D.ck).x i ∈ D.P := Ideal.subset_span ⟨i, hi, rfl⟩
  rw [D.transport_x_mk' _ i a m hx] at h1
  have h2 := D.P.mul_mem_right (algebraMap A (Localization.AtPrime 𝔪) m) h1
  rwa [IsLocalization.mk'_spec] at h2

/-- Conversely, the explicit points of `V(𝔭) ∩ D(g)` are in the maximal locus. -/
lemma mem_of_p_le (p : Pt A) (hg' : D.g ∉ p.ker) (hp : D.p ≤ p.ker) :
    I ≤ p.ker ∧ InvAt I p.ker v₀ := by
  rw [D.iff p hg']
  intro i hi
  obtain ⟨a, m, hx⟩ := D.exists_num i
  rw [D.transport_x_mk' _ i a m hx,
    IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime p.ker) p.ker]
  exact hp (D.num_mem_p i hi a m hx)

/-- `g aᵢ` lies in the locus ideal at points (decided at each point). -/
lemma g_mul_num_mem_pt (i : Fin D.n) (hi : (i : ℕ) < D.k) (a : A) (m : D.M)
    (hx : D.ck.x i = IsLocalization.mk' (Localization D.M) a m) :
    D.g * a ∈ locusPt I v₀ := by
  intro p hI hv
  rcases p.mem_ker_dec D.g with hg | hg
  · exact Ideal.mul_mem_right _ _ hg
  · refine Ideal.mul_mem_left _ _ ?_
    have := (D.iff p hg).1 ⟨hI, hv⟩ i hi
    rw [D.transport_x_mk' _ i a m hx,
      IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime p.ker) p.ker] at this
    exact this

/-- **The head numerators** of local data: in `D.p`, with `g a ⊆ locusPt`, and
`V(a) ∩ D(g)` in the maximal locus at points. -/
theorem exists_heads : ∃ a : List A, (∀ b ∈ a, b ∈ D.p) ∧ (∀ b ∈ a, D.g * b ∈ locusPt I v₀) ∧
    ∀ p : Pt A, D.g ∉ p.ker → (∀ b ∈ a, b ∈ p.ker) → I ≤ p.ker ∧ InvAt I p.ker v₀ := by
  obtain ⟨f, hf⟩ := exists_fun_fin
    (fun i (am : A × D.M) => D.ck.x i = IsLocalization.mk' (Localization D.M) am.1 am.2)
    (fun i => by obtain ⟨a, m, h⟩ := D.exists_num i; exact ⟨(a, m), h⟩)
  refine ⟨((List.finRange D.n).filter (fun i : Fin D.n => decide ((i : ℕ) < D.k))).map
    (fun i => (f i).1), ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact D.num_mem_p i (by simpa using (List.mem_filter.1 hi).2) _ _ (hf i)
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact D.g_mul_num_mem_pt i (by simpa using (List.mem_filter.1 hi).2) _ _ (hf i)
  · intro p hg hall
    rw [D.iff p hg]
    intro i hi
    rw [D.transport_x_mk' _ i _ _ (hf i),
      IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime p.ker) p.ker]
    exact hall _ (List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_finRange i, decide_eq_true hi⟩,
      rfl⟩)

/-- **The locus ideal at points lies in `D.p`** (replaces `locusIdeal_le_p`, no Jacobson): decide
`(g f)ᵏ ∈ (a)` for the head numerators `a`; otherwise a point of `V(a) ∩ D(g f)` lies in the locus
and `f` does not vanish there. -/
theorem locusPt_le_p [hpA : Fact (HasPres A)] : locusPt I v₀ ≤ D.p := by
  intro f hf
  have hp : HasPres A := hpA.out
  obtain ⟨a, hap, -, hloc⟩ := D.exists_heads
  obtain ⟨R, hR⟩ := hp.exists_radical a
  rcases hp.mem_dec R (D.g * f) with h | h
  · rw [hR] at h
    obtain ⟨k, hk⟩ := h
    have hle : lspan a ≤ D.p := by
      rw [lspan, Ideal.span_le]; exact fun b hb => hap b hb
    rcases (inferInstance : D.p.IsPrime).mem_or_mem
      ((inferInstance : D.p.IsPrime).mem_of_pow_mem k (hle hk)) with h | h
    · exact absurd (D.p_le h) D.hg
    · exact h
  · exfalso
    have hk : ∀ k : ℕ, (D.g * f) ^ k ∉ lspan a := fun k hk => h (hR ▸ ⟨k, hk⟩)
    obtain ⟨p, hap', hgf⟩ := HasPres.exists_pt_away hp a (D.g * f) hk
    have hg : D.g ∉ p.ker := fun h => hgf (Ideal.mul_mem_right _ _ h)
    obtain ⟨hI, hv⟩ := hloc p hg fun b hb => hap' (Ideal.subset_span hb)
    exact hgf (Ideal.mul_mem_left _ _ (hf p hI hv))

/-- The chart functions lie in the extension of any ideal containing `locusPt`. -/
lemma P_le_map_pt {𝔮 : Ideal A} (h𝔮 : locusPt I v₀ ≤ 𝔮) :
    D.P ≤ 𝔮.map (algebraMap A (Localization.AtPrime 𝔪)) := by
  rw [P, Ideal.span_le]
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨a, m, hx⟩ := D.exists_num i
  rw [SetLike.mem_coe, D.transport_x_mk' _ i a m hx,
    IsLocalization.mk'_mem_map_algebraMap_iff 𝔪.primeCompl]
  exact ⟨D.g, D.hg, h𝔮 (D.g_mul_num_mem_pt i hi a m hx)⟩

/-- `D.p` lies below every prime between `locusPt` and `𝔪`. -/
lemma p_le_of_le_pt {𝔮 : Ideal A} [𝔮.IsPrime] (h1 : locusPt I v₀ ≤ 𝔮) (h2 : 𝔮 ≤ 𝔪) :
    D.p ≤ 𝔮 := by
  intro a ha
  have h := D.P_le_map_pt h1 ha
  rw [← under_map_atPrime h2]
  exact h

end LocDataPt

end BezoutCounterexample.Principalization
