import BezoutCounterexample.Principalization.TorsorDerPt
import BezoutCounterexample.Principalization.TorsorInvPt

/-!
# Vertical derivations at explicit points (D3.8 E3, leaf)

`VertOK I m` (TorsorDer) asks for derivations stabilizing `I` with a Jacobian unit at every maximal
ideal above `I`; on the torsor this needs a coordinate `torsorY l` off an arbitrary maximal ideal
(`exists_torsorY_not_mem`, classical), and the stabilization of the component filtration
(`deriv_mem_compFPt`, classical engine). At explicit points:

* `VertOKPt I m`: the same condition at the explicit points above `I` (the form of
  `StarC.derivations` since D3.8);
* `deriv_mem_compFPtP`: `deriv_mem_compFPt` through `deriv_mem_compFPt_ptL`, with the generators
  and charts carried by `LocusComp` (same signature);
* `deriv_mem_divIP`, `div_vertOKPt`: the divisorial step;
* `torsor_vertOKPt`: the torsor step (`exists_torsorY_not_mem_pt` at the point).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial Jou

section VertPt

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- **`VertOK` at explicit points.** -/
def VertOKPt (I : Ideal A) (m : ℕ) : Prop :=
  ∀ q : Pt A, I ≤ q.ker → ∃ (δ : Fin m → Derivation ℚ A A) (y : Fin m → A),
    (∀ j, ∀ f ∈ I, δ j f ∈ I) ∧ (Matrix.of fun j l => δ j (y l)).det ∉ q.ker

/-- `deriv_mem_compFPt` through `deriv_mem_compFPt_ptL`, with the generators and charts carried by
`h𝔭` (signature of `deriv_mem_compFPt`). -/
theorem deriv_mem_compFPtP [IsNoetherianRing A] {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
    (hmax : IsMaxInvPt I v₀)
    {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) (δ : Derivation ℚ A A) (hδ : ∀ f ∈ I, δ f ∈ I)
    (t : ℚ) {f : A} (hf : f ∈ compFPt I 𝔭 t) : δ f ∈ compFPt I 𝔭 t := by
  obtain ⟨l, hl⟩ := h𝔭.gensI
  exact deriv_mem_compFPt_ptL hI l hl h𝔭.hchart hmax h𝔭 δ hδ
    t hf

end VertPt

section DivDerPt

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)
  {π : A} (h𝔭π : 𝔭 = Ideal.span {π}) {a : ℕ} (ha0 : 0 < a)

include hI hmax h𝔭 hd hw h𝔭π ha0 in
/-- Stabilizing derivations pass to `I : π^a` (`deriv_mem_divI` at points). -/
theorem deriv_mem_divIP [Fact (Constructive.HasPres A)] (δ : Derivation ℚ A A) (hδ : ∀ f ∈ I, δ f ∈ I) {f : A}
    (hf : f ∈ divI I π a) : δ f ∈ divI I π a := by
  have hπF : π ∈ compFPt I 𝔭 (1 / d) := by
    rw [h𝔭.compFPt_one_divP hI hmax hd hw, h𝔭π]; exact Ideal.mem_span_singleton_self π
  have hδπ : δ π ∈ Ideal.span {π} := by
    rw [← h𝔭π, ← h𝔭.compFPt_one_divP hI hmax hd hw]
    exact deriv_mem_compFPtP hI hmax h𝔭 δ hδ _ hπF
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hδπ
  rw [mem_divI] at hf ⊢
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have h2 : δ (π ^ (b + 1) * f) = π ^ (b + 1) * δ f + ((b + 1 : ℕ) * c) * (π ^ (b + 1) * f) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, ← hc, smul_eq_mul, smul_eq_mul, nsmul_eq_mul,
      smul_eq_mul, Nat.add_sub_cancel]
    push_cast; ring
  have : π ^ (b + 1) * δ f = δ (π ^ (b + 1) * f) - ((b + 1 : ℕ) * c) * (π ^ (b + 1) * f) := by
    rw [h2]; ring
  rw [this]
  exact I.sub_mem (hδ _ hf) (I.mul_mem_left _ hf)

include hI hmax h𝔭 hd hw h𝔭π ha0 in
/-- `div_vertOK` at explicit points. -/
theorem div_vertOKPt [Fact (Constructive.HasPres A)] {m : ℕ} (hV : VertOKPt I m) :
    VertOKPt (divI I π a) m := by
  intro q hle
  obtain ⟨δ, y, hδ, hdet⟩ := hV q ((le_divI I π a).trans hle)
  exact ⟨δ, y, fun j f hf => deriv_mem_divIP hI hmax h𝔭 hd hw h𝔭π ha0 (δ j) (hδ j) hf, hdet⟩

end DivDerPt

section TorsorVertPt

open IsLocalRing IsLocalization LaurentPolynomial Jou

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {d : ℕ} (hd : 0 < d)
  (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i) {π : A} (hπ : π ∈ (compFil hI hmax h𝔭 d).F 1)
  (hπ0 : π ≠ 0)

include hd hw hπ0 in
set_option maxHeartbeats 4000000 in
omit hπ0 in
/-- **Vertical derivations on the torsor, at explicit points** (`torsor_vertOK` with
`deriv_mem_compFPtP` and `exists_torsorY_not_mem_pt`). -/
theorem torsor_vertOKPt [Constructive.Enum A] [Fact (Constructive.HasPres A)] {m : ℕ}
    (hV : VertOKPt I m) :
    VertOKPt (torsorI hI hmax h𝔭 hd hπ) (m + (nGen hI hmax h𝔭 d + 1)) := by
  classical
  intro q hIQ
  set Q := q.ker
  have hQ : Q.IsMaximal := inferInstance
  have : Algebra.FiniteType ℚ (Torsor hI hmax h𝔭 d hπ) := torsor_finiteType hI hmax h𝔭 hd hw hπ
  have hI𝔪 := le_comap_of_torsorI hI hmax h𝔭 hd hπ Q hIQ
  have : (Q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ))).IsMaximal :=
    comap_isMaximal_of_finiteType Q
  have hkA := Pt.ker_comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)) q
  obtain ⟨δ, yA, hδ, hdet⟩ := hV (q.comap (algebraMap A (Torsor hI hmax h𝔭 d hπ)))
    (by rw [hkA]; exact hI𝔪)
  rw [hkA] at hdet
  have hδF : ∀ j, ∀ i, ∀ f ∈ (compFil hI hmax h𝔭 d).F i, δ j f ∈ (compFil hI hmax h𝔭 d).F i :=
    fun j i f hf => by
      rw [compFil_F] at hf ⊢
      exact deriv_mem_compFPtP hI hmax h𝔭 (δ j) (hδ j) _ hf
  obtain ⟨l, hl⟩ := exists_torsorY_not_mem_pt hI hmax h𝔭 hπ q
  set y := torsorY hI hmax h𝔭 d hπ
  set DR : Fin m → Derivation ℚ (ReesAlg (compFil hI hmax h𝔭 d)) (ReesAlg (compFil hI hmax h𝔭 d)) :=
    fun j => reesLift _ (δ j) (hδF j)
  set E := reesEuler (compFil hI hmax h𝔭 d)
  have hE := torsorY_euler hI hmax h𝔭 hπ
  set e := (finSumFinEquiv (m := m) (n := nGen hI hmax h𝔭 d + 1)).symm
  refine ⟨famD y DR E _ hE l ∘ e, famY y l yA ∘ e, ?_, ?_⟩
  · intro i x hx
    simp only [Function.comp_apply]
    rcases e i with j | a
    · exact deriv_mem_map (algebraMap _ _) _ (DR j) (jLift_algebraMap y (DR j))
        (fun f hf => reesLift_weakT _ (δ j) (hδF j) (hδ j) _ _ hf) hx
    · cases a using Fin.cases with
      | zero =>
        exact deriv_mem_map (algebraMap _ _) _ E (jEuler_algebraMap y E _ hE)
          (fun f hf => reesEuler_weakT _ _ _ hf) hx
      | succ b =>
        exact deriv_mem_map (algebraMap _ _) _ 0 (fun f => by
            show jTheta y l b _ = _
            rw [jTheta_algebraMap, Derivation.zero_apply, map_zero])
          (fun f _ => by rw [Derivation.zero_apply]; exact zero_mem _) hx
  · have hsub : (Matrix.of fun j l' => (famD y DR E _ hE l ∘ e) j ((famY y l yA ∘ e) l')) =
        (Matrix.of fun i i' => famD y DR E _ hE l i (famY y l yA i')).submatrix e e := rfl
    rw [hsub, Matrix.det_submatrix_equiv_self,
      det_fam y DR E _ hE l yA δ (fun j a => reesLift_algebraMap _ (δ j) (hδF j) a)
        (fun a => reesEuler_algebraMap _ a)]
    intro hmem
    rcases hQ.isPrime.mem_or_mem hmem with h | h
    · exact hdet h
    rcases hQ.isPrime.mem_or_mem h with h | h
    · rw [map_zsmul, zsmul_eq_mul] at h
      rcases hQ.isPrime.mem_or_mem h with h | h
      · have hu : IsUnit ((genDeg hI hmax h𝔭 d l : ℤ) : Torsor hI hmax h𝔭 d hπ) := by
          have hne : ((genDeg hI hmax h𝔭 d l : ℤ) : ℚ) ≠ 0 := by
            have := genDeg_pos hI hmax h𝔭 d l
            exact_mod_cast (by omega : genDeg hI hmax h𝔭 d l ≠ 0)
          have := (isUnit_iff_ne_zero.2 hne).map (algebraMap ℚ (Torsor hI hmax h𝔭 d hπ))
          rwa [map_intCast] at this
        exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
      · exact hl h
    · exact hl (by
        have := hQ.isPrime.mem_of_pow_mem _ h
        rwa [neg_mem_iff] at this)

end TorsorVertPt

end BezoutCounterexample.Principalization
