import BezoutCounterexample.Principalization.Drop
import BezoutCounterexample.Principalization.DropPtBase
import BezoutCounterexample.Principalization.VertexGPos
import BezoutCounterexample.Principalization.SpanSPtL

/-!
# The drop of the invariant at an explicit point (leaf; `docs/plan-drop-pt.md`)

`drop` (Drop) at a maximal ideal `P` of the Rees algebra `R` uses Zariski
(`comap_isMaximal_of_finiteType`), `VertexData.nonempty`, `local_inv` at the vertex and
`exists_invAt` at a rescaled point (classical), `exists_reesScale_not_mem` (roots of a polynomial
avoided by `Infinite.exists_notMem_finset`), and `rees_smooth`. At an explicit point `Q : Pt R`:

* the point of `A` below `Q` is `Q.pullback (algebraMap A R)` (explicit, no Zariski);
* vertex data from `VertexData.nonempty_ptL`, the weak transform at the vertex from
  `VertexData.vertexG_data_pos`;
* the vertex is the explicit point `q.vertexPt` (`Pt.vertexPt_ker`), and the local structure of
  the weak transform there is `local_structure_pt` on `R` (I4 binders: the instances at the points
  of `R` are hypotheses, see `docs/plan-drop-pt.md`), with a chart of `R` near the vertex
  (`hchartR`) and the generators `weakTGens` of the weak transform;
* the rescaling by `exists_reesScale_not_mem_pt`, the rescaled point `Q.pullback σ`;
* the invariant at the rescaled point is the given one transported by `σ⁻¹`
  (`InvAt.of_ringEquiv`), so `exists_invAt` is not used.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial Constructive

section WeakTGens

variable {B : Type} [CommRing B] (Φ : WFil B)

/-- The generators `f Tᵈ` (`f ∈ l`) of the weak transform. -/
def weakTGens {d : ℕ} (l : List B) (hl : ∀ f ∈ l, f ∈ Φ.F d) : List (ReesAlg Φ) :=
  l.attach.map fun g => ⟨LaurentPolynomial.C g.1 * T d, C_mul_T_mem_ReesAlg (hl g.1 g.2)⟩

/-- **The weak transform is explicitly generated.** -/
theorem weakT_eq_lspan {d : ℕ} (I : Ideal B) (hId : I ≤ Φ.F d) (l : List B) (hlI : I = lspan l) :
    weakT Φ I d hId = lspan (weakTGens Φ l fun f hf => hId (hlI ▸ Ideal.subset_span hf)) := by
  have h := weakIdeal_eq_span (Φ := Φ) I hId l hlI
  rw [show weakT Φ I d hId = weakIdeal I hId from rfl, h]
  show Ideal.span _ = Ideal.span _
  congr 1
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact List.mem_map.2 ⟨⟨f, hf⟩, List.mem_attach _ _, rfl⟩
  · intro hx
    obtain ⟨⟨f, hf⟩, -, rfl⟩ := List.mem_map.1 hx
    exact ⟨f, hf, rfl⟩

end WeakTGens

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [Algebra.FiniteType ℚ A] [IsNoetherianRing A]

variable {I : Ideal A} (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l) {v₀ : ℕ → ℚ}
  (hmax : IsMaxInvPt I v₀)
  {𝔭 : Ideal A} (h𝔭 : LocusComp I v₀ 𝔭) {dim : ℕ}
  (hchartn : ∀ p : Pt A, ∃ f : A, f ∉ p.ker ∧ Nonempty (Chart (Localization.Away f) dim))
  {d : ℕ} (hd : 0 < d) (hw : ∀ i, ∃ w : ℕ, (w : ℚ) = d * v₀ i)

include hI l hl hmax h𝔭 hchartn hd hw

omit [Algebra.FiniteType ℚ A] in
set_option maxHeartbeats 1600000 in
/-- **The drop of the invariant at an explicit point of the exceptional divisor** (twin of
`drop`): the instances at the points of `R` (I4) and the charts of `R` near its points are
hypotheses. -/
theorem drop_pt [Fact (Constructive.HasPres A)]
    [hR4a : ∀ q : Pt (ReesAlg (compFil hI hmax h𝔭 d)),
      Fact (Constructive.PolyIndNoeth (Localization.AtPrime q.ker))]
    [hR4b : ∀ q : Pt (ReesAlg (compFil hI hmax h𝔭 d)),
      Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker)]
    [hR4c : ∀ q : Pt (ReesAlg (compFil hI hmax h𝔭 d)),
      Algebra.FormallySmooth ℚ (IsLocalRing.ResidueField (Localization.AtPrime q.ker))]
    (hchartR : ∀ p : Pt (ReesAlg (compFil hI hmax h𝔭 d)), ∃ f, f ∉ p.ker ∧ ∃ n : ℕ,
      Nonempty (Chart (Localization.Away f) n))
    (Q : Pt (ReesAlg (compFil hI hmax h𝔭 d)))
    (_hIwQ : weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil_gen hI hmax h𝔭 hd) ≤ Q.ker)
    (hsQ : reesS (compFil hI hmax h𝔭 d) (fun _j hj => compFil_F_nonpos_gen hI hmax h𝔭 hj) ∈ Q.ker)
    {j : ℤ} (hj : 1 ≤ j) {f : A} (hf : f ∈ (compFil hI hmax h𝔭 d).F j)
    (hyQ : (⟨LaurentPolynomial.C f * T j, C_mul_T_mem_ReesAlg hf⟩ :
      ReesAlg (compFil hI hmax h𝔭 d)) ∉ Q.ker)
    {v : ℕ → ℚ}
    (hv : InvAt (weakT (compFil hI hmax h𝔭 d) I d (I_le_compFil_gen hI hmax h𝔭 hd)) Q.ker v) :
    toLex v₀ < toLex v := by
  let Φ := compFil hI hmax h𝔭 d
  let R := ReesAlg Φ
  have hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤ := fun _j hj => compFil_F_nonpos_gen hI hmax h𝔭 hj
  have hId := I_le_compFil_gen hI hmax h𝔭 hd
  let Iw := weakT Φ I d hId
  have hchart := LocusComp.hchart_of_dim hI l hl hmax h𝔭 hchartn
  -- the point of `A` below `Q`
  set q : Pt A := Q.pullback (algebraMap A R)
  have hqker : q.ker = Q.ker.comap (algebraMap A R) := Pt.pullback_ker Q _
  have h𝔭q : 𝔭 ≤ q.ker := by
    intro g hg
    have hg1 : g ∈ Φ.F 1 := by
      have := h𝔭.pow_le_compFPt_ptL hI l hl hchart hmax hd hw 1 (by rw [pow_one]; exact hg)
      rw [compFil_F]; push_cast at this ⊢; exact this
    rw [hqker, Ideal.mem_comap]
    have : algebraMap A R g = reesS Φ hneg * ⟨LaurentPolynomial.C g * T 1, C_mul_T_mem_ReesAlg hg1⟩ := by
      apply Subtype.ext
      show algebraMap A A[T;T⁻¹] g = T (-1) * (LaurentPolynomial.C g * T 1)
      rw [mul_left_comm, ← T_add, neg_add_cancel, T_zero, mul_one, LaurentPolynomial.C_eq_algebraMap]
    rw [this]; exact Q.ker.mul_mem_right _ hsQ
  -- vertex data at `q` and the weak transform at the vertex
  obtain ⟨D⟩ := VertexData.nonempty_ptL hI l hl hchartn hmax h𝔭 hw q h𝔭q
  set hpos := D.hpos hd
  set q₀ : Pt R := q.vertexPt Φ hpos
  have hq₀ : q₀.ker = vertexG Φ q.ker hpos := Pt.vertexPt_ker Φ q hpos
  have key : ∀ (P : Ideal R) [P.IsMaximal], P = vertexG Φ q.ker hpos →
      ∃ J₀ : MC (Localization.AtPrime P) (D.n + 1),
        J₀.Adm (Iloc Iw P) ∧ J₀.e = pad (D.n + 1) D.J.e ∧ IsInv (Iloc Iw P) (D.n + 1) J₀.e ∧
        ∀ (j : ℤ), 1 ≤ j → ∀ (f : A) (hf : f ∈ Φ.F j),
          algebraMap R (Localization.AtPrime P)
            ⟨LaurentPolynomial.C f * T j, C_mul_T_mem_ReesAlg hf⟩ ∈ J₀.RF (1 / d) := by
    rintro P _ rfl
    exact D.vertexG_data_pos hd (Pt.dec_local q) l hl
  obtain ⟨J₀, hJ₀adm, hJ₀e, hJ₀inv, hJ₀homog⟩ := key q₀.ker hq₀
  -- the local structure of the weak transform at the vertex point
  have hIw0 : Iw ≠ ⊥ := weakT_ne_bot Φ hI d hId
  have hIwq₀ : Iw ≤ q₀.ker := by
    rw [hq₀]
    apply weakT_le
    intro g hg
    rw [mem_vertexG, coeff_C_mul_T, ite_eq_right (by omega)]
    exact zero_mem _
  have hlw := weakT_eq_lspan Φ I hId l hl
  obtain ⟨f₀, hf₀, n₀, ⟨c₀⟩⟩ := hchartR q₀
  obtain ⟨M', g, hg, hctrl, k', ck, ek, -, -, hnn', hanti', hadm', hM', hcent', hbound⟩ :=
    local_structure_pt Iw hIw0 _ hlw q₀ hIwq₀ hf₀ c₀
  -- the invariant there is `pad e`
  have hadmq₀ : Iloc Iw q₀.ker ≤ (Loc.transport hM' ck).RF ek 1 := by
    rw [← Loc.map_RF]
    have h1 := Ideal.map_mono (f := Loc.map hM') hadm'
    rwa [Ideal.map_map, show (Loc.map hM').comp (algebraMap R (Localization M')) =
      algebraMap R (Localization.AtPrime q₀.ker) from RingHom.ext (Loc.map_algebraMap hM')] at h1
  set Jq : MC (Localization.AtPrime q₀.ker) n₀ := ⟨Loc.transport hM' ck, ek, hcent', hnn', hanti'⟩
  have hinvq : IsInv (Iloc Iw q₀.ker) n₀ ek :=
    ⟨⟨Jq, hadmq₀, rfl⟩, fun J' hJ' => (hbound q₀ hg J' hJ').1⟩
  obtain rfl := hinvq.card_eq J₀.c
  have hek : ek = pad (D.n + 1) D.J.e := by
    rw [← hJ₀e]; exact hinvq.unique hJ₀inv
  -- homogeneous elements lie in the chart ideal near the vertex
  set y : R := ⟨LaurentPolynomial.C f * T j, C_mul_T_mem_ReesAlg hf⟩
  have hy₀ : algebraMap R (Localization.AtPrime q₀.ker) y ∈
      (ck.RF ek (1 / d)).map (Loc.map (hctrl q₀.ker hg)) := by
    rw [Loc.map_RF, ← (hbound q₀ hg J₀ hJ₀adm).2 (by rw [hJ₀e, hek]) (1 / d)]
    exact hJ₀homog j hj f hf
  obtain ⟨h, hh, hhy⟩ := Loc.exists_of_mem_map (hctrl q₀.ker hg) _ hy₀
  -- a rescaling moving `Q` into `D(g h)`
  set G := g * h
  have hG : hcomp Φ G 0 ∉ Q.ker := by
    intro hGP
    have hGP₀ : G ∉ q₀.ker := fun h' => (Ideal.IsPrime.mem_or_mem inferInstance h').elim hg hh
    apply hGP₀
    rw [hq₀, mem_vertexG]
    have : hcomp Φ G 0 = algebraMap A R ((G : A[T;T⁻¹]).coeff 0) := by
      apply Subtype.ext
      show LaurentPolynomial.C ((G : A[T;T⁻¹]).coeff 0) * T 0 = _
      rw [T_zero, mul_one, LaurentPolynomial.C_eq_algebraMap]; rfl
    rw [this] at hGP
    rw [hqker]
    exact hGP
  obtain ⟨μ, hμ, hμG⟩ := exists_reesScale_not_mem_pt Φ hneg Q hsQ G hG
  set σ := reesScale Φ (qUnit (B := A) μ hμ)
  set Q' : Pt R := Q.pullback (σ : R →+* R)
  have hQ'ker : Q'.ker = Q.ker.comap (σ : R →+* R) := Pt.pullback_ker Q _
  have hgQ' : g ∉ Q'.ker := fun h' => hμG (by
    rw [hQ'ker, Ideal.mem_comap] at h'
    exact (show σ G ∈ Q.ker by rw [map_mul]; exact Q.ker.mul_mem_right _ h'))
  have hhQ' : h ∉ Q'.ker := fun h' => hμG (by
    rw [hQ'ker, Ideal.mem_comap] at h'
    exact (show σ G ∈ Q.ker by rw [map_mul]; exact Q.ker.mul_mem_left _ h'))
  -- the invariant at `Q'`: the given one, transported by `σ⁻¹`
  have hσ : Iw.map σ = Iw := reesScale_weakT Φ _ d hId
  have hσs : Iw.map σ.symm = Iw := by
    conv_lhs => rw [← hσ]
    exact Ideal.map_of_equiv σ
  have hv' : InvAt Iw Q'.ker v := by
    refine InvAt.of_ringEquiv σ.symm hσs Q'.ker ?_
    convert hv using 1
    ext x
    rw [Ideal.mem_comap, hQ'ker, Ideal.mem_comap]
    simp
  obtain ⟨n'', e', he', rfl⟩ := hv'
  obtain rfl := he'.card_eq (Loc.transport (hctrl Q'.ker hgQ') ck)
  obtain ⟨⟨J', hJ', hJ'e⟩, hmin'⟩ := he'
  have hle := (hbound Q' hgQ' J' hJ').1
  rw [hJ'e, hek] at hle
  rcases hle.lt_or_eq with hlt | heq
  · have := ext0_lt hlt
    rwa [ext0_pad (by omega), D.hev] at this
  · exfalso
    -- equality forces `y ∈ Q'`, hence `y ∈ Q`
    have hRF := (hbound Q' hgQ' J' hJ').2 (by rw [hJ'e, hek]; exact (toLex.injective heq).symm)
    have hmem : algebraMap R (Localization.AtPrime Q'.ker) (h * y) ∈ J'.RF (1 / d) := by
      rw [hRF (1 / d), ← Loc.map_RF, ← Loc.map_algebraMap (hctrl Q'.ker hgQ')]
      exact Ideal.mem_map_of_mem _ hhy
    have hmax' := J'.centred.RF_le_maximalIdeal (show (0 : ℚ) < 1 / d by positivity) hmem
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q'.ker] at hmax'
    have hyQ' : y ∈ Q'.ker := (Ideal.IsPrime.mem_or_mem inferInstance hmax').resolve_left hhQ'
    rw [hQ'ker, Ideal.mem_comap] at hyQ'
    apply hyQ
    have : σ y = algebraMap A R ↑((qUnit (B := A) μ hμ) ^ j) * y := by
      apply Subtype.ext
      rw [reesScale_coe]
      show lscale _ (LaurentPolynomial.C f * T j) =
        algebraMap A A[T;T⁻¹] ↑((qUnit (B := A) μ hμ) ^ j) * (LaurentPolynomial.C f * T j)
      rw [lscale_C_mul_T, ← LaurentPolynomial.C_eq_algebraMap, ← mul_assoc, ← map_mul, mul_comm f]
    rw [show (σ : R →+* R) y = σ y from rfl, this] at hyQ'
    refine ((Ideal.IsPrime.mem_or_mem inferInstance hyQ').resolve_left fun hu => ?_)
    have hunit : IsUnit (algebraMap A R ↑((qUnit (B := A) μ hμ) ^ j)) := (Units.isUnit _).map _
    exact (Ideal.IsMaximal.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem _ hu hunit)

end BezoutCounterexample.Principalization
