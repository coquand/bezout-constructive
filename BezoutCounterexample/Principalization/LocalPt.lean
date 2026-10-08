import BezoutCounterexample.Principalization.Globalize
import BezoutCounterexample.Principalization.RecentrePos
import BezoutCounterexample.Principalization.SpreadPos
import BezoutCounterexample.Principalization.TransferPos
import BezoutCounterexample.Principalization.Points

/-!
# Local structure of the invariant at an explicit point (D3.4 (c), leaf)

`local_structure` (Globalize) at a maximal ideal `𝔪` uses: Hilbert's basis theorem (`I.FG`,
`𝔪.FG`), a chart near `𝔪` (`exists_chart_away`, `choose`), the recentring by `minpoly` with
Zariski (`exists_centred_transport`), the classical start, run and spreading of Method 1
(`sa_zero_Q`, `spread_run`), and the classical transfer (`transfer_bound`) at every `𝔪' ∌ g`.
At an explicit point `q : Pt A`:

* `Pt.zAt`, `Pt.zAt_spec`: the point of `A_q` (`ζ x = 0 ↔ x ∈ 𝔪`). Same as coll-8a's
  `Pt.ζloc` (ChainLiftReesL3e); unified at integration;
* `exists_centred_transport_pt`: the recentring with `exists_sep_poly` (Kronecker and the zero
  test of the point) in place of `minpoly`, and `isCentred_of_mem_N` in place of `𝔪.FG`;
* `local_structure_pt`: the conclusion of `local_structure` with the chart near `q` as an input
  (`c₀` over `A_f`, `f ∉ q.ker`), generators `I = (l)`, the run from `sa_zero_pos` and
  `spread_run_pos`, and the bound at every explicit point `p` with `g ∉ p.ker`
  (`transfer_bound_pos` with `Pt.dec_local`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalization IsLocalRing Polynomial Constructive

section Point

variable {A : Type} [CommRing A] [Algebra ℚ A]

/-- The explicit point of the local ring at a point. -/
def Pt.zAt (q : Pt A) : Localization.AtPrime q.ker →ₐ[ℚ] q.L :=
  (IsLocalization.lift (M := q.ker.primeCompl) (S := Localization.AtPrime q.ker)
    (g := (q.z : A →+* q.L)) fun s => isUnit_iff_ne_zero.2 fun h => s.2 (q.mem_ker.2 h)).toRatAlgHom

lemma Pt.zAt_spec (q : Pt A) (x : Localization.AtPrime q.ker) :
    q.zAt x = 0 ↔ x ∈ maximalIdeal (Localization.AtPrime q.ker) := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.ker.primeCompl x
  rw [IsLocalization.AtPrime.mk'_mem_maximal_iff _ q.ker a s]
  show IsLocalization.lift _ (IsLocalization.mk' _ a s) = 0 ↔ _
  rw [IsLocalization.lift_mk'_spec, mul_zero]
  exact q.mem_ker.symm

end Point

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A]
  -- I4 (D3.6): the per-point instances instead of `[Algebra.Smooth ℚ A]`, so that the twins apply
  -- to the Rees algebra (`i4_of_smooth` recovers them from smoothness)
  [hI4a : ∀ q : Pt A, Fact (BezoutCounterexample.Constructive.PolyIndNoeth (Localization.AtPrime q.ker))]
  [hI4b : ∀ q : Pt A, Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker)]
  [hI4c : ∀ q : Pt A, Algebra.FormallySmooth ℚ (IsLocalRing.ResidueField (Localization.AtPrime q.ker))]

/-- **Recentring over a localization at an explicit point** (`exists_centred_transport` with the
separable polynomials of `exists_sep_poly` in place of `minpoly`). -/
lemma exists_centred_transport_pt (q : Pt A) {n : ℕ} {M : Submonoid A}
    (hM : M ≤ q.ker.primeCompl) (c : Chart (Localization M) n) :
    ∃ M', ∃ hE : Loc.Ext M q.ker.primeCompl M', ∃ c₁ : Chart (Localization M') n,
      (Loc.transport hE.le₂ c₁).IsCentred := by
  have hN := Ideal.primeCompl_le_nonZeroDivisors q.ker
  set cN := Loc.transport hM c
  set ζ := q.zAt
  obtain ⟨P, hP⟩ := fin_choice (P := fun i (P : ℚ[X]) => aeval (ζ (cN.x i)) P = 0 ∧
    aeval (ζ (cN.x i)) (derivative P) ≠ 0 ∧ (ζ (cN.x i) = 0 → P = X))
    fun i => exists_sep_poly q.dec (ζ (cN.x i))
  have hmap : ∀ (a : Localization.AtPrime q.ker) (p : ℚ[X]), ζ (aeval a p) = aeval (ζ a) p :=
    fun a p => (Polynomial.aeval_algHom_apply ζ a p).symm
  set y₀ : Fin n → Localization M := fun i => aeval (c.x i) (P i) with hy₀
  set yN : Fin n → Localization.AtPrime q.ker := fun i => aeval (cN.x i) (P i) with hyN
  have hy : ∀ i, Loc.map hM (y₀ i) = yN i := fun i => by
    rw [hy₀, hyN]; simp only [Loc.map_aeval]; rfl
  have hjacN : cN.jac yN = Matrix.diagonal fun j => aeval (cN.x j) (derivative (P j)) := by
    ext i j
    simp only [Chart.jac, Matrix.of_apply, hyN, Derivation.map_aeval, cN.d_x, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  have hdetN : IsUnit (cN.jac yN).det := by
    rw [hjacN, Matrix.det_diagonal, IsUnit.prod_univ_iff]
    intro j
    rw [← notMem_maximalIdeal, ← q.zAt_spec, hmap]
    exact (hP j).2.1
  have hdet : Loc.map hM (c.jac y₀).det = (cN.jac yN).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Chart.jac, Matrix.of_apply,
      ← Loc.transport_d, ← hy]
    rfl
  obtain ⟨M', hE, hunit⟩ := Loc.spread_isUnit hM hN (hdet ▸ hdetN)
  set c' := Loc.transport hE.le₁ c
  have hjac : (c'.jac (fun i => Loc.map hE.le₁ (y₀ i))).det = Loc.map hE.le₁ (c.jac y₀).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Chart.jac, Matrix.of_apply, c',
      Loc.transport_d]
  refine ⟨M', hE, c'.change _ (hjac ▸ hunit), Chart.isCentred_of_mem_N fun i => ?_⟩
  rw [Loc.transport_x, Chart.change_x, Loc.map_apply_comp, hy, ← q.zAt_spec, hyN]
  simp only
  rw [hmap]
  exact (hP i).1

/-- A run from stage `j ≤ n` ends at a stage `k ≤ n`. -/
lemma IsRun.le_n {S : Type*} [CommRing S] [Algebra ℚ S] {n : ℕ} {I : Ideal S} {j : ℕ}
    {c : Chart S n} {e : Fin n → ℚ} {k : ℕ} {ck : Chart S n} {ek : Fin n → ℚ}
    (h : IsRun I j c e k ck ek) (hj : j ≤ n) : k ≤ n := by
  induction h with
  | refl => exact hj
  | step hj' f hf β l hl hβl hlam hN hunit hb u hu hnext ih => exact ih hj'

/-- **Local structure of the invariant at an explicit point** (`local_structure` with the chart
near `q` as an input and the bound at explicit points). -/
theorem local_structure_pt (I : Ideal A) (hI : I ≠ ⊥) (l : List A) (hl : I = lspan l) (q : Pt A)
    (hIq : I ≤ q.ker) {f : A} (hf : f ∉ q.ker) {n : ℕ} (c₀ : Chart (Localization.Away f) n) :
    ∃ (M' : Submonoid A) (g : A), g ∉ q.ker ∧ ∃ hctrl : Loc.Ctrl M' g,
      ∃ (k : ℕ) (ck : Chart (Localization M') n) (ek : Fin n → ℚ), k ≤ n ∧
      (∀ i, ek i ≠ 0 ↔ (i : ℕ) < k) ∧ (∀ i, 0 ≤ ek i) ∧ Antitone ek ∧
      I.map (algebraMap A (Localization M')) ≤ ck.RF ek 1 ∧
      ∃ hM' : M' ≤ q.ker.primeCompl, (Loc.transport hM' ck).IsCentred ∧
      ∀ (p : Pt A) (hg' : g ∉ p.ker),
        ∀ J' : MC (Localization.AtPrime p.ker) n,
          J'.Adm (I.map (algebraMap A (Localization.AtPrime p.ker))) →
          toLex ek ≤ toLex J'.e ∧
          (J'.e = ek → ∀ t, J'.RF t = (Loc.transport (hctrl p.ker hg') ck).RF ek t) := by
  have hM₀ : Submonoid.powers f ≤ q.ker.primeCompl := (Submonoid.powers_le).2 hf
  obtain ⟨M₁, hE₁, c₁, hc₁⟩ := exists_centred_transport_pt q hM₀ c₀
  -- Method 1 at `q`
  set IR := I.map (algebraMap A (Localization.AtPrime q.ker))
  have hIR : IR ≠ ⊥ := by
    intro h
    apply hI
    rw [eq_bot_iff]
    intro a ha
    have : algebraMap A (Localization.AtPrime q.ker) a = 0 := by
      rw [← Ideal.mem_bot, ← h]; exact Ideal.mem_map_of_mem _ ha
    rw [Ideal.mem_bot]
    exact (IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors q.ker))
      (by rw [this, map_zero])
  have hIRm : IR ≤ maximalIdeal (Localization.AtPrime q.ker) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q.ker) q.ker a]
    exact hIq ha
  have hSA0 := MC.sa_zero_pos q.dec_local _ (hlR q.ker I l hl) hIR hIRm _ hc₁
  obtain ⟨M', hE, k, ck, ek, hrun, hadm, hsupp, hnn, hanti, hcent⟩ :=
    spread_run_pos q.ker q.dec_local I l hl (n - 0) 0 rfl M₁ hE₁.le₂ c₁ 0 hc₁ (fun _ => le_rfl)
      (fun _ _ _ => le_rfl) hSA0
  -- control
  obtain ⟨t₁, ht₁, hct₁⟩ := hE₁.ctrl
  obtain ⟨t₂, ht₂, hct₂⟩ := hE.ctrl
  have hctrl : Loc.Ctrl M' (f * t₁ * t₂) := hct₂ _ (hct₁ f (Loc.ctrl_powers f))
  have hg : f * t₁ * t₂ ∉ q.ker :=
    q.ker.primeCompl.mul_mem (q.ker.primeCompl.mul_mem hf ht₁) ht₂
  refine ⟨M', f * t₁ * t₂, hg, hctrl, k, ck, ek, hrun.le_n (Nat.zero_le n), hsupp, hnn, hanti, hadm, hE.le₂, hcent,
    fun p hg' J' hJ' => ?_⟩
  -- transfer to `p`
  have hM'p : M' ≤ p.ker.primeCompl := hctrl p.ker hg'
  set ψ := Loc.map hM'p
  have hcompat := Loc.compat_transport hM'p (Loc.transport hE.le₁ c₁)
  obtain ⟨ck'', hck'', hbound⟩ := hrun.transfer_bound_pos p.dec_local hcompat
  have hIψ : (I.map (algebraMap A (Localization M'))).map ψ =
      I.map (algebraMap A (Localization.AtPrime p.ker)) := Loc.map_map_algebraMap hM'p I
  have hck : ck'' = Loc.transport hM'p ck :=
    Chart.eq_of_x (funext fun i => by
      have := hck''.x i
      simpa [pushIdx, Fin.castLE_refl] using this)
  obtain ⟨h1, h2⟩ := hbound J' (by rw [hIψ]; exact hJ')
  rw [pad_refl] at h1 h2
  refine ⟨h1, fun he t => ?_⟩
  rw [h2 he t, hck]

end BezoutCounterexample.Principalization
