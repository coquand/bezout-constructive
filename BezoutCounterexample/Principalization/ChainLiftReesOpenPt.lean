import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesOpenW
import BezoutCounterexample.Principalization.ChainLiftReesRowsZ
import BezoutCounterexample.Principalization.ChainLiftReesLocalPt
import BezoutCounterexample.Principalization.ChainLiftReesL3e

/-!
# The weighted-chart open of one `LocDataPt` chart (Task B, Rees layer S6, producer part 3)

`rees_rows_weighted_pt` (stage 1, the rows) and `rees_open_weighted_of_rows` (stage 2, in a common
global presentation `GR` containing the rows of all opens, see `rowsW`/`rowsW_vanish`): for one chart
`D : LocDataPt` (with the cover facts `hglob`, `hloc`), its
head numerators, an `A`-piece `S` whose heads are `Dq · a`, and integer Rees generators, the global
presentation `GR` of the Rees algebra (with the model rows appended) has chart data and conormal
injectivity on the weighted-chart open of `S.h · β · γ`. Here `γ ↦ c gᴺ` and `β ↦ c' gˢ`.

Ingredients: L1/L2 at the chart (`exists_heads_poly_pt`, `exists_rees_expansion_pt`), cleared to
`ℤ` (`exists_head_rows`, `exists_yrow_int`), appended to the kernel (`exists_reesKer_ext`). L3 comes
from `hloc_of_cent` + `hcent_of_locDataPt`, and everything is assembled by `exists_reesChart_of_l3`.
The I4 instances at the local rings `A_q` are hypotheses, filled today from `Algebra.Smooth ℚ A`.
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive
open LaurentPolynomial hiding C

set_option linter.unusedSectionVars false

section Eval

variable {A : Type} [CommRing A] [Algebra ℚ A] {m kc l r : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (gZ : Fin r → MvPolynomial (Fin (m + (kc + l))) ℤ) (δ : Fin r → ℕ) (Ly : Fin r → A[T;T⁻¹])

lemma evG_reesYL : evG G e (reesYL G e gZ δ) = reesVec G e gZ δ := by
  funext v
  refine Fin.addCases (fun v => ?_) (fun v => ?_) v
  · simp [evG, reesVec, toAq]
  · refine Fin.addCases (fun o => ?_) (fun j => ?_) v
    · simp [evG, reesVec]
    · simp [evG, reesVec]

lemma evG_gS : evG G e Ly (gS (l := l) (r := r)) = T (-1) := by simp [evG, gS]

lemma evG_gYr (j : Fin r) : evG G e Ly (gYr (m := m) (kc := kc) (l := l) j) = Ly j := by
  simp [evG, gYr]

lemma aeval_evG_gY (p : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    aeval (evG G e Ly) (rename gY p) = LaurentPolynomial.C (toAZ G e p) := by
  rw [aeval_rename]
  have : (aeval (evG G e Ly ∘ gY)).toRingHom =
      (LaurentPolynomial.C : A →+* A[T;T⁻¹]).comp
        (e.toRingHom.comp ((Ideal.Quotient.mk _).comp toQZ)) := by
    refine MvPolynomial.ringHom_ext (fun n => intHom_C _ _ n) (fun v => ?_)
    simp [evG, gY, toQZ]
  exact RingHom.congr_fun this p

variable (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (γ : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ)

/-- Under the heads' evaluations, `ψ_W` followed by the global evaluation is `evW`. -/
lemma aeval_evG_reesψW (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hP : ∀ i, aeval (evG G e Ly) (P i) =
      LaurentPolynomial.C (toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i)))) * T (w i))
    (q : MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ) :
    aeval (evG G e Ly) (aeval (reesψW P) q) = aeval (evW G e F γ w) q := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  suffices hfun : (fun i => aeval (evG G e Ly) (reesψW P i)) = evW G e F γ w by rw [hfun]
  funext v
  refine Fin.addCases (fun v => ?_) (fun v => ?_) v
  · refine Fin.addCases (fun o => ?_) (fun i => ?_) v
    · simp [reesψW, evW, evG_gS]
    · simp [reesψW, evW, hP]
  · simp only [reesψW, evW, Fin.addCases_right, aeval_X]
    simp [evG, gY]

lemma toAZ_eq_zero_of_mem {p : MvPolynomial (Fin (m + (kc + l))) ℤ} (hp : p ∈ lspan G) :
    toAZ G e p = 0 := by
  rw [toAZ, Ideal.Quotient.eq_zero_iff_mem.2 (toQZ_mem_lspan_map hp), map_zero]

/-- **The `y`-rows with one `β`**: per-row identities `aeval Qⱼ = Dⱼ · C(g^{Sⱼ}) yⱼ` give one integer
`β ↦ c gˢ` and rows with `C(β) yⱼ = aeval Qⱼ` (a uniform `S`, then common multiples). -/
lemma exists_yrows (y : Fin r → A[T;T⁻¹]) (g : A)
    (h : ∀ j, ∃ (S D : ℕ) (Qj : MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ), 0 < D ∧
      aeval (evW G e F γ w) Qj = (D : A[T;T⁻¹]) * (LaurentPolynomial.C (g ^ S) * y j)) :
    ∃ (β : MvPolynomial (Fin (m + (kc + l))) ℤ) (cβ S : ℕ)
      (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ),
      0 < cβ ∧ toAZ G e β = (cβ : A) * g ^ S ∧
      ∀ j, LaurentPolynomial.C (toAZ G e β) * y j = aeval (evW G e F γ w) (Q j) := by
  -- a uniform `S`
  obtain ⟨S, hS⟩ := exists_uniform_list
    (P := fun j S => ∃ (D : ℕ) (Qj : MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ), 0 < D ∧
      aeval (evW G e F γ w) Qj = (D : A[T;T⁻¹]) * (LaurentPolynomial.C (g ^ S) * y j))
    (fun j S S' hSS' ⟨D, Qj, hD, hQ⟩ => by
      obtain ⟨c, pZ, hc, hpZ⟩ := exists_toAq_int G e (g ^ (S' - S))
      refine ⟨c * D, rename wY pZ * Qj, Nat.mul_pos hc hD, ?_⟩
      rw [map_mul, aeval_evW_wY, hQ, show toAZ G e pZ = toAq G e (toQZ pZ) from rfl, hpZ,
        ← Nat.sub_add_cancel hSS', pow_add, Nat.add_sub_cancel]
      simp only [map_mul, map_natCast, map_pow, Nat.cast_mul]
      ring)
    (List.finRange r) fun j _ => by
      obtain ⟨S, D, Qj, hD, hQ⟩ := h j
      exact ⟨S, D, Qj, hD, hQ⟩
  obtain ⟨DQ, hDQ⟩ := Constructive.finite_choice_dep (ι := Fin r)
    (P := fun j (x : ℕ × MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ) => 0 < x.1 ∧
      aeval (evW G e F γ w) x.2 = (x.1 : A[T;T⁻¹]) * (LaurentPolynomial.C (g ^ S) * y j))
    fun j => by
      obtain ⟨D, Qj, hD, hQ⟩ := hS j (List.mem_finRange j)
      exact ⟨(D, Qj), hD, hQ⟩
  obtain ⟨Dc, k, hDc, hk⟩ := exists_common_mul (fun j => (DQ j).1) fun j => (hDQ j).1
  obtain ⟨Eβ, β₀, hEβ, hβ₀⟩ := exists_toAq_int G e (g ^ S)
  refine ⟨(Dc : MvPolynomial _ ℤ) * β₀, Dc * Eβ, S,
    fun j => ((k j * Eβ : ℕ) : MvPolynomial _ ℤ) * (DQ j).2, Nat.mul_pos hDc hEβ, ?_, fun j => ?_⟩
  · rw [toAZ_mul', toAZ_natCast, show toAZ G e β₀ = toAq G e (toQZ β₀) from rfl, hβ₀]
    push_cast; ring
  · rw [map_mul, map_natCast, (hDQ j).2, toAZ_mul', toAZ_natCast,
      show toAZ G e β₀ = toAq G e (toQZ β₀) from rfl, hβ₀, ← hk j]
    simp only [map_mul, map_natCast, map_pow, Nat.cast_mul]
    ring

/-- **The rows of a weighted chart** (to be appended to the global relations): `F_eq`, the heads
`γ x̃_q − s^{w_q} P̃_q` and the `y`-rows `β yⱼ − Qⱼ(s, P̃, Y)`. -/
def rowsW (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) (β : MvPolynomial (Fin (m + (kc + l))) ℤ)
    (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ) :
    List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ) :=
  (List.ofFn fun i : Fin m => rename gY (F (Fin.castAdd _ i))) ++
  (List.ofFn fun q : Fin kc =>
    rename gY (γ * F (Fin.natAdd m (Fin.castAdd l q))) - X gS ^ w q * P q) ++
  (List.ofFn fun j : Fin r => rename gY β * X (gYr j) - aeval (reesψW P) (Q j))

lemma rowsW_vanish (hF : ∀ i : Fin m, F (Fin.castAdd _ i) ∈ lspan G)
    (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (hP : ∀ i, aeval (evG G e Ly) (P i) =
      LaurentPolynomial.C (toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i)))) * T (w i))
    (β : MvPolynomial (Fin (m + (kc + l))) ℤ)
    (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)
    (hy : ∀ j, LaurentPolynomial.C (toAZ G e β) * Ly j = aeval (evW G e F γ w) (Q j)) :
    ∀ x ∈ rowsW F γ w P β Q, aeval (evG G e Ly) x = 0 := by
  intro x hx
  simp only [rowsW, List.mem_append, List.mem_ofFn] at hx
  rcases hx with (⟨i, rfl⟩ | ⟨q, rfl⟩) | ⟨j, rfl⟩
  · rw [aeval_evG_gY, toAZ_eq_zero_of_mem G e (hF i), map_zero]
  · rw [map_sub, aeval_evG_gY, map_mul, map_pow, aeval_X, evG_gS, hP q, T_pow,
      mul_comm (T _), mul_assoc (LaurentPolynomial.C _), ← T_add,
      show ((w q : ℤ) + (w q : ℤ) * -1) = 0 by ring, T_zero, mul_one, sub_self]
  · rw [map_sub, map_mul, aeval_evG_gY, aeval_X, evG_gYr, aeval_evG_reesψW G e Ly F γ w P hP,
      ← hy j, sub_self]

end Eval

section Main

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
  [IsNoetherianRing A] {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal] {𝔭 : Ideal A}

/-- **The rows of the weighted chart of one `LocDataPt` chart** (stage 1): `γ ↦ cγ gᴺ`,
`β ↦ cβ gˢ`, integer heads `P̃` (`hP`) and `y`-rows `Q` (`hy`), from L1/L2 at the chart. -/
theorem rees_rows_weighted_pt {m kc l r : ℕ}
    (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
    (D : LocDataPt I v₀ 𝔪) (hkn : kc ≤ D.n) (hk : D.k = kc)
    (hglob : ∀ (b : A) (t : ℚ), algebraMap A D.B b ∈ D.RFB t → ∃ N : ℕ, D.g ^ N * b ∈ compFPt I 𝔭 t)
    (hloc : ∀ (t : ℚ) (z : A), z ∈ compFPt I 𝔭 t → algebraMap A D.B z ∈ D.RFB t)
    (Φ : WFil A) {d : ℕ} (hΦ : ∀ j : ℤ, Φ.F j = compFPt I 𝔭 ((j : ℚ) / d)) (hd : 0 < d)
    (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
    (gZ : Fin r → MvPolynomial (Fin (m + (kc + l))) ℤ) (δ : Fin r → ℕ)
    (hgF : ∀ i, toAq G e (toQZ (gZ i)) ∈ Φ.F (δ i))
    (hgen : ∀ (j : ℤ) (f : A), f ∈ Φ.F j →
      LaurentPolynomial.C f * T j ∈ Algebra.adjoin A (insert (T (-1)) (Set.range (reesYL G e gZ δ))))
    (s : ℕ) (a : Fin D.n → A)
    (ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s = algebraMap A D.B (a i))
    (Dq : Fin kc → ℕ) (hDq : ∀ i, 0 < Dq i) (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
    (hhead : ∀ i, toAZ G e (F (Fin.natAdd m (Fin.castAdd l i))) = (Dq i : A) * a (ιk hkn i))
    (wf : Fin D.n → ℕ) (hwf : ∀ i, (wf i : ℚ) = d * D.ek i) :
    ∃ (γ β : MvPolynomial (Fin (m + (kc + l))) ℤ) (cγ cβ N S' : ℕ)
      (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
      (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ),
      0 < cγ ∧ 0 < cβ ∧ toAZ G e γ = (cγ : A) * D.g ^ N ∧ toAZ G e β = (cβ : A) * D.g ^ S' ∧
      (∀ i, aeval (evG G e (reesYL G e gZ δ)) (P i) =
        LaurentPolynomial.C (toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i)))) * T (wf (ιk hkn i))) ∧
      (∀ j, LaurentPolynomial.C (toAZ G e β) * reesYL G e gZ δ j =
        aeval (evW G e F γ (fun i => wf (ιk hkn i))) (Q j)) := by
  set w : Fin kc → ℕ := fun i => wf (ιk hkn i) with hwdef
  -- L1: the heads
  obtain ⟨N, -, Pq', -, hPq'⟩ := exists_heads_poly_pt D hglob Φ hΦ hd G e gZ δ hneg hgF hgen s a ha wf hwf
  obtain ⟨Eγ, γ₀, hEγ, hγ₀⟩ := exists_toAq_int G e (D.g ^ N)
  obtain ⟨Dh, P, hDh, hP⟩ := exists_head_rows G e F w (reesYL G e gZ δ) (D.g ^ N)
    (fun i => a (ιk hkn i)) (fun i => Pq' (ιk hkn i))
    (fun i => by rw [evG_reesYL, hPq' (ιk hkn i)]) γ₀ Eγ hγ₀ Dq hhead
  set γ : MvPolynomial (Fin (m + (kc + l))) ℤ := (Dh : MvPolynomial _ ℤ) * γ₀ with hγdef
  have hγA : toAZ G e γ = ((Dh * Eγ : ℕ) : A) * D.g ^ N := by
    rw [hγdef, toAZ_mul', toAZ_natCast, show toAZ G e γ₀ = toAq G e (toQZ γ₀) from rfl, hγ₀]
    push_cast; ring
  have hu : ∀ q, toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l q))) =
      ((Dh * Eγ * Dq q : ℕ) : A) * (D.g ^ N * a (ιk hkn q)) := fun q => by
    rw [toAZ_mul', hγA, hhead]; push_cast; ring
  -- L2: the `y`-rows
  obtain ⟨β, cβ, S', Q, hcβ, hβA, hy⟩ := exists_yrows G e F γ w (reesYL G e gZ δ) D.g fun j => by
    obtain ⟨Sj, K, b, α, ex, hα0, -, hexp⟩ :=
      exists_rees_expansion_pt D hloc Φ hΦ hd s a ha wf hwf N (hgF j)
    have hαk : ∀ i (l : Fin D.n), kc ≤ (l : ℕ) → α i l = 0 := fun i l hl => by
      refine hα0 i l ?_
      by_cases h0 : D.ek l = 0
      · exact h0
      · exact absurd ((D.supp l).1 h0) (by rw [hk]; omega)
    have hexp' : LaurentPolynomial.C (D.g ^ Sj) * reesYL G e gZ δ j =
        ∑ i, LaurentPolynomial.C (b i) * T (-(ex i : ℤ)) *
          ∏ q : Fin kc, (LaurentPolynomial.C (D.g ^ N * a (ιk hkn q)) * T (w q : ℤ)) ^
            α i (ιk hkn q) := by
      rw [reesYL, ← mul_assoc, ← map_mul, hexp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [prod_pow_ιk hkn _ _ (hαk i)]
    obtain ⟨Dj, Qj, hDj, hQj⟩ := exists_yrow_int G e F γ w (reesYL G e gZ δ j)
      (LaurentPolynomial.C (D.g ^ Sj)) (fun q => D.g ^ N * a (ιk hkn q))
      (fun q => Dh * Eγ * Dq q) (fun q => Nat.mul_pos (Nat.mul_pos hDh hEγ) (hDq q)) hu
      b ex (fun i q => α i (ιk hkn q)) hexp'
    exact ⟨Sj, Dj, Qj, hDj, hQj⟩
  exact ⟨γ, β, Dh * Eγ, cβ, N, S', P, Q, Nat.mul_pos hDh hEγ, hcβ, hγA, hβA, hP, hy⟩

/-- **The weighted-chart open from its rows** (stage 2), in any global presentation `GR` of the
Rees algebra whose relations contain the rows: chart data and conormal injectivity of `GR`
(renamed along `ε`) on the open of `dW = n! · (S.h β γ g̃)ⁿ`, where `g̃ ↦ cg g`. -/
theorem rees_open_weighted_of_rows {m kc l r : ℕ}
    (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
    (D : LocDataPt I v₀ 𝔪) (hkn : kc ≤ D.n) (hk : D.k = kc)
    {d : ℕ} (hd : 0 < d) (Ly : Fin r → A[T;T⁻¹])
    (s : ℕ) (a : Fin D.n → A)
    (ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s = algebraMap A D.B (a i))
    (Dq : Fin kc → ℕ) (hDq : ∀ i, 0 < Dq i) (S : SquarePiece m (kc + l) G)
    (hhead : ∀ i, toAZ G e (S.F (Fin.natAdd m (Fin.castAdd l i))) = (Dq i : A) * a (ιk hkn i))
    (wf : Fin D.n → ℕ) (hwf : ∀ i, (wf i : ℚ) = d * D.ek i)
    (inst₁ : ∀ q : Pt A, Fact (PolyIndNoeth (Localization.AtPrime q.ker)))
    (inst₂ : ∀ q : Pt A, Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker))
    (inst₃ : ∀ q : Pt A,
      Algebra.FormallySmooth ℚ (IsLocalRing.ResidueField (Localization.AtPrime q.ker)))
    (γ β gt : MvPolynomial (Fin (m + (kc + l))) ℤ) (cγ cg N : ℕ)
    (hγA : toAZ G e γ = (cγ : A) * D.g ^ N) (hgtA : toAZ G e gt = (cg : A) * D.g)
    (P : Fin kc → MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ)
    (Q : Fin r → MvPolynomial (Fin ((1 + kc) + (m + (kc + l)))) ℤ)
    (hP : ∀ i, aeval (evG G e Ly) (P i) =
      LaurentPolynomial.C (toAZ G e (γ * S.F (Fin.natAdd m (Fin.castAdd l i)))) * T (wf (ιk hkn i)))
    (hy : ∀ j, LaurentPolynomial.C (toAZ G e β) * Ly j =
      aeval (evW G e S.F γ (fun i => wf (ιk hkn i))) (Q j))
    (GR : List (MvPolynomial (Fin ((m + (kc + l)) + (1 + r))) ℤ))
    (hGR0 : ∀ g ∈ GR, aeval (evG G e Ly) g = 0)
    (hrows : ∀ x ∈ rowsW S.F γ (fun i => wf (ιk hkn i)) P β Q, x ∈ lspan GR)
    (ε : Fin ((m + (kc + l)) + (1 + r)) ≃ Fin ((m + r) + ((1 + kc) + l))) :
    ∃ n : ℕ,
      let w : Fin kc → ℕ := fun i => wf (ιk hkn i)
      let dW : MvPolynomial (Fin (((m + kc) + r) + ((1 + kc) + l))) ℤ :=
        ((n.factorial : ℕ) : MvPolynomial _ ℤ) * rename varY (S.h * (β * (γ * gt))) ^ n
      let GR' := GR.map (rename ε)
      let ψ' := fun i => rename ε (reesψ P i)
      (∃ T : ChartData GR', T.x = (fun i => rename ε (Fin.addCases (Fin.addCases
          (fun _ => X gS) P) (fun z => rename gY (S.F (Fin.natAdd m (Fin.natAdd kc z)))) i)) ∧
        T.c = aeval ψ' (dW ^ 2 * (dW ^ 2 * (jacPoly (reesSys S.F γ β w Q)).det))) ∧
      ConormalInj GR' (aeval ψ' ((jacPoly (reesSys S.F γ β w Q)).det * dW ^ 2)) := by
  set w : Fin kc → ℕ := fun i => wf (ιk hkn i) with hwdef
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hw0 : ∀ i, 0 < w i := fun i => by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h1 := hwf (ιk hkn i)
    rw [show wf (ιk hkn i) = 0 from h0, Nat.cast_zero, eq_comm, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact hdq h1
    · exact (D.supp (ιk hkn i)).2 (by rw [hk]; exact i.2) h1
  set dA : MvPolynomial (Fin (m + (kc + l))) ℤ := S.h * (β * (γ * gt)) with hdA
  -- L3
  have Hloc : ∀ q : Pt A, toAZ G e dA ∉ q.ker →
      ∀ p : MvPolynomial (Option (Fin kc)) (Localization.AtPrime q.ker),
        aeval (lGen (xq G e S.F γ q) w) p = 0 →
          p ∈ Ideal.span (Set.range (lRel (xq G e S.F γ q) w)) := by
    refine hloc_of_cent G e S.F γ w dA hw0 fun q hq hall p hp => ?_
    have := inst₁ q
    have := inst₂ q
    have := inst₃ q
    have hdA' : toAZ G e dA = toAZ G e S.h * (toAZ G e β * (toAZ G e γ * toAZ G e gt)) := by
      simp only [hdA, toAZ_mul']
    have hγq : toAZ G e γ ∉ q.ker := fun h0 => hq (by
      rw [hdA']; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ h0)))
    have hgq : D.g ∉ q.ker := fun h0 => hq (by
      rw [hdA', hgtA]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
        (Ideal.mul_mem_left _ _ h0))))
    exact hcent_of_locDataPt G e S.F γ w D hkn hk s a ha Dq hDq hhead hd wf hwf (fun i => rfl)
      q hgq hγq hall p hp
  exact exists_reesChart_of_l3 G e S.F γ β w Q S.h S.f S.genc dA (β * (γ * gt))
    (S.h * (γ * gt)) rfl (by rw [hdA]; ring) Ly hy Hloc P hP GR hGR0 ε
    (fun i => hrows _ (by simp [rowsW]))
    (fun q => hrows _ (by simp [rowsW]))
    (fun j => hrows _ (by simp [rowsW]))

end Main

end BezoutCounterexample.Principalization
