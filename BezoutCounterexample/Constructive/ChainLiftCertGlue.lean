import Mathlib
import BezoutCounterexample.Constructive.ChainLiftSmoothCert
import BezoutCounterexample.Constructive.ChainLiftChoice
import BezoutCounterexample.Constructive.ChainLiftMinorPoly

/-!
# Gluing square pieces along a cover (Task B, Rees layer S6, glue)

`exists_smoothCert_of_cover`: a cover `C ≡ Σⱼ λⱼ eⱼ` (`C > 0`) modulo `(G)`, opens whose multipliers
`ωⱼ` satisfy `eⱼ^{M+1} ≡ tⱼ ωⱼ`, and for each open square pieces with `Nⱼ ωⱼ ≡ Σₖ uⱼₖ hⱼₖ`
(`exists_minor_cover`), give a `SmoothCert`. The pieces are indexed by `Σ j, Fin Kⱼ`
(`finSigmaFinEquiv`); the constant is `(∏ Nⱼ) C^{JM+1}` (`Ideal.sum_pow_mem_span_pow`).
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open MvPolynomial

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}

/-- Flattening a `Fin J`-indexed family of lists of pieces into one list (`Fin.append`). -/
lemma exists_flatten : ∀ {J : ℕ} (K : Fin J → ℕ) (P : ∀ j, Fin (K j) → SquarePiece m n G)
    (v : ∀ j, Fin (K j) → MvPolynomial (Fin (m + n)) ℤ),
    ∃ (K' : ℕ) (P' : Fin K' → SquarePiece m n G) (v' : Fin K' → MvPolynomial (Fin (m + n)) ℤ),
      ∑ k, v' k * (P' k).h = ∑ j, ∑ k, v j k * (P j k).h
  | 0, _, _, _ => ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | J + 1, K, P, v => by
    obtain ⟨K', P', v', h⟩ := exists_flatten (fun j => K j.succ) (fun j => P j.succ) (fun j => v j.succ)
    refine ⟨K 0 + K', Fin.append (P 0) P', Fin.append (v 0) v', ?_⟩
    rw [Fin.sum_univ_add, Fin.sum_univ_succ, ← h]
    simp only [Fin.append_left, Fin.append_right]

/-- **Gluing a certificate along a cover.** -/
theorem exists_smoothCert_of_cover {J : ℕ} (e ω t lam : Fin J → MvPolynomial (Fin (m + n)) ℤ)
    (C M : ℕ) (hC : 0 < C)
    (hcov : (C : MvPolynomial (Fin (m + n)) ℤ) - ∑ j, lam j * e j ∈ lspan G)
    (hpow : ∀ j, e j ^ (M + 1) - t j * ω j ∈ lspan G)
    (hω : ∀ j, ∃ (K : ℕ) (P : Fin K → SquarePiece m n G) (u : Fin K → MvPolynomial (Fin (m + n)) ℤ)
      (N : ℕ), 0 < N ∧ (N : MvPolynomial (Fin (m + n)) ℤ) * ω j - ∑ k, u k * (P k).h ∈ lspan G) :
    Nonempty (SmoothCert m n G) := by
  set π := Ideal.Quotient.mk (lspan G)
  have hπ : ∀ {x y : MvPolynomial (Fin (m + n)) ℤ}, x - y ∈ lspan G → π x = π y :=
    fun h => Ideal.Quotient.eq.2 h
  -- the data of the opens
  obtain ⟨D, hD⟩ := finite_choice_dep (α := fun _ : Fin J =>
      (K : ℕ) × (Fin K → SquarePiece m n G) × (Fin K → MvPolynomial (Fin (m + n)) ℤ) × ℕ)
    (P := fun j a => 0 < a.2.2.2 ∧ (a.2.2.2 : MvPolynomial (Fin (m + n)) ℤ) * ω j -
      ∑ k, a.2.2.1 k * (a.2.1 k).h ∈ lspan G)
    fun j => by
      obtain ⟨K, P, u, N, hN, h⟩ := hω j
      exact ⟨⟨K, P, u, N⟩, hN, h⟩
  set K : Fin J → ℕ := fun j => (D j).1
  set N : Fin J → ℕ := fun j => (D j).2.2.2
  set R : Fin J → ℕ := fun j => ∏ i ∈ Finset.univ.erase j, N i
  have hNR : ∀ j, N j * R j = ∏ i, N i := fun j => Finset.mul_prod_erase _ N (Finset.mem_univ j)
  -- the power of the cover
  have hspan := Ideal.sum_pow_mem_span_pow Finset.univ (fun j => lam j * e j) M
  rw [Finset.coe_univ, Set.image_univ, Finset.card_univ, Fintype.card_fin] at hspan
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hspan
  set E := J * M + 1
  have hcovE : π ((C : MvPolynomial (Fin (m + n)) ℤ) ^ E) =
      ∑ j, π (c j * lam j ^ (M + 1) * t j) * π (ω j) := by
    rw [map_pow, hπ hcov, ← map_pow, ← hc, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have he : π (e j ^ (M + 1)) = π (t j) * π (ω j) := by rw [hπ (hpow j), map_mul]
    rw [mul_pow, map_mul, map_mul, he]
    simp only [map_mul, map_pow]
    ring
  -- the glued certificate
  obtain ⟨K', P', v', hflat⟩ := exists_flatten K (fun j => (D j).2.1)
    (fun j k => c j * lam j ^ (M + 1) * t j * (R j : MvPolynomial _ ℤ) * (D j).2.2.1 k)
  refine ⟨{
    K := K'
    P := P'
    C := (∏ i, N i) * C ^ E
    hC := Nat.mul_pos (Finset.prod_pos fun i _ => (hD i).1) (pow_pos hC _)
    u := v'
    cover := ?_ }⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, hflat]
  have hopen : ∀ j, ∑ k, π (c j * lam j ^ (M + 1) * t j * (R j : MvPolynomial _ ℤ) *
      (D j).2.2.1 k * ((D j).2.1 k).h) =
      π (c j * lam j ^ (M + 1) * t j) * π ((R j : MvPolynomial _ ℤ) * (N j : MvPolynomial _ ℤ)) *
        π (ω j) := by
    intro j
    have h1 : π (N j : MvPolynomial _ ℤ) * π (ω j) = ∑ k, π ((D j).2.2.1 k) * π (((D j).2.1 k).h) := by
      have := hπ (hD j).2
      rw [map_mul, map_sum] at this
      simpa only [map_mul] using this
    calc ∑ k, π (c j * lam j ^ (M + 1) * t j * (R j : MvPolynomial _ ℤ) *
          (D j).2.2.1 k * ((D j).2.1 k).h)
        = π (c j * lam j ^ (M + 1) * t j) * π (R j : MvPolynomial _ ℤ) *
            ∑ k, π ((D j).2.2.1 k) * π (((D j).2.1 k).h) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [map_mul]
          ring
      _ = _ := by rw [← h1, map_mul π (R j : MvPolynomial _ ℤ)]; ring
  simp only [map_sum]
  rw [Finset.sum_congr rfl fun j _ => hopen j]
  rw [Nat.cast_mul, Nat.cast_pow, map_mul, hcovE, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Nat.cast_mul, mul_comm (R j), hNR j]
  ring

/-- **Gluing along an ideal-membership cover**: `C ∈ (ω) + (G)` with `C > 0` (as produced by a
point argument and `int_mem`). -/
theorem exists_smoothCert_of_mem {J : ℕ} (ω : Fin J → MvPolynomial (Fin (m + n)) ℤ) (C : ℕ) (hC : 0 < C)
    (hmem : (C : MvPolynomial (Fin (m + n)) ℤ) ∈ Ideal.span (Set.range ω) ⊔ lspan G)
    (hω : ∀ j, ∃ (K : ℕ) (P : Fin K → SquarePiece m n G) (u : Fin K → MvPolynomial (Fin (m + n)) ℤ)
      (N : ℕ), 0 < N ∧ (N : MvPolynomial (Fin (m + n)) ℤ) * ω j - ∑ k, u k * (P k).h ∈ lspan G) :
    Nonempty (SmoothCert m n G) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨lam, hlam⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy
  refine exists_smoothCert_of_cover ω ω (fun _ => 1) lam C 0 hC ?_ (fun j => ?_) hω
  · have h : (C : MvPolynomial (Fin (m + n)) ℤ) - ∑ j, lam j * ω j = z := by
      rw [← hyz, ← hlam]
      simp only [smul_eq_mul, add_sub_cancel_left]
    rw [h]; exact hz
  · simp

/-- **Enumerating a finset inside a proof** (`Finset.induction_on`; no `toList`). -/
lemma exists_fin_enum {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    ∃ (K : ℕ) (f : Fin K → ι), ∀ g : ι → MvPolynomial (Fin (m + n)) ℤ, ∑ k, g (f k) = ∑ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Fin.elim0, fun g => by simp⟩
  | insert a s ha ih =>
    obtain ⟨K, f, hf⟩ := ih
    refine ⟨K + 1, Fin.cons a f, fun g => ?_⟩
    rw [Fin.sum_univ_succ, Finset.sum_insert ha, ← hf g]
    simp only [Fin.cons_zero, Fin.cons_succ]

/-- **Chart data and conormal injectivity give pieces covering a power of `c · d`.** -/
theorem ChartData.exists_pow_cover (T : ChartData G) (hn : 0 < n) (d : MvPolynomial (Fin (m + n)) ℤ)
    (hinj : ConormalInj G d) :
    ∃ (a K : ℕ) (P : Fin K → SquarePiece m n G) (u : Fin K → MvPolynomial (Fin (m + n)) ℤ) (N : ℕ),
      0 < N ∧ (N : MvPolynomial (Fin (m + n)) ℤ) * (T.c * d) ^ a - ∑ k, u k * (P k).h ∈ lspan G := by
  obtain ⟨K, P, u, -, -, h⟩ := T.exists_minor_cover hn d hinj
  set A := m * K + (n + G.length * (n + 1))
  set L := G.length
  obtain ⟨K', f, hf⟩ := exists_fin_enum (m := m) (n := n)
    (Finset.univ : Finset (ChartData.MinorIdx (m := m) (n := n) G))
  refine ⟨A + L, K', fun k => P (f k), fun k => T.c ^ L * d ^ A * u (f k), m.factorial ^ K,
    pow_pos (Nat.factorial_pos m) K, ?_⟩
  have e1 : ∑ k, T.c ^ L * d ^ A * u (f k) * (P (f k)).h =
      T.c ^ L * d ^ A * ∑ s, u s * (P s).h := by
    rw [Finset.mul_sum, ← hf (fun s => T.c ^ L * d ^ A * (u s * (P s).h))]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ((m.factorial ^ K : ℕ) : MvPolynomial (Fin (m + n)) ℤ) * (T.c * d) ^ (A + L) =
      T.c ^ L * d ^ A * (((m.factorial ^ K : ℕ) : MvPolynomial (Fin (m + n)) ℤ) * (T.c ^ A * d ^ L)) := by
    ring
  rw [e1, e2, ← mul_sub]
  exact Ideal.mul_mem_left _ _ h

/-- **Gluing along powers**: `C ∈ (e) + (G)` and, for each open, pieces covering `N eⱼᵃ`. -/
theorem exists_smoothCert_of_pow_mem {J : ℕ} (e : Fin J → MvPolynomial (Fin (m + n)) ℤ) (C : ℕ)
    (hC : 0 < C) (hmem : (C : MvPolynomial (Fin (m + n)) ℤ) ∈ Ideal.span (Set.range e) ⊔ lspan G)
    (hω : ∀ j, ∃ (a K : ℕ) (P : Fin K → SquarePiece m n G) (u : Fin K → MvPolynomial (Fin (m + n)) ℤ)
      (N : ℕ), 0 < N ∧ (N : MvPolynomial (Fin (m + n)) ℤ) * e j ^ a - ∑ k, u k * (P k).h ∈ lspan G) :
    Nonempty (SmoothCert m n G) := by
  obtain ⟨a, ha⟩ := fin_choice (P := fun j (a : ℕ) => ∃ (K : ℕ) (P : Fin K → SquarePiece m n G)
    (u : Fin K → MvPolynomial (Fin (m + n)) ℤ) (N : ℕ),
      0 < N ∧ (N : MvPolynomial (Fin (m + n)) ℤ) * e j ^ a - ∑ k, u k * (P k).h ∈ lspan G) hω
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨lam, hlam⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy
  set M := ∑ j, a j
  have haM : ∀ j, a j ≤ M + 1 := fun j =>
    (Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans (Nat.le_succ _)
  refine exists_smoothCert_of_cover e (fun j => e j ^ a j) (fun j => e j ^ (M + 1 - a j)) lam C M hC
    ?_ (fun j => ?_) ha
  · have h : (C : MvPolynomial (Fin (m + n)) ℤ) - ∑ j, lam j * e j = z := by
      rw [← hyz, ← hlam]
      simp only [smul_eq_mul, add_sub_cancel_left]
    rw [h]; exact hz
  · rw [← pow_add, Nat.sub_add_cancel (haM j), sub_self]
    exact zero_mem _

end BezoutCounterexample.Constructive
