import Mathlib
import BezoutCounterexample.Constructive.ChainLiftRetTransport

/-!
# Transport of chart data along polynomial substitutions (Task B, Rees layer S1)

Setting of `ChainLiftRetTransport`: a target presentation `G` (variables `Z`, `m + n`), a model
presentation `H` (variables `W`, `m' + n`), substitutions `φ : Z → ℤ[W]`, `ψ : W → ℤ[Z]` with
`d_W (g ∘ φ) ∈ (H)`, `ψ(H) ⊆ (G)` and `Z_v - ψ(φ_v) ∈ (G)`. Given model chart data `T_H` whose
coordinates are target polynomials pulled back by `φ` (`T_H.x i = xT i ∘ φ`), the target gets chart
data with coordinates `xT` and multiplier `ψ(d_W² c_H)` (`exists_chartData_transport`):

* `V_T = ψ(d_W²) · P₁ · ψ(V_H)` with `P₁ = (ψ(∂_u φ_v))` (the model derivations pushed forward);
* `B_T` from the round trip, the model splitting `B_H`, and the expressions of `ψ(h)` and
  `xT - ψ(xT ∘ φ)` in terms of `G`.

All identities are checked in the quotient `ℤ[Z]/(G)` (`ψ̄ = π ∘ ψ` kills `(H)`), where they are
matrix identities: `1 = P̄₁P̄₂ + μ̄J̄_G` (round trip, `P₂ = (∂_w ψ_u)`), `ψ̄(J_H)P̄₂ = ν̄J̄_G`,
`ψ̄(J_{x_H})P̄₂ = J̄_{xT} - κ̄J̄_G` (chain rule), and the model's (L), (D), (X).
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial Matrix

variable {m n m' : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ))
  (H : List (MvPolynomial (Fin (m' + n)) ℤ))
  (φ : Fin (m + n) → MvPolynomial (Fin (m' + n)) ℤ) (ψ : Fin (m' + n) → MvPolynomial (Fin (m + n)) ℤ)
  (dW : MvPolynomial (Fin (m' + n)) ℤ)

/-- `ψ̄ = π ∘ ψ : ℤ[W] → ℤ[Z]/(G)`. -/
noncomputable abbrev ψbar : MvPolynomial (Fin (m' + n)) ℤ →+* MvPolynomial (Fin (m + n)) ℤ ⧸ lspan G :=
  (π G).comp (aeval ψ : MvPolynomial (Fin (m' + n)) ℤ →ₐ[ℤ] _).toRingHom

lemma matCong_of_map {a b : Type*} {A A' : Matrix a b (MvPolynomial (Fin (m + n)) ℤ)}
    (h : A.map (π G) = A'.map (π G)) : MatCong (lspan G) A A' := fun i j => by
  have := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at this
  exact Ideal.Quotient.eq.1 this

lemma exists_coeffs {p : MvPolynomial (Fin (m + n)) ℤ} (hp : p ∈ lspan G) :
    ∃ c : Fin G.length → MvPolynomial (Fin (m + n)) ℤ, p = ∑ r, c r * G.get r := by
  rw [lspan_eq_span_range, Ideal.mem_span_range_iff_exists_fun] at hp
  obtain ⟨c, hc⟩ := hp
  exact ⟨c, hc.symm⟩

/-- The derivative of an element of `(G)`, in the quotient. -/
lemma pi_pderiv_of_eq {p : MvPolynomial (Fin (m + n)) ℤ} {c : Fin G.length → MvPolynomial (Fin (m + n)) ℤ}
    (hc : p = ∑ r, c r * G.get r) (w : Fin (m + n)) :
    π G (pderiv w p) = ∑ r, π G (c r) * π G (pderiv w (G.get r)) := by
  have h0 : ∀ r, π G (G.get r) = 0 := fun r =>
    Ideal.Quotient.eq_zero_iff_mem.2 (get_mem_lspan G r)
  rw [hc, map_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, h0, zero_mul,
    add_zero]

section Facts

variable {G H φ ψ dW}
variable (hφ : ∀ g ∈ G, dW * aeval φ g ∈ lspan H) (hψ : ∀ h ∈ H, aeval ψ h ∈ lspan G)
  (hround : ∀ v, X v - aeval ψ (φ v) ∈ lspan G)

include hψ in
lemma ψbar_eq_zero {h : MvPolynomial (Fin (m' + n)) ℤ} (hh : h ∈ lspan H) : ψbar G ψ h = 0 := by
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  have : (lspan H).map (aeval ψ : MvPolynomial (Fin (m' + n)) ℤ →ₐ[ℤ] _).toRingHom ≤ lspan G := by
    rw [Ideal.map_le_iff_le_comap, lspan, Ideal.span_le]
    intro h hh; exact hψ h hh
  exact this (Ideal.mem_map_of_mem _ hh)

include hround in
/-- Taylor of order 0 in the quotient: `π p = ψ̄ (p ∘ φ)`. -/
lemma pi_eq_ψbar (p : MvPolynomial (Fin (m + n)) ℤ) : π G p = ψbar G ψ (aeval φ p) := by
  have hJ : diffIdeal (fun v => (X v : MvPolynomial (Fin (m + n)) ℤ)) (fun v => aeval ψ (φ v)) ≤
      lspan G := by
    rw [diffIdeal, Ideal.span_le]; rintro _ ⟨v, rfl⟩; exact hround v
  have h := hJ (taylor0 (fun v => (X v : MvPolynomial (Fin (m + n)) ℤ)) (fun v => aeval ψ (φ v)) p)
  have hc : aeval ψ (aeval φ p) = aeval (fun v => aeval ψ (φ v)) p := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rw [aeval_X_self] at h
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hc]
  exact Ideal.Quotient.eq.2 h

/-- The model derivation `D_i p = Σ_u ∂_u p · V_{u,i}` preserves `(H)` when `∂H · V ≡ 0`. -/
lemma derivV_mem {V : Matrix (Fin (m' + n)) (Fin n) (MvPolynomial (Fin (m' + n)) ℤ)}
    (hD : MatCong (lspan H) (jacG H * V) 0) (i : Fin n) {p : MvPolynomial (Fin (m' + n)) ℤ}
    (hp : p ∈ lspan H) : ∑ u, pderiv u p * V u i ∈ lspan H := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := List.get_of_mem hx
    have := hD r i
    simpa [Matrix.mul_apply, jacG] using this
  | zero => simp
  | add x z _ _ hx hz =>
    simp only [map_add, add_mul, Finset.sum_add_distrib]; exact Ideal.add_mem _ hx hz
  | smul c x hxI hx =>
    have hd : ∀ u, pderiv u (c * x) * V u i = c * (pderiv u x * V u i) + x * (pderiv u c * V u i) :=
      fun u => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    rw [smul_eq_mul, Finset.sum_congr rfl (fun u _ => hd u), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hxI)

/-- `d_W² D_i (g ∘ φ) ∈ (H)` when `d_W (g ∘ φ) ∈ (H)`. -/
lemma dW_sq_derivV_mem {V : Matrix (Fin (m' + n)) (Fin n) (MvPolynomial (Fin (m' + n)) ℤ)}
    (hD : MatCong (lspan H) (jacG H * V) 0) (i : Fin n) {q : MvPolynomial (Fin (m' + n)) ℤ}
    (hq : dW * q ∈ lspan H) : dW ^ 2 * ∑ u, pderiv u q * V u i ∈ lspan H := by
  have h1 := Ideal.mul_mem_left _ dW (derivV_mem hD i hq)
  have h2 := Ideal.mul_mem_right (∑ u, pderiv u dW * V u i) _ hq
  have e : dW ^ 2 * ∑ u, pderiv u q * V u i =
      dW * ∑ u, pderiv u (dW * q) * V u i - dW * q * ∑ u, pderiv u dW * V u i := by
    have hd : ∀ u, pderiv u (dW * q) * V u i =
        dW * (pderiv u q * V u i) + q * (pderiv u dW * V u i) := fun u => by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    rw [Finset.sum_congr rfl (fun u _ => hd u), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    ring
  rw [e]; exact Ideal.sub_mem _ h1 h2

include hround in
/-- `J̄_p · P̄₁ = ψ̄(J_{p∘φ})` for target polynomials `p`. -/
lemma jac_mul_P1 {k : ℕ} (p : Fin k → MvPolynomial (Fin (m + n)) ℤ) (r : Fin k)
    (u : Fin (m' + n)) :
    ∑ v, π G (pderiv v (p r)) * ψbar G ψ (pderiv u (φ v)) = ψbar G ψ (pderiv u (aeval φ (p r))) := by
  rw [pderiv_aeval, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [pi_eq_ψbar hround, map_mul]


lemma map_smul_ringHom {a b R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R)
    (A : Matrix a b R) : (c • A).map f = f c • A.map f := by
  ext i j; simp

include hround in
/-- F1, entrywise: the derivative of the round trip. -/
lemma F1_entry {v : Fin (m + n)} {μ : Fin G.length → MvPolynomial (Fin (m + n)) ℤ}
    (hμ : X v - aeval ψ (φ v) = ∑ r, μ r * G.get r) (w : Fin (m + n)) :
    ∑ u, ψbar G ψ (pderiv u (φ v)) * π G (pderiv w (ψ u)) +
      ∑ r, π G (μ r) * π G (pderiv w (G.get r)) = if v = w then 1 else 0 := by
  have hd := pi_pderiv_of_eq G hμ w
  rw [map_sub, pderiv_X, pderiv_aeval, map_sub, map_sum] at hd
  simp only [map_mul] at hd
  rw [← hd, Pi.single_apply]
  have : ∀ u, ψbar G ψ (pderiv u (φ v)) = π G (aeval ψ (pderiv u (φ v))) := fun u => rfl
  simp only [this]
  split_ifs <;> simp

/-- F3, entrywise: the chain rule for `ψ(h)`. -/
lemma F3_entry {h : MvPolynomial (Fin (m' + n)) ℤ} {ν : Fin G.length → MvPolynomial (Fin (m + n)) ℤ}
    (hν : aeval ψ h = ∑ r, ν r * G.get r) (w : Fin (m + n)) :
    ∑ u, ψbar G ψ (pderiv u h) * π G (pderiv w (ψ u)) =
      ∑ r, π G (ν r) * π G (pderiv w (G.get r)) := by
  have hd := pi_pderiv_of_eq G hν w
  rw [pderiv_aeval, map_sum] at hd
  simp only [map_mul] at hd
  rw [← hd]; rfl

/-- F4, entrywise: the chain rule for `ψ(p ∘ φ)`. -/
lemma F4_entry {p : MvPolynomial (Fin (m + n)) ℤ} {κ : Fin G.length → MvPolynomial (Fin (m + n)) ℤ}
    (hκ : p - aeval ψ (aeval φ p) = ∑ r, κ r * G.get r) (w : Fin (m + n)) :
    ∑ u, ψbar G ψ (pderiv u (aeval φ p)) * π G (pderiv w (ψ u)) =
      π G (pderiv w p) - ∑ r, π G (κ r) * π G (pderiv w (G.get r)) := by
  have hd := pi_pderiv_of_eq G hκ w
  rw [map_sub, map_sub, pderiv_aeval, map_sum] at hd
  simp only [map_mul] at hd
  rw [← hd]
  have : ∀ u, ψbar G ψ (pderiv u (aeval φ p)) = π G (aeval ψ (pderiv u (aeval φ p))) :=
    fun u => rfl
  simp only [this]
  ring


lemma map_aeval_map (A : Matrix (Fin (m' + n)) (Fin n) (MvPolynomial (Fin (m' + n)) ℤ)) :
    (A.map (aeval ψ)).map (π G) = A.map (ψbar G ψ) := by ext; rfl

lemma map_aeval_map' {k : ℕ} (A : Matrix (Fin (m' + n)) (Fin k) (MvPolynomial (Fin (m' + n)) ℤ)) :
    (A.map (aeval ψ)).map (π G) = A.map (ψbar G ψ) := by ext; rfl

include hψ hround in
/-- **Transport of chart data** along polynomial substitutions. -/
theorem exists_chartData_transport
    (hφ : ∀ g ∈ G, dW * aeval φ g ∈ lspan H)
    (TH : ChartData H) (xT : Fin n → MvPolynomial (Fin (m + n)) ℤ)
    (hx : ∀ i, TH.x i = aeval φ (xT i)) :
    ∃ T : ChartData G, T.x = xT ∧ T.c = aeval ψ (dW ^ 2 * TH.c) ∧
      T.V = aeval ψ (dW ^ 2) • (Matrix.of (fun v u => aeval ψ (pderiv u (φ v))) *
        TH.V.map (aeval ψ)) := by
  obtain ⟨μ, hμ⟩ := fin_choice fun v : Fin (m + n) => exists_coeffs G (hround v)
  obtain ⟨ν, hν⟩ := fin_choice fun r' : Fin H.length => exists_coeffs G (hψ _ (List.get_mem H r'))
  have hκ' : ∀ i, xT i - aeval ψ (aeval φ (xT i)) ∈ lspan G := fun i =>
    Ideal.Quotient.eq.1 (pi_eq_ψbar (G := G) (φ := φ) hround (xT i))
  obtain ⟨κ, hκ⟩ := fin_choice fun i : Fin n => exists_coeffs G (hκ' i)
  set ψb := ψbar G ψ with hψb
  -- quotient matrices
  set P1q : Matrix (Fin (m + n)) (Fin (m' + n)) _ := Matrix.of fun v u => ψb (pderiv u (φ v))
    with hP1q
  set P2q : Matrix (Fin (m' + n)) (Fin (m + n)) _ := Matrix.of fun u w => π G (pderiv w (ψ u))
    with hP2q
  set JG := (jacG G).map (π G) with hJG
  set JX := (jacX xT).map (π G) with hJX
  set JH := (jacG H).map ψb with hJH
  set JXH := (jacX TH.x).map ψb with hJXH
  set μq := (Matrix.of μ).map (π G) with hμq
  set νq := (Matrix.of ν).map (π G) with hνq
  set κq := (Matrix.of κ).map (π G) with hκq
  set BHq := TH.B.map ψb with hBHq
  set VHq := TH.V.map ψb with hVHq
  have F1 : P1q * P2q + μq * JG = 1 := by
    refine Matrix.ext fun v w => ?_
    simp only [Matrix.add_apply, Matrix.mul_apply, hP1q, hP2q, hμq, hJG, Matrix.of_apply,
      Matrix.map_apply, jacG, Matrix.one_apply]
    exact F1_entry hround (hμ v) w
  have F2 : BHq * JH + VHq * JXH = ψb TH.c • 1 := by
    refine Matrix.ext fun u w => ?_
    have h := ψbar_eq_zero hψ (TH.hL u w)
    rw [map_sub, sub_eq_zero] at h
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply, map_add, map_sum, map_mul,
      Matrix.smul_apply, smul_eq_mul, hBHq, hJH, hVHq, hJXH] at h ⊢
    rw [h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp <;> rfl
  have F3 : JH * P2q = νq * JG := by
    refine Matrix.ext fun r' w => ?_
    simp only [Matrix.mul_apply, hJH, hP2q, hνq, hJG, Matrix.map_apply, Matrix.of_apply, jacG]
    exact F3_entry (hν r') w
  have F4 : JX = JXH * P2q + κq * JG := by
    refine Matrix.ext fun i w => ?_
    simp only [Matrix.add_apply, Matrix.mul_apply, hJXH, hP2q, hκq, hJG, hJX, Matrix.map_apply,
      Matrix.of_apply, jacG, jacX, hx]
    rw [F4_entry (hκ i) w]; ring
  have F5 : ∀ r i, ψb (dW ^ 2) * (JG * P1q * VHq) r i = 0 := by
    intro r i
    have hm := dW_sq_derivV_mem TH.hD i (hφ _ (List.get_mem G r))
    rw [← ψbar_eq_zero hψ hm]
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, hJG, hP1q, hVHq, jacG,
      map_mul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    exact jac_mul_P1 hround (fun r => G.get r) r u
  have F6 : JX * P1q = JXH := by
    refine Matrix.ext fun i u => ?_
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, hJX, hJXH, hP1q, jacX, hx]
    exact jac_mul_P1 hround xT i u
  have F7 : JXH * VHq = ψb TH.c • 1 := by
    refine Matrix.ext fun i i' => ?_
    have h := ψbar_eq_zero hψ (TH.hX i i')
    rw [map_sub, sub_eq_zero] at h
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, Matrix.smul_apply,
      smul_eq_mul, hJXH, hVHq] at h ⊢
    rw [h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp <;> rfl
  have key : P1q * (BHq * νq - VHq * κq) * JG + P1q * VHq * JX = ψb TH.c • (P1q * P2q) := by
    rw [F4]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
    rw [← F3]
    have F2' : BHq * (JH * P2q) + VHq * (JXH * P2q) = ψb TH.c • P2q := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, F2, Matrix.smul_mul,
        Matrix.one_mul]
    calc P1q * (BHq * (JH * P2q)) - P1q * (VHq * (κq * JG)) +
          (P1q * (VHq * (JXH * P2q)) + P1q * (VHq * (κq * JG)))
        = P1q * (BHq * (JH * P2q) + VHq * (JXH * P2q)) := by rw [Matrix.mul_add]; abel
      _ = ψb TH.c • (P1q * P2q) := by rw [F2', Matrix.mul_smul]
  refine ⟨{ x := xT
            B := aeval ψ (dW ^ 2) • (Matrix.of (fun v u => aeval ψ (pderiv u (φ v))) *
              (TH.B.map (aeval ψ) * Matrix.of ν - TH.V.map (aeval ψ) * Matrix.of κ)) +
              aeval ψ (dW ^ 2 * TH.c) • Matrix.of μ
            V := aeval ψ (dW ^ 2) • (Matrix.of (fun v u => aeval ψ (pderiv u (φ v))) *
              TH.V.map (aeval ψ))
            c := aeval ψ (dW ^ 2 * TH.c)
            hL := ?_, hD := ?_, hX := ?_ }, rfl, rfl, rfl⟩
  all_goals apply matCong_of_map
  · have hm : ∀ {k : ℕ} (A : Matrix (Fin (m' + n)) (Fin k) (MvPolynomial (Fin (m' + n)) ℤ)),
        (A.map (aeval ψ)).map (π G) = A.map ψb := fun A => by ext; rfl
    rw [Matrix.map_add _ (map_add (π G)), Matrix.map_mul, Matrix.map_mul, map_smul_ringHom,
      Matrix.map_add _ (map_add (π G)), map_smul_ringHom, map_smul_ringHom, Matrix.map_mul,
      Matrix.map_mul, Matrix.map_sub _ (map_sub (π G)), Matrix.map_mul, Matrix.map_mul, hm, hm,
      map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _)]
    change (ψb (dW ^ 2) • (P1q * (BHq * νq - VHq * κq)) + ψb (dW ^ 2 * TH.c) • μq) * JG +
      ψb (dW ^ 2) • (P1q * VHq) * JX = ψb (dW ^ 2 * TH.c) • 1
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, add_right_comm,
      ← smul_add, key, smul_smul, ← map_mul, ← smul_add, F1]
  · simp only [Matrix.map_mul, map_smul_ringHom, map_aeval_map, Matrix.map_zero _ (map_zero _)]
    refine Matrix.ext fun r i => ?_
    change (JG * (ψb (dW ^ 2) • (P1q * VHq))) r i = 0
    rw [Matrix.mul_smul, Matrix.smul_apply, ← Matrix.mul_assoc, smul_eq_mul, F5]
  · simp only [Matrix.map_mul, map_smul_ringHom, map_aeval_map,
      Matrix.map_one _ (map_zero _) (map_one _)]
    change JX * (ψb (dW ^ 2) • (P1q * VHq)) = ψb (dW ^ 2 * TH.c) • 1
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, F6, F7, smul_smul, map_mul]

end Facts

end BezoutCounterexample.Constructive
