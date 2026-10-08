import Mathlib
import BezoutCounterexample.Constructive.ChainLiftMinor
import BezoutCounterexample.Constructive.ChainLiftSquare
import BezoutCounterexample.Constructive.PresentedOps

/-!
# The Jacobian-minor cover (§2.2, milestone C1): square pieces

A presentation `G` (integer polynomials in `N = m + n` variables) with *chart data* modulo `(G)`
(`ChartData`): polynomials `x₁ … xₙ`, matrices `B`, `V` and a multiplier `c` with

* (L) `B ∂G + V ∂x ≡ c`,  (D) `∂G V ≡ 0`,  (X) `∂x V ≡ c`.

`c` is the denominator of a chart on `D(c)`: with `c = 1` these say that `V` lists the derivations
dual to `dx` and that `B` splits the conormal sequence on the right. The *conormal injectivity*
`ConormalInj G d` (`d f ∈ (G)²` whenever `f ∈ (G)` and `∂f ∈ (G)`) is the one input that is not
chart data: it is the left exactness of the conormal sequence on `D(d)` (smoothness).

* `conormal_retract`: (L), (D) and `ConormalInj` give `d (c gₗ - Σⱼ Eₗⱼ gⱼ) ∈ (G)²`, `E = ∂G B`.
* `exists_sep`: for `σ : Fin m → Fin r`, with `Δ = det E_σσ`, an `h'` with `h' ≡ (Δ² cⁿ⁺¹ d)ʳ`
  and `h' gₗ ∈ (G_σ)` for all `l` (the determinant trick on `(G)/(G_σ)`; no saturation).
* `exists_piece`: a `SquarePiece` with `F = (G_σ, x)` and `h ≡ Δ^{2r+1} w`, `w = c^{n+r(n+1)} dʳ`
  independent of `σ`.
* `exists_minor_cover`: pieces indexed by the `m`-subsets with `C · W ≡ Σ u_S h_S`, `C` a
  positive integer and `W` a power of `c` times `w`: the pieces cover `D(c d)`.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

open MvPolynomial Matrix

/-! ## Generalities -/

/-- Finite choice over a finite type with decidable equality (no axiom of choice). -/
theorem fintype_choice {J α : Type*} [Fintype J] [DecidableEq J] {P : J → α → Prop}
    (h : ∀ j, ∃ a, P j a) : ∃ f : J → α, ∀ j, P j (f j) := by
  refine Trunc.induction_on (Fintype.truncEquivFin J) fun e => ?_
  obtain ⟨f, hf⟩ := fin_choice (P := fun i a => P (e.symm i) a) fun i => h _
  exact ⟨fun j => f (e j), fun j => by simpa using hf (e j)⟩

section Cong

variable {R : Type*} [CommRing R] {a b : Type*}

/-- Entrywise congruence of matrices modulo an ideal. -/
def MatCong (I : Ideal R) (A A' : Matrix a b R) : Prop := ∀ i j, A i j - A' i j ∈ I

lemma MatCong.map_eq {I : Ideal R} {A A' : Matrix a b R} (h : MatCong I A A') :
    A.map (Ideal.Quotient.mk I) = A'.map (Ideal.Quotient.mk I) := by
  ext i j
  simp only [Matrix.map_apply]
  exact Ideal.Quotient.eq.2 (h i j)

lemma map_smul_one [Fintype a] [DecidableEq a] (I : Ideal R) (c : R) :
    ((c • 1 : Matrix a a R)).map (Ideal.Quotient.mk I) = Ideal.Quotient.mk I c • 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

end Cong

lemma lspan_eq_span_range {R : Type*} [CommRing R] (G : List R) :
    lspan G = Ideal.span (Set.range G.get) := by
  show Ideal.span _ = Ideal.span _
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_range]
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := List.get_of_mem h
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact List.get_mem G i

lemma get_mem_lspan {R : Type*} [CommRing R] (G : List R) (i : Fin G.length) :
    G.get i ∈ lspan G :=
  Ideal.subset_span (List.get_mem G i)

/-- Elements of `(G)²` are combinations `Σ qᵢ gᵢ` with `qᵢ ∈ (G)`. -/
lemma exists_of_mem_sq {R : Type*} [CommRing R] (G : List R) {z : R} (hz : z ∈ lspan G ^ 2) :
    ∃ q : Fin G.length → R, (∀ i, q i ∈ lspan G) ∧ z = ∑ i, q i * G.get i := by
  have h2 : lspan G ^ 2 = lspan G • Submodule.span R (Set.range G.get) := by
    rw [pow_two, Ideal.smul_eq_mul]
    congr 1
    exact lspan_eq_span_range G
  rw [h2, Submodule.mem_ideal_smul_span_iff_exists_sum] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  exact ⟨q, hq, by rw [Finsupp.sum_fintype _ _ (by simp)]; rfl⟩

/-! ## Chart data -/

section Chart

variable {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ))

/-- The quotient map. -/
noncomputable abbrev π (G : List (MvPolynomial (Fin (m + n)) ℤ)) :
    MvPolynomial (Fin (m + n)) ℤ →+* MvPolynomial (Fin (m + n)) ℤ ⧸ lspan G :=
  Ideal.Quotient.mk (lspan G)

/-- `∂G`. -/
noncomputable def jacG : Matrix (Fin G.length) (Fin (m + n)) (MvPolynomial (Fin (m + n)) ℤ) :=
  Matrix.of fun j k => pderiv k (G.get j)

/-- `∂x`. -/
noncomputable def jacX (x : Fin n → MvPolynomial (Fin (m + n)) ℤ) :
    Matrix (Fin n) (Fin (m + n)) (MvPolynomial (Fin (m + n)) ℤ) :=
  Matrix.of fun b k => pderiv k (x b)

/-- **Chart data** on `D(c)` modulo `(G)`. -/
structure ChartData where
  x : Fin n → MvPolynomial (Fin (m + n)) ℤ
  B : Matrix (Fin (m + n)) (Fin G.length) (MvPolynomial (Fin (m + n)) ℤ)
  V : Matrix (Fin (m + n)) (Fin n) (MvPolynomial (Fin (m + n)) ℤ)
  c : MvPolynomial (Fin (m + n)) ℤ
  hL : MatCong (lspan G) (B * jacG G + V * jacX x) (c • 1)
  hD : MatCong (lspan G) (jacG G * V) 0
  hX : MatCong (lspan G) (jacX x * V) (c • 1)

/-- **Conormal injectivity on `D(d)`**: `d f ∈ (G)²` for `f ∈ (G)` with all `∂ₖ f ∈ (G)`. -/
def ConormalInj (d : MvPolynomial (Fin (m + n)) ℤ) : Prop :=
  ∀ f ∈ lspan G, (∀ k, pderiv k f ∈ lspan G) → d * f ∈ lspan G ^ 2

variable {G} (T : ChartData G)

namespace ChartData


/-- `E = ∂G B`. -/
noncomputable def E : Matrix (Fin G.length) (Fin G.length) (MvPolynomial (Fin (m + n)) ℤ) :=
  jacG G * T.B

lemma hL' : T.B.map (π G) * (jacG G).map (π G) + T.V.map (π G) * (jacX T.x).map (π G) = π G T.c • 1 := by
  have := T.hL.map_eq
  rwa [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, map_smul_one] at this

lemma hD' : (jacG G).map (π G) * T.V.map (π G) = 0 := by
  have := T.hD.map_eq
  rwa [Matrix.map_mul, Matrix.map_zero _ (map_zero _)] at this

lemma hX' : (jacX T.x).map (π G) * T.V.map (π G) = π G T.c • 1 := by
  have := T.hX.map_eq
  rwa [Matrix.map_mul, map_smul_one] at this

lemma E_map : T.E.map (π G) = (jacG G).map (π G) * T.B.map (π G) := Matrix.map_mul

/-- (L) and (D) make `c gₗ - Σⱼ Eₗⱼ gⱼ` a member of `(G)` with all derivatives in `(G)`. -/
lemma pderiv_retract_mem (l : Fin G.length) (k : Fin (m + n)) :
    pderiv k (T.c * G.get l - ∑ j, T.E l j * G.get j) ∈ lspan G := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hg : ∀ j, π G (G.get j) = 0 := fun j => Ideal.Quotient.eq_zero_iff_mem.2 (get_mem_lspan G j)
  simp only [map_sub, map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul, hg, mul_zero,
    zero_add]
  -- `c ∂G - E ∂G = ∂G (c - B ∂G) = ∂G V ∂x ≡ 0`
  have hE : T.E.map (π G) * (jacG G).map (π G) = π G T.c • (jacG G).map (π G) := by
    have hBD : T.B.map (π G) * (jacG G).map (π G) = π G T.c • 1 - T.V.map (π G) * (jacX T.x).map (π G) :=
      eq_sub_of_add_eq T.hL'
    rw [E_map, Matrix.mul_assoc, hBD, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, T.hD',
      Matrix.zero_mul, sub_zero]
  have := congrFun (congrFun hE l) k
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
  simp only [jacG, Matrix.of_apply] at this ⊢
  rw [← this]
  simp only [zero_mul, add_zero]
  exact sub_self _

/-- **The conormal retraction**: `d (c gₗ - Σⱼ Eₗⱼ gⱼ) ∈ (G)²`. -/
theorem retract (d : MvPolynomial (Fin (m + n)) ℤ) (hinj : ConormalInj G d) (l : Fin G.length) :
    d * (T.c * G.get l - ∑ j, T.E l j * G.get j) ∈ lspan G ^ 2 := by
  refine hinj _ ?_ (T.pderiv_retract_mem l)
  refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (get_mem_lspan G l)) ?_
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (get_mem_lspan G j)

end ChartData

end Chart

/-! ## Maps commute with the constructions -/

section Maps

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {m n r : ℕ}
  (DG : Matrix (Fin r) (Fin (m + n)) R) (DX : Matrix (Fin n) (Fin (m + n)) R)
  (B : Matrix (Fin (m + n)) (Fin r) R) (V : Matrix (Fin (m + n)) (Fin n) R) (σ : Fin m → Fin r)

lemma map_sqRows : (sqRows DG DX σ).map f = sqRows (DG.map f) (DX.map f) σ := by
  ext i k
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp

lemma map_sqCols : (sqCols B V σ).map f = sqCols (B.map f) (V.map f) σ := by
  ext k i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp

lemma map_det_E : f ((DG * B).submatrix σ σ).det = ((DG.map f * B.map f).submatrix σ σ).det := by
  rw [RingHom.map_det, ← Matrix.map_mul]; rfl

lemma map_sepCoeff (l : Fin r) (a : Fin m) :
    f (sepCoeff DG B σ l a) = sepCoeff (DG.map f) (B.map f) σ l a := by
  rw [sepCoeff, RingHom.map_vecMul]
  have h := RingHom.map_adjugate f ((DG * B).submatrix σ σ)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [h, sepCoeff, ← Matrix.submatrix_map, ← Matrix.map_mul]
  congr 2

end Maps

/-! ## Separation: the determinant trick -/

section Sep

/-- **Determinant trick.** If `ρ gₗ ≡ Σᵢ qₗᵢ gᵢ` modulo `J` with all `qₗᵢ ∈ I`, then
`h' = det (ρ - q)` has `h' gₗ ∈ J` and `h' ≡ ρʳ` modulo `I`. -/
theorem det_trick {R : Type*} [CommRing R] {r : ℕ} (I J : Ideal R) (g : Fin r → R) (ρ : R)
    (q : Fin r → Fin r → R) (hq : ∀ i j, q i j ∈ I) (h : ∀ l, ρ * g l - ∑ i, q l i * g i ∈ J) :
    (∀ l, (ρ • (1 : Matrix (Fin r) (Fin r) R) - Matrix.of q).det * g l ∈ J) ∧
      (ρ • (1 : Matrix (Fin r) (Fin r) R) - Matrix.of q).det - ρ ^ r ∈ I := by
  set A := ρ • (1 : Matrix (Fin r) (Fin r) R) - Matrix.of q
  constructor
  · intro l
    set πJ := Ideal.Quotient.mk J
    have hA : (A.map πJ).mulVec (πJ ∘ g) = 0 := by
      ext l'
      have := Ideal.Quotient.eq_zero_iff_mem.2 (h l')
      simp only [map_sub, map_mul, map_sum] at this
      rw [Pi.zero_apply, ← this]
      simp [A, πJ, Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply, sub_mul,
        Finset.sum_sub_distrib, ite_mul, apply_ite (Ideal.Quotient.mk J)]
    have h2 := congrArg (fun v => (A.map πJ).adjugate.mulVec v) hA
    simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h2
    have := congrFun h2 l
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply] at this
    have e : πJ A.det = (A.map πJ).det := RingHom.map_det _ _
    rw [← e, ← map_mul] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  · rw [← Ideal.Quotient.eq]
    rw [show Ideal.Quotient.mk I A.det = (A.map (Ideal.Quotient.mk I)).det from
      RingHom.map_det _ _, map_pow]
    have : A.map (Ideal.Quotient.mk I) = Ideal.Quotient.mk I ρ • 1 := by
      ext i j
      have := Ideal.Quotient.eq_zero_iff_mem.2 (hq i j)
      by_cases hij : i = j
      · subst hij; simp [A, Matrix.sub_apply, this]
      · simp [A, Matrix.sub_apply, Matrix.one_apply, hij, this]
    rw [this, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

end Sep

/-! ## The pieces of one chart -/

section Pieces

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)} (T : ChartData G)
  (σ : Fin m → Fin G.length)

/-- The computation behind `ChartData.sep_mem`, in any commutative ring. -/
theorem sep_algebra {R : Type*} [CommRing R] (I : Ideal R) {r m : ℕ} {n : ℕ} (σ : Fin m → Fin r)
    (l : Fin r) (Δ c d : R) (x : Fin m → R) (E : Fin r → Fin r → R) (g : Fin r → R)
    (hg : ∀ i, g i ∈ I) (hRt : ∀ j, d * (c * g j - ∑ i, E j i * g i) ∈ I ^ 2)
    (hK : ∀ i, Δ * c ^ n * (∑ a, x a * E (σ a) i - Δ * E l i) ∈ I) :
    Δ * c ^ n * Δ * d * c * g l - ∑ a, (Δ * c ^ n * x a * d * c) * g (σ a) ∈ I ^ 2 := by
  have hK' : ∑ i, (Δ * c ^ n * (∑ a, x a * E (σ a) i - Δ * E l i)) * g i =
      Δ * c ^ n * ∑ a, x a * ∑ i, E (σ a) i * g i - Δ * c ^ n * Δ * ∑ i, E l i * g i := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine congrArg₂ _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring)
      (Finset.sum_congr rfl fun i _ => by ring)
  have hR : ∑ a, x a * (d * (c * g (σ a) - ∑ i, E (σ a) i * g i)) =
      d * c * ∑ a, x a * g (σ a) - d * ∑ a, x a * ∑ i, E (σ a) i * g i := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
  have hL : ∑ a, (Δ * c ^ n * x a * d * c) * g (σ a) = Δ * c ^ n * d * c * ∑ a, x a * g (σ a) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  have key : Δ * c ^ n * Δ * d * c * g l - ∑ a, (Δ * c ^ n * x a * d * c) * g (σ a) =
      Δ * c ^ n * Δ * (d * (c * g l - ∑ i, E l i * g i)) -
        d * ∑ i, (Δ * c ^ n * (∑ a, x a * E (σ a) i - Δ * E l i)) * g i -
        Δ * c ^ n * ∑ a, x a * (d * (c * g (σ a) - ∑ i, E (σ a) i * g i)) := by
    rw [hK', hR, hL]; ring
  rw [key]
  refine Ideal.sub_mem _ (Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (hRt l)) ?_) ?_
  · refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun i _ => ?_)
    rw [pow_two]
    exact Ideal.mul_mem_mul (hK i) (hg i)
  · exact Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hRt _))

namespace ChartData

/-- `Δ = det E_σσ`. -/
noncomputable def Δ : MvPolynomial (Fin (m + n)) ℤ := (T.E.submatrix σ σ).det

/-- `x = E_{l,σ} adj E_σσ`. -/
noncomputable def xs (l : Fin G.length) (a : Fin m) : MvPolynomial (Fin (m + n)) ℤ :=
  sepCoeff (jacG G) T.B σ l a

/-- `ρ = Δ² cⁿ⁺¹ d`. -/
noncomputable def ρ (d : MvPolynomial (Fin (m + n)) ℤ) : MvPolynomial (Fin (m + n)) ℤ :=
  T.Δ σ * T.c ^ n * T.Δ σ * d * T.c

lemma E_apply_map (a b : Fin G.length) :
    π G (T.E a b) = ((jacG G).map (π G) * T.B.map (π G)) a b := by
  rw [← T.E_map]; rfl

/-- `Δ cⁿ (Σ_a x_a E_{σ a, i} - Δ E_{l i}) ∈ (G)`. -/
lemma K_mem (l i : Fin G.length) :
    T.Δ σ * T.c ^ n * (∑ a, T.xs σ l a * T.E (σ a) i - T.Δ σ * T.E l i) ∈ lspan G := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h := congrFun (sep_rowE ((jacG G).map (π G)) ((jacX T.x).map (π G)) (T.B.map (π G))
    (T.V.map (π G)) (π G T.c) σ T.hD' T.hX' l) i
  have hΔ : π G (T.Δ σ) = (((jacG G).map (π G) * T.B.map (π G)).submatrix σ σ).det := by
    rw [Δ, E]; exact map_det_E _ _ _ _
  have hx : ∀ a, π G (T.xs σ l a) = sepCoeff ((jacG G).map (π G)) (T.B.map (π G)) σ l a :=
    fun a => map_sepCoeff _ _ _ _ _ _
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Matrix.vecMul, dotProduct,
    Matrix.submatrix_apply, id, Pi.zero_apply] at h
  simp only [map_mul, map_sub, map_sum, map_pow, hΔ, hx, E_apply_map]
  exact h

/-- **Separation modulo `(G)²`**: `ρ gₗ ≡ Σ_a Δ cⁿ x_a d c g_{σ a}` modulo `(G)²`. -/
theorem sep_mem (d : MvPolynomial (Fin (m + n)) ℤ) (hinj : ConormalInj G d) (l : Fin G.length) :
    T.ρ σ d * G.get l - ∑ a, (T.Δ σ * T.c ^ n * T.xs σ l a * d * T.c) * G.get (σ a) ∈
      lspan G ^ 2 := by
  have hRt : ∀ j, d * (T.c * G.get j - ∑ i, T.E j i * G.get i) ∈ lspan G ^ 2 :=
    fun j => T.retract d hinj j
  exact sep_algebra (lspan G) σ l (T.Δ σ) T.c d (T.xs σ l) T.E G.get (get_mem_lspan G) hRt
    (T.K_mem σ l)

/-- The ideal `(G_σ)`. -/
noncomputable abbrev Jσ : Ideal (MvPolynomial (Fin (m + n)) ℤ) := lspan (List.ofFn fun a => G.get (σ a))

lemma get_mem_Jσ (a : Fin m) : G.get (σ a) ∈ Jσ σ :=
  Ideal.subset_span (List.mem_ofFn.2 ⟨a, rfl⟩)

/-- **The separating element** `h' ≡ ρʳ` with `h' G ⊆ (G_σ)`. -/
theorem exists_sep (d : MvPolynomial (Fin (m + n)) ℤ) (hinj : ConormalInj G d) :
    ∃ h' : MvPolynomial (Fin (m + n)) ℤ, (∀ l, h' * G.get l ∈ Jσ σ) ∧
      h' - T.ρ σ d ^ G.length ∈ lspan G := by
  obtain ⟨q, hq⟩ := fin_choice fun l => exists_of_mem_sq G (T.sep_mem σ d hinj l)
  obtain ⟨h1, h2⟩ := det_trick (lspan G) (Jσ σ) G.get (T.ρ σ d) q (fun l i => (hq l).1 i)
    fun l => by
      rw [← (hq l).2, sub_sub_cancel]
      exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (get_mem_Jσ σ a)
  exact ⟨_, h1, h2⟩

/-- Certificate (i) modulo `(G)`: `det [∂G_σ; ∂x] · det [B_σ | V] ≡ Δ cⁿ`. -/
lemma det_sq_mem :
    (sqRows (jacG G) (jacX T.x) σ).det * (sqCols T.B T.V σ).det - T.Δ σ * T.c ^ n ∈ lspan G := by
  rw [← Ideal.Quotient.eq]
  have h1 : π G (sqRows (jacG G) (jacX T.x) σ).det =
      (sqRows ((jacG G).map (π G)) ((jacX T.x).map (π G)) σ).det := by
    rw [RingHom.map_det]; exact congrArg Matrix.det (map_sqRows _ _ _ _)
  have h2 : π G (sqCols T.B T.V σ).det = (sqCols (T.B.map (π G)) (T.V.map (π G)) σ).det := by
    rw [RingHom.map_det]; exact congrArg Matrix.det (map_sqCols _ _ _ _)
  have hΔ : π G (T.Δ σ) = (((jacG G).map (π G) * T.B.map (π G)).submatrix σ σ).det := by
    rw [Δ, E]; exact map_det_E _ _ _ _
  rw [map_mul, map_mul, map_pow, h1, h2, hΔ]
  exact det_sq _ _ _ _ _ σ T.hD' T.hX'

/-- **A square piece of the chart**: `F = (G_σ, x)`, `h ≡ Δ^{2r+1} w` with
`w = c^{n + r(n+1)} dʳ`, `r` the number of relations. -/
theorem exists_piece (hn : 0 < n) (d : MvPolynomial (Fin (m + n)) ℤ) (hinj : ConormalInj G d) :
    ∃ S : SquarePiece m n G, S.F = Fin.addCases (fun a => G.get (σ a)) T.x ∧
      S.h - T.Δ σ ^ (2 * G.length + 1) * (T.c ^ (n + G.length * (n + 1)) * d ^ G.length) ∈
        lspan G := by
  obtain ⟨h', hh'1, hh'2⟩ := T.exists_sep σ d hinj
  set F : Fin (m + n) → MvPolynomial (Fin (m + n)) ℤ := Fin.addCases (fun a => G.get (σ a)) T.x
  have hjac : jacPoly F = sqRows (jacG G) (jacX T.x) σ := by
    ext i k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [jacPoly, jacG, jacX, F]
  have hJ : List.ofFn (fun i : Fin m => F (Fin.castAdd n i)) = List.ofFn fun a => G.get (σ a) := by
    simp [F]
  refine ⟨{
    F := F
    hn := hn
    eqmem := fun i => by simpa [F] using get_mem_lspan G (σ i)
    h := T.Δ σ * T.c ^ n * h'
    e := 1
    f := 1
    U := (sqCols T.B T.V σ).det * h'
    detc := ?_
    genc := ?_ }, rfl, ?_⟩
  · rw [hjac, pow_one]
    have := Ideal.mul_mem_right h' _ (T.det_sq_mem σ)
    convert this using 1; ring
  · intro g hg
    obtain ⟨l, rfl⟩ := List.get_of_mem hg
    rw [hJ, pow_one, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hh'1 l)
  · have := Ideal.mul_mem_left (lspan G) (T.Δ σ * T.c ^ n) hh'2
    convert this using 1
    simp only [ρ]; ring

/-- The `m`-subsets of the relations. -/
abbrev MinorIdx (G : List (MvPolynomial (Fin (m + n)) ℤ)) : Type :=
  ((Finset.univ : Finset (Fin G.length)).powersetCard m : Finset (Finset (Fin G.length)))

lemma MinorIdx.card (s : MinorIdx (m := m) (n := n) G) : s.1.card = m :=
  (Finset.mem_powersetCard.1 s.2).2

/-- The increasing enumeration of an `m`-subset. -/
noncomputable def subEnum (s : MinorIdx (m := m) (n := n) G) : Fin m → Fin G.length :=
  s.1.orderEmbOfFin s.card

/-- **The minors cover modulo `(G)`**: `m! Σ_S Δ_S ≡ m! cᵐ`. -/
lemma sum_Δ_mem :
    (m.factorial : MvPolynomial (Fin (m + n)) ℤ) * ∑ s : MinorIdx (m := m) (n := n) G, T.Δ (subEnum s) -
      (m.factorial : MvPolynomial (Fin (m + n)) ℤ) * T.c ^ m ∈ lspan G := by
  rw [← Ideal.Quotient.eq]
  set E' := (jacG G).map (π G) * T.B.map (π G)
  have hsq : E' * E' = π G T.c • E' :=
    sq_E_sq ((jacG G).map (π G)) ((jacX T.x).map (π G)) _ _ _ T.hL' T.hD'
  have htr : E'.trace = (m : _) * π G T.c :=
    sq_E_trace ((jacG G).map (π G)) ((jacX T.x).map (π G)) _ _ _ T.hL' T.hX'
  have h := factorial_mul_sum_minors_of_sq E' (π G T.c) m hsq htr
  rw [map_mul, map_mul, map_sum, map_pow, map_natCast, ← h]
  congr 1
  rw [← Finset.sum_coe_sort (Finset.powersetCard m (Finset.univ : Finset (Fin G.length)))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Δ, E, map_det_E]
  rw [← Matrix.det_submatrix_equiv_self (s.1.orderIsoOfFin s.card).toEquiv]
  rfl

/-- **The square pieces of one chart cover `D(c d)`.** -/
theorem exists_minor_cover (hn : 0 < n) (d : MvPolynomial (Fin (m + n)) ℤ)
    (hinj : ConormalInj G d) :
    ∃ (K : ℕ) (P : MinorIdx (m := m) (n := n) G → SquarePiece m n G)
      (u : MinorIdx (m := m) (n := n) G → MvPolynomial (Fin (m + n)) ℤ),
      (∀ s, (P s).F = Fin.addCases (fun a => G.get ((subEnum s) a)) T.x) ∧
      (∀ s, (P s).h - T.Δ (subEnum s) ^ (2 * G.length + 1) *
        (T.c ^ (n + G.length * (n + 1)) * d ^ G.length) ∈ lspan G) ∧
      ((m.factorial ^ K : ℕ) : MvPolynomial (Fin (m + n)) ℤ) *
          (T.c ^ (m * K + (n + G.length * (n + 1))) * d ^ G.length) -
        ∑ s, u s * (P s).h ∈ lspan G := by
  obtain ⟨P, hP⟩ := fintype_choice fun s : MinorIdx (m := m) (n := n) G => T.exists_piece (subEnum s) hn d hinj
  set r := G.length
  set w := T.c ^ (n + r * (n + 1)) * d ^ r
  set f : MinorIdx (m := m) (n := n) G → MvPolynomial (Fin (m + n)) ℤ :=
    fun s => (m.factorial : MvPolynomial (Fin (m + n)) ℤ) * T.Δ (subEnum s)
  set K := (Finset.univ : Finset (MinorIdx (m := m) (n := n) G)).card * (2 * r) + 1
  have hpow := Ideal.sum_pow_mem_span_pow (Finset.univ : Finset (MinorIdx (m := m) (n := n) G)) f (2 * r)
  rw [Finset.coe_univ, Set.image_univ, Ideal.mem_span_range_iff_exists_fun] at hpow
  obtain ⟨a, ha⟩ := hpow
  refine ⟨K, P, fun s => a s * (m.factorial : MvPolynomial (Fin (m + n)) ℤ) ^ (2 * r + 1),
    fun s => (hP s).1, fun s => (hP s).2, ?_⟩
  -- `(m! cᵐ)^K w ≡ (Σ f)^K w = Σ aₛ fₛ^{2r+1} w ≡ Σ aₛ m!^{2r+1} hₛ`
  have h1 : ((m.factorial : MvPolynomial (Fin (m + n)) ℤ) * T.c ^ m) ^ K * w -
      (∑ s, f s) ^ K * w ∈ lspan G := by
    rw [← sub_mul]
    refine Ideal.mul_mem_right _ _ ?_
    have := T.sum_Δ_mem
    rw [← Finset.mul_sum] at *
    rw [← Ideal.Quotient.eq] at this ⊢
    rw [map_pow, map_pow, this]
  have h2 : (∑ s, f s) ^ K * w - ∑ s, a s * (m.factorial : MvPolynomial (Fin (m + n)) ℤ) ^
      (2 * r + 1) * (P s).h ∈ lspan G := by
    rw [← ha, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun s _ => ?_
    have := Ideal.mul_mem_left (lspan G)
      (a s * (m.factorial : MvPolynomial (Fin (m + n)) ℤ) ^ (2 * r + 1)) (hP s).2
    have e : a s * f s ^ (2 * r + 1) * w -
        a s * (m.factorial : MvPolynomial (Fin (m + n)) ℤ) ^ (2 * r + 1) * (P s).h =
        -(a s * (m.factorial : MvPolynomial (Fin (m + n)) ℤ) ^ (2 * r + 1) *
          ((P s).h - T.Δ (subEnum s) ^ (2 * r + 1) * w)) := by
      simp only [f]; ring
    rw [e]
    exact (Ideal.neg_mem_iff _).2 this
  have h3 := Ideal.add_mem _ h1 h2
  rw [sub_add_sub_cancel] at h3
  convert h3 using 2
  simp only [w]; push_cast; ring

end ChartData

end Pieces


end BezoutCounterexample.Constructive
