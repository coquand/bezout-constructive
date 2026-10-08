import Mathlib
import BezoutCounterexample.Constructive.ChainLiftSquare
import BezoutCounterexample.Constructive.ChainLiftChart
import BezoutCounterexample.Constructive.ChainLift
import BezoutCounterexample.Constructive.ChainLiftNuGe

/-!
# Certified push-off data (§2.2–2.3, algebraic input)

`CertPush m n G`: everything the push-off needs, as polynomial certificates modulo `(G)`
(ideal membership, decidable by Gröbner and checkable):

* the filtration generators `g i` with even exponents `E i`, `E i d i = D₂`;
* certified square pieces (`SquarePiece`), with head coordinates `hd p` (at least two: `k ≥ 2`)
  and weights `w p`;
* for each piece and head coordinate a pure-power identity
  `h^s · a^{a} ≡ Σ_γ c_γ g^γ` (`lid`), with `Σ γ d ≥ a w`, `γ ≠ 0`: input to
  `nu_lo_of_identity_ge` (the Rees algebra gives `≥`, the surplus powers of `T⁻¹` drop out);
* for each piece and generator the weighted-monomial identity
  `h^s · gᵢ ≡ Σ_α b_α x_head^α`, `w · α ≥ dᵢ` (`hid`): input to `nu_hi_of_identity`;
* a partition of unity `C ≡ Σᵢ bᵢ gᵢ + Σ_p c_p h_p` with a positive integer `C` (`cid`; over `ℤ`
  the minor cover only gives a multiple of `1`), linear in the `gᵢ` (a partition
  `1 ≡ b ν + …` is in general not certifiable, `ν` has complex zeros off `V(g)`); at a real
  point some `|gᵢ| ≥ κ` (then `ν ≥ κ^{Eᵢ}`) or some `|h_p| ≥ κ` (`cover_of_identity`).

`CertPush.pushData`: on every box, a `PushData` for the real points of `G` and
`ν = Σ gᵢ^{Eᵢ}`. All constants are explicit, from `poly_bdd_lip`, `exists_pos_mul_le` and the
primitives `exists_inv_pos`, `cotrans`.
-/

set_option linter.unusedSectionVars false

namespace BezoutCounterexample.Constructive

open MvPolynomial

/-! ## Evaluation of congruences -/

section Eval
variable {N : ℕ}

/-- Evaluation as a ring hom. -/
noncomputable abbrev evalHom (x : Fin N → ℝ) : MvPolynomial (Fin N) ℤ →+* ℝ :=
  eval₂Hom (Int.castRingHom ℝ) x

lemma evalR_eq_evalHom (x : Fin N → ℝ) (P : MvPolynomial (Fin N) ℤ) :
    evalR x P = evalHom x P := rfl

/-- Congruences modulo `(G)` hold at real points. -/
lemma evalR_eq_of_sub_mem {G : List (MvPolynomial (Fin N) ℤ)} {x : Fin N → ℝ} (hx : PtG G x)
    {P Q : MvPolynomial (Fin N) ℤ} (h : P - Q ∈ lspan G) : evalHom x P = evalHom x Q := by
  have := evalR_eq_zero_of_mem hx h
  rw [evalR_eq_evalHom, map_sub] at this
  linarith

end Eval

/-- Uniform constants for a finite family: two lower bounds (`R`, `S`) and two upper bounds
(`K`, `L`). -/
theorem exists_uniform4 {ι : Type*} [DecidableEq ι] (Q : ι → ℝ → ℝ → ℝ → ℝ → Prop)
    (hmono : ∀ i R K S L R' K' S' L', Q i R K S L → 0 < R' → R' ≤ R → K ≤ K' → 0 < S' → S' ≤ S →
      L ≤ L' → Q i R' K' S' L')
    (h : ∀ i, ∃ R K S L, 0 < R ∧ 0 ≤ K ∧ 0 < S ∧ 0 ≤ L ∧ Q i R K S L) :
    ∀ s : Finset ι, ∃ R K S L, 0 < R ∧ 0 ≤ K ∧ 0 < S ∧ 0 ≤ L ∧ ∀ i ∈ s, Q i R K S L := by
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1, 0, 1, 0, one_pos, le_rfl, one_pos, le_rfl, fun i hi => absurd hi
      (Finset.notMem_empty i)⟩
  | insert a s _ ih =>
    obtain ⟨R, K, S, L, hR, hK, hS, hL, hs⟩ := ih
    obtain ⟨Ra, Ka, Sa, La, hRa, hKa, hSa, hLa, ha⟩ := h a
    obtain ⟨R', hR', h1, h2⟩ := exists_pos_mul_le₂ hR hRa 1 1
    obtain ⟨S', hS', h3, h4⟩ := exists_pos_mul_le₂ hS hSa 1 1
    rw [one_mul] at h1 h2 h3 h4
    refine ⟨R', K + Ka, S', L + La, hR', by positivity, hS', by positivity, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hmono _ _ _ _ _ _ _ _ _ ha hR' h2 (by linarith) hS' h4 (by linarith)
    · exact hmono _ _ _ _ _ _ _ _ _ (hs i hi) hR' h1 (by linarith) hS' h3 (by linarith)

/-- **Certified push-off data.** -/
structure CertPush (m n : ℕ) (G : List (MvPolynomial (Fin (m + n)) ℤ)) where
  ι : Type
  [fι : Fintype ι]
  [dι : DecidableEq ι]
  g : ι → MvPolynomial (Fin (m + n)) ℤ
  d : ι → ℕ
  E : ι → ℕ
  D₂ : ℕ
  hD : D₂ ≠ 0
  hEd : ∀ i, E i * d i = D₂
  hE : ∀ i, Even (E i)
  J : Type
  [fJ : Fintype J]
  [dJ : DecidableEq J]
  piece : J → SquarePiece m n G
  k : ℕ
  hk : 2 ≤ k
  hd : J → Fin k → Fin n
  hd_inj : ∀ p, Function.Injective (hd p)
  w : J → Fin k → ℕ
  hw : ∀ p q, w p q ≠ 0
  la : J → Fin k → ℕ
  ls : J → Fin k → ℕ
  lΓ : J → Fin k → Finset (ι → ℕ)
  lc : J → Fin k → (ι → ℕ) → MvPolynomial (Fin (m + n)) ℤ
  lhom : ∀ p q, ∀ γ ∈ lΓ p q, la p q * w p q ≤ ∑ j, γ j * d j
  lne : ∀ p q, ∀ γ ∈ lΓ p q, ∑ j, γ j ≠ 0
  lid : ∀ p q, (piece p).h ^ ls p q * (piece p).F (Fin.natAdd m (hd p q)) ^ la p q -
    ∑ γ ∈ lΓ p q, lc p q γ * ∏ j, g j ^ γ j ∈ lspan G
  hs : J → ι → ℕ
  hΓ : J → ι → Finset (Fin k → ℕ)
  hb : J → ι → (Fin k → ℕ) → MvPolynomial (Fin (m + n)) ℤ
  hdeg : ∀ p i, ∀ α ∈ hΓ p i, d i ≤ ∑ q, w p q * α q
  hid : ∀ p i, (piece p).h ^ hs p i * g i -
    ∑ α ∈ hΓ p i, hb p i α * ∏ q, (piece p).F (Fin.natAdd m (hd p q)) ^ α q ∈ lspan G
  cb : ι → MvPolynomial (Fin (m + n)) ℤ
  ca : J → MvPolynomial (Fin (m + n)) ℤ
  C0 : ℕ
  hC0 : 0 < C0
  cid : (C0 : MvPolynomial (Fin (m + n)) ℤ) - (∑ i, cb i * g i + ∑ p, ca p * (piece p).h) ∈ lspan G

attribute [instance] CertPush.fι CertPush.dι CertPush.fJ CertPush.dJ

namespace CertPush

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)} (T : CertPush m n G)

/-- `ν = Σ gᵢ^{Eᵢ}` at real points. -/
noncomputable def nu (x : Fin (m + n) → ℝ) : ℝ := ∑ i, evalR x (T.g i) ^ T.E i

lemma nu_nonneg (x : Fin (m + n) → ℝ) : 0 ≤ T.nu x :=
  Finset.sum_nonneg fun i _ => (T.hE i).pow_nonneg _

/-- The pure-power identity at a real point where `h t = 1`. -/
lemma lid_real {x : Fin (m + n) → ℝ} (hx : PtG G x) (p : T.J) (q : Fin T.k) {t : ℝ}
    (ht : evalR x (T.piece p).h * t = 1) :
    evalR x ((T.piece p).F (Fin.natAdd m (T.hd p q))) ^ T.la p q =
      ∑ γ ∈ T.lΓ p q, (evalR x (T.lc p q γ) * t ^ T.ls p q) *
        ∏ j, evalR x (T.g j) ^ γ j := by
  have h := evalR_eq_of_sub_mem hx (T.lid p q)
  simp only [map_mul, map_pow, map_sum, map_prod] at h
  simp only [← evalR_eq_evalHom] at h
  set A := evalR x ((T.piece p).F (Fin.natAdd m (T.hd p q))) ^ T.la p q
  calc A = (evalR x (T.piece p).h * t) ^ T.ls p q * A := by rw [ht, one_pow, one_mul]
    _ = t ^ T.ls p q * (evalR x (T.piece p).h ^ T.ls p q * A) := by ring
    _ = _ := by
      rw [h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun γ _ => by ring

/-- The weighted-monomial identity at a real point where `h t = 1`. -/
lemma hid_real {x : Fin (m + n) → ℝ} (hx : PtG G x) (p : T.J) (i : T.ι) {t : ℝ}
    (ht : evalR x (T.piece p).h * t = 1) :
    evalR x (T.g i) = ∑ α ∈ T.hΓ p i, (evalR x (T.hb p i α) * t ^ T.hs p i) *
      ∏ q, evalR x ((T.piece p).F (Fin.natAdd m (T.hd p q))) ^ α q := by
  have h := evalR_eq_of_sub_mem hx (T.hid p i)
  simp only [map_mul, map_pow, map_sum, map_prod] at h
  simp only [← evalR_eq_evalHom] at h
  calc evalR x (T.g i) = (evalR x (T.piece p).h * t) ^ T.hs p i * evalR x (T.g i) := by
        rw [ht, one_pow, one_mul]
    _ = t ^ T.hs p i * (evalR x (T.piece p).h ^ T.hs p i * evalR x (T.g i)) := by ring
    _ = _ := by
      rw [h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring

/-- The partition of unity at a real point. -/
lemma cid_real {x : Fin (m + n) → ℝ} (hx : PtG G x) :
    (T.C0 : ℝ) = ∑ i, evalR x (T.cb i) * evalR x (T.g i) +
      ∑ p, evalR x (T.ca p) * evalR x (T.piece p).h := by
  have h := evalR_eq_of_sub_mem hx T.cid
  simp only [map_natCast, map_add, map_mul, map_sum] at h
  simp only [← evalR_eq_evalHom] at h
  rw [h]

end CertPush

namespace PolyChart

variable {m n : ℕ}

/-- The three chart fields of `PushData` with given constants. -/
def FieldsAt (P : PolyChart m n) (C R K S L : ℝ) : Prop :=
  (∀ z, PtG P.G z → Bdd C z → P.valid z → ∀ c e, e ≤ R → Close e c (P.φ z) →
      ∃ z', PtG P.G z' ∧ P.φ z' = c ∧ Close (K * e) z' z) ∧
  (∀ z, PtG P.G z → Bdd C z → P.valid z → ∀ z' z'', PtG P.G z' → PtG P.G z'' →
      Close S z' z → Close S z'' z → ∀ e, Close e (P.φ z') (P.φ z'') → Close (K * e) z' z'') ∧
  (∀ z, PtG P.G z → Bdd C z → P.valid z → ∀ z' z'' e, Close S z' z → Close S z'' z →
      Close e z' z'' → Close (L * e) (P.φ z') (P.φ z''))

lemma FieldsAt.mono {P : PolyChart m n} {C R K S L R' K' S' L' : ℝ} (h : P.FieldsAt C R K S L)
    (hR : R' ≤ R) (hK : K ≤ K') (hS : S' ≤ S) (hL : L ≤ L') : P.FieldsAt C R' K' S' L' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun z hz hzC hv c e he hc => ?_, fun z hz hzC hv z' z'' hz' hz'' hs hs' e hc => ?_,
    fun z hz hzC hv z' z'' e hs hs' hc => ?_⟩
  · obtain ⟨z', h', hφ, hcl⟩ := h1 z hz hzC hv c e (he.trans hR) hc
    exact ⟨z', h', hφ, hcl.mono (mul_le_mul_of_nonneg_right hK (P.nonneg_of_close hc))⟩
  · exact (h2 z hz hzC hv z' z'' hz' hz'' (hs.mono hS) (hs'.mono hS) e hc).mono
      (mul_le_mul_of_nonneg_right hK (P.nonneg_of_close hc))
  · have he : 0 ≤ e := (abs_nonneg _).trans (hc ⟨m, by have := P.hn; omega⟩)
    exact (h3 z hz hzC hv z' z'' e (hs.mono hS) (hs'.mono hS) hc).mono
      (mul_le_mul_of_nonneg_right hL he)

lemma fieldsAt (P : PolyChart m n) (C : ℝ) (hC : 0 ≤ C) :
    ∃ R K S L, 0 < R ∧ 0 ≤ K ∧ 0 < S ∧ 0 ≤ L ∧ P.FieldsAt C R K S L := by
  obtain ⟨R, K, S, L, hR, hK, hS, hL, h1, h2, h3⟩ := P.fields C hC
  exact ⟨R, K, S, L, hR, hK, hS, hL, h1, h2, h3⟩

end PolyChart

namespace CertPush

variable {m n : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)} (T : CertPush m n G)

/-- **Certified data give push-off data on every box.** -/
theorem pushData (C : ℝ) : Nonempty (PushData (m + n) (PtG G) T.nu C) := by
  set C₀ := |C|
  have hC₀ : 0 ≤ C₀ := abs_nonneg C
  set C₁ := C₀ + 1
  have hC₁ : 0 ≤ C₁ := by positivity
  have hbC : ∀ z : Fin (m + n) → ℝ, Bdd C z → Bdd C₀ z := fun z hz k => (hz k).trans (le_abs_self C)
  -- 1. the cover
  obtain ⟨A₁, hA₁, hbA₁⟩ := exists_uniform (fun i A => ∀ x, Bdd C₀ x → |evalR x (T.cb i)| ≤ A)
    (fun i A A' h hAA' x hx => (h x hx).trans hAA')
    (fun i => by
      obtain ⟨M, -, hM, -, hb, -⟩ := poly_bdd_lip C₀ hC₀ (T.cb i)
      exact ⟨M, hM, hb⟩) Finset.univ
  obtain ⟨A₂, hA₂, hbA₂⟩ := exists_uniform (fun p A => ∀ x, Bdd C₀ x → |evalR x (T.ca p)| ≤ A)
    (fun p A A' h hAA' x hx => (h x hx).trans hAA')
    (fun p => by
      obtain ⟨M, -, hM, -, hb, -⟩ := poly_bdd_lip C₀ hC₀ (T.ca p)
      exact ⟨M, hM, hb⟩) Finset.univ
  set A := A₁ + A₂
  have hA : 0 ≤ A := by positivity
  obtain ⟨κc, hκc, h8κ, hκc1⟩ :=
    exists_pos_mul_le₂ one_pos one_pos (8 * A * Fintype.card (T.ι ⊕ T.J)) 1
  rw [one_mul] at hκc1
  obtain ⟨θ₁, hθ₁, h8θ⟩ := exists_pos_mul_le one_pos (8 * A)
  obtain ⟨θlo, hθlo, h2θ⟩ := exists_pos_mul_le hκc 2
  have hθlt : θlo < κc := lt_of_two_mul_le h2θ hκc
  -- 2. the charts
  set P : T.J → PolyChart m n := fun p => (T.piece p).toPolyChart κc θlo hθlo hθlt
  obtain ⟨R, K, S₀, L, hR, hK, hS₀, hL, hF⟩ := exists_uniform4
    (fun p R K S L => (P p).FieldsAt C₀ R K S L)
    (fun p R K S L R' K' S' L' h _ hR' hK' _ hS' hL' => h.mono hR' hK' hS' hL')
    (fun p => (P p).fieldsAt C₀ hC₀) Finset.univ
  -- 3. Lipschitz constant of the `h_p` on the box `C₁`, and the final `S`
  obtain ⟨Lh, hLh, hLip⟩ := exists_uniform
    (fun p L => ∀ x x' δ, 0 ≤ δ → Bdd C₁ x → Bdd C₁ x' → Close δ x x' →
      |evalR x (T.piece p).h - evalR x' (T.piece p).h| ≤ L * δ)
    (fun p L L' h hLL' x x' δ hδ hx hx' hc =>
      (h x x' δ hδ hx hx' hc).trans (mul_le_mul_of_nonneg_right hLL' hδ))
    (fun p => by
      obtain ⟨-, L, -, hL, -, hl⟩ := poly_bdd_lip C₁ hC₁ (T.piece p).h
      exact ⟨L, hL, fun x x' δ _ hx hx' hc => hl x x' δ hx hx' hc⟩) Finset.univ
  obtain ⟨S, hS, hSl⟩ := exists_pos_mul_le_list [(1, S₀), (1, 1), (Lh, κc - θlo)]
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨zero_le_one, hS₀⟩
      · exact ⟨zero_le_one, one_pos⟩
      · exact ⟨hLh, sub_pos.2 hθlt⟩)
  have hSS₀ : S ≤ S₀ := by simpa using hSl (1, S₀) (by simp)
  have hS1 : S ≤ 1 := by simpa using hSl (1, 1) (by simp)
  have hLhS : Lh * S ≤ κc - θlo := hSl (Lh, κc - θlo) (by simp)
  -- 4. inverses of `h_p` near valid points
  obtain ⟨t₀, ht₀, hθt₀⟩ := exists_inv_pos hθlo
  have hnear : ∀ p z z', Bdd C₀ z → κc ≤ |evalR z (T.piece p).h| → Close S z' z →
      Bdd C₁ z' ∧ ∃ t, evalR z' (T.piece p).h * t = 1 ∧ |t| ≤ t₀ := by
    intro p z z' hz hv hz'
    have hz'C : Bdd C₁ z' := (hz.of_close hz').mono (by simp only [C₁]; linarith)
    have hzC : Bdd C₁ z := hz.mono (by simp only [C₁]; linarith)
    refine ⟨hz'C, ?_⟩
    have h1 := hLip p (Finset.mem_univ p) z' z S hS.le hz'C hzC hz'
    have h2 := abs_sub_abs_le_abs_sub (evalR z (T.piece p).h) (evalR z' (T.piece p).h)
    rw [abs_sub_comm] at h1
    have hge : θlo ≤ |evalR z' (T.piece p).h| := by linarith
    obtain ⟨t, ht, htθ⟩ := exists_inv_of_le_abs hθlo hge
    refine ⟨t, ht, ?_⟩
    calc |t| = |t| * (θlo * t₀) := by rw [hθt₀, mul_one]
      _ = (|t| * θlo) * t₀ := by ring
      _ ≤ 1 * t₀ := mul_le_mul_of_nonneg_right htθ ht₀.le
      _ = t₀ := one_mul _
  -- 5. constants for `nu_lo`
  set slo : Finset (T.J × Fin T.k × (T.ι → ℕ)) := Finset.univ.biUnion fun pq : T.J × Fin T.k =>
    (T.lΓ pq.1 pq.2).image fun γ => (pq.1, pq.2, γ)
  obtain ⟨Klo, hKlo, hKl⟩ := exists_uniform
    (fun (pqγ : T.J × Fin T.k × (T.ι → ℕ)) K => ∀ x, Bdd C₁ x → ∀ t, |t| ≤ t₀ →
      |evalR x (T.lc pqγ.1 pqγ.2.1 pqγ.2.2) * t ^ T.ls pqγ.1 pqγ.2.1| ≤ K)
    (fun _ K K' h hKK' x hx t ht => (h x hx t ht).trans hKK')
    (fun pqγ => by
      obtain ⟨M, -, hM, -, hb, -⟩ := poly_bdd_lip C₁ hC₁ (T.lc pqγ.1 pqγ.2.1 pqγ.2.2)
      refine ⟨M * t₀ ^ T.ls pqγ.1 pqγ.2.1, by positivity, fun x hx t ht => ?_⟩
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hb x hx) (pow_le_pow_left₀ (abs_nonneg _) ht _) (by positivity) hM)
    slo
  set Γb : ℝ := ∑ pq : T.J × Fin T.k, ((T.lΓ pq.1 pq.2).card : ℝ)
  obtain ⟨κ, hκ, hκ4, hκ2⟩ := exists_pos_mul_le₂ one_pos one_pos (4 * Klo * Γb) 2
  set Eb := ∑ i, T.E i
  -- 6. constants for `nu_hi`
  set shi : Finset (T.J × T.ι × (Fin T.k → ℕ)) := Finset.univ.biUnion fun pi : T.J × T.ι =>
    (T.hΓ pi.1 pi.2).image fun α => (pi.1, pi.2, α)
  obtain ⟨Khi, hKhi, hKh⟩ := exists_uniform
    (fun (piα : T.J × T.ι × (Fin T.k → ℕ)) K => ∀ x, Bdd C₁ x → ∀ t, |t| ≤ t₀ →
      |evalR x (T.hb piα.1 piα.2.1 piα.2.2) * t ^ T.hs piα.1 piα.2.1| ≤ K)
    (fun _ K K' h hKK' x hx t ht => (h x hx t ht).trans hKK')
    (fun piα => by
      obtain ⟨M, -, hM, -, hb, -⟩ := poly_bdd_lip C₁ hC₁ (T.hb piα.1 piα.2.1 piα.2.2)
      refine ⟨M * t₀ ^ T.hs piα.1 piα.2.1, by positivity, fun x hx t ht => ?_⟩
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hb x hx) (pow_le_pow_left₀ (abs_nonneg _) ht _) (by positivity) hM)
    shi
  set Γh : ℝ := ∑ pi : T.J × T.ι, ((T.hΓ pi.1 pi.2).card : ℝ)
  set chi : ℝ := ∑ i, (Khi * Γh) ^ T.E i
  have hEb : ∀ i, T.E i ≤ Eb := fun i =>
    Finset.single_le_sum (f := T.E) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨{
    J := T.J
    ch := fun p => {
      n := n, k := T.k, hk := T.hk, hd := T.hd p, hd_inj := T.hd_inj p, w := T.w p,
      hw := T.hw p, φ := (P p).φ, valid := (P p).valid }
    θ := κc ^ Eb
    hθ := pow_pos hκc _
    cover := ?_
    D := T.D₂
    hD := T.hD
    R := R
    K := K
    S := S
    Lφ := L
    clo := κ ^ Eb
    chi := chi
    hR := hR
    hK := hK
    hS := hS
    hL := hL
    hclo := pow_pos hκ _
    hchi := Finset.sum_nonneg fun i _ => (T.hE i).pow_nonneg _
    sect := ?_
    inj := ?_
    lipφ := ?_
    nu_lo := ?_
    nu_hi := ?_ }⟩
  · intro z hz hzC
    have hz₀ := hbC z hzC
    -- `1/C` for the integer constant of the partition
    have hC0r : (0 : ℝ) < T.C0 := Nat.cast_pos.2 T.hC0
    obtain ⟨tC, htC, hCt⟩ := exists_inv_pos hC0r
    have htC1 : tC ≤ 1 := by
      have h1 : (1 : ℝ) ≤ T.C0 := Nat.one_le_cast.2 T.hC0
      calc tC = tC * 1 := (mul_one _).symm
        _ ≤ tC * T.C0 := mul_le_mul_of_nonneg_left h1 htC.le
        _ = 1 := by rw [mul_comm]; exact hCt
    have hsc : ∀ e : ℝ, |e * tC| ≤ |e| := fun e => by
      rw [abs_mul, abs_of_pos htC]
      calc |e| * tC ≤ |e| * 1 := mul_le_mul_of_nonneg_left htC1 (abs_nonneg _)
        _ = |e| := mul_one _
    -- one family `ι ⊕ J`: the generators and the chart elements
    set a' : T.ι ⊕ T.J → ℝ := fun s => Sum.elim (fun i => evalR z (T.cb i) * tC)
      (fun p => evalR z (T.ca p) * tC) s
    set h' : T.ι ⊕ T.J → ℝ := fun s => Sum.elim (fun i => evalR z (T.g i))
      (fun p => evalR z (T.piece p).h) s
    have ha' : ∀ s, |a' s| ≤ A := fun s => by
      rcases s with i | p
      · exact (hsc _).trans ((hbA₁ i (Finset.mem_univ i) z hz₀).trans (by simp only [A]; linarith))
      · exact (hsc _).trans ((hbA₂ p (Finset.mem_univ p) z hz₀).trans (by simp only [A]; linarith))
    have hid : 1 = 0 * 0 + ∑ s, a' s * h' s := by
      rw [Fintype.sum_sum_type, zero_mul, zero_add]
      have h := T.cid_real hz
      calc (1 : ℝ) = T.C0 * tC := hCt.symm
        _ = _ := by
          rw [h, add_mul, Finset.sum_mul, Finset.sum_mul]
          congr 1
          · refine Finset.sum_congr rfl fun i _ => ?_
            simp only [a', h', Sum.elim_inl]; ring
          · refine Finset.sum_congr rfl fun p _ => ?_
            simp only [a', h', Sum.elim_inr]; ring
    rcases cover_of_identity 0 0 a' h' A θ₁ κc hθ₁ hκc le_rfl (by simp; exact hA) ha' h8θ h8κ
        hid with h | ⟨s, hs⟩
    · exact absurd (lt_of_lt_of_le hθ₁ h) (lt_irrefl 0)
    rcases s with i | p
    · left
      have hs : κc ≤ |evalR z (T.g i)| := hs
      have h1 : κc ^ Eb ≤ κc ^ T.E i := pow_le_pow_of_le_one hκc.le hκc1 (hEb i)
      have h2 : κc ^ T.E i ≤ evalR z (T.g i) ^ T.E i := by
        exact (pow_le_pow_left₀ hκc.le hs _).trans (le_of_eq ((T.hE i).pow_abs _))
      have h3 : evalR z (T.g i) ^ T.E i ≤ T.nu z :=
        Finset.single_le_sum (f := fun j => evalR z (T.g j) ^ T.E j)
          (fun j _ => (T.hE j).pow_nonneg _) (Finset.mem_univ i)
      linarith
    · exact Or.inr ⟨p, hs⟩
  · intro j z hz hzC hv c e he hc
    exact (hF j (Finset.mem_univ j)).1 z hz (hbC z hzC) hv c e he hc
  · intro j z hz hzC hv z' z'' hz' hz'' h1 h2 e hc
    exact (hF j (Finset.mem_univ j)).2.1 z hz (hbC z hzC) hv z' z'' hz' hz'' (h1.mono hSS₀)
      (h2.mono hSS₀) e hc
  · intro j z hz hzC hv z' z'' e h1 h2 hc
    exact (hF j (Finset.mem_univ j)).2.2 z hz (hbC z hzC) hv z' z'' e (h1.mono hSS₀)
      (h2.mono hSS₀) hc
  · intro j z hz hzC hv z' hz' hz'S r hr hr1 q hq
    obtain ⟨hz'C, t, ht, htt⟩ := hnear j z z' (hbC z hzC) hv hz'S
    have hc : ∀ γ ∈ T.lΓ j q, |evalR z' (T.lc j q γ) * t ^ T.ls j q| ≤ Klo := fun γ hγ =>
      hKl (j, q, γ) (Finset.mem_biUnion.2 ⟨(j, q), Finset.mem_univ _,
        Finset.mem_image.2 ⟨γ, hγ, rfl⟩⟩) z' hz'C t htt
    have hcard : 4 * Klo * ((T.lΓ j q).card : ℝ) * κ ≤ 1 := by
      have h1 : ((T.lΓ j q).card : ℝ) ≤ Γb :=
        Finset.single_le_sum (f := fun pq : T.J × Fin T.k => ((T.lΓ pq.1 pq.2).card : ℝ))
          (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ (j, q))
      have h2 : 4 * Klo * ((T.lΓ j q).card : ℝ) ≤ 4 * Klo * Γb :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have := mul_le_mul_of_nonneg_right h2 hκ.le
      linarith
    exact nu_lo_of_identity_ge (fun i => evalR z' (T.g i)) T.d T.E T.D₂ Eb (T.la j q) (T.w j q)
      T.hE T.hEd hEb (T.lΓ j q) (fun γ => evalR z' (T.lc j q γ) * t ^ T.ls j q) Klo κ hκ hκ2
      hcard hc (T.lhom j q) (T.lne j q) _ (T.lid_real hz' j q ht) r hr hr1 hq
  · intro j z hz hzC hv z' hz' hz'S r hr hr1 hall
    obtain ⟨hz'C, t, ht, htt⟩ := hnear j z z' (hbC z hzC) hv hz'S
    have hb : ∀ i, ∀ α ∈ T.hΓ j i, |evalR z' (T.hb j i α) * t ^ T.hs j i| ≤ Khi :=
      fun i α hα => hKh (j, i, α) (Finset.mem_biUnion.2 ⟨(j, i), Finset.mem_univ _,
        Finset.mem_image.2 ⟨α, hα, rfl⟩⟩) z' hz'C t htt
    have h := nu_hi_of_identity (fun i => evalR z' (T.g i)) T.d T.E T.D₂ T.hE T.hEd
      (fun q => evalR z' ((T.piece j).F (Fin.natAdd m (T.hd j q)))) (T.w j) (T.hΓ j)
      (fun i α => evalR z' (T.hb j i α) * t ^ T.hs j i) Khi hKhi hb (T.hdeg j)
      (fun i => T.hid_real hz' j i ht) r hr.le hr1 hall
    refine h.trans (mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun i _ => ?_)
      (pow_nonneg hr.le _))
    have h1 : ((T.hΓ j i).card : ℝ) ≤ Γh :=
      Finset.single_le_sum (f := fun pi : T.J × T.ι => ((T.hΓ pi.1 pi.2).card : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ (j, i))
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left h1 hKhi) _

end CertPush

/-- `ChainLift.torsor` with push-off data given only as `Nonempty` on each box. -/
theorem ChainLift.torsor' {N N' : ℕ} {ι : Type*} [Fintype ι] (T : OffStep N N' ι)
    (PD : ∀ C, Nonempty (PushData N T.Pt T.nu C)) : ChainLift T.Pt T.Pt' T.π := by
  intro C
  obtain ⟨C', hC'⟩ := T.lift_chain (C + 1)
  refine ⟨C', fun ε hε => ?_⟩
  obtain ⟨P⟩ := PD C
  obtain ⟨ρ, hρ, hpush⟩ := P.push_off ε hε
  obtain ⟨δ₁, hδ₁, hlift⟩ := hC' ρ hρ ε hε
  obtain ⟨δ, hδ, hpush'⟩ := hpush δ₁ hδ₁
  refine ⟨δ, hδ, fun m z hz => ?_⟩
  obtain ⟨m', w, ι', hw, hν, hι, hcl⟩ := hpush' m z hz
  obtain ⟨u, hu, hπ⟩ := hlift m' w hw hν
  exact ⟨m', u, ι', hu, hι, fun j hj => by rw [hπ j hj]; exact hcl j hj⟩

/-- **A certified torsor step lifts chains.** The step is given semantically (`OffStep`: the
explicit lift is a ring map), its base is the presentation `G`, and its filtration generators
are the certified `T.g`. -/
theorem ChainLift.torsor_cert {m n N' : ℕ} {G : List (MvPolynomial (Fin (m + n)) ℤ)}
    (T : CertPush m n G) (O : OffStep (m + n) N' T.ι) (hPt : O.Pt = PtG G)
    (hg : O.g = fun i w => evalR w (T.g i)) (hE : O.E = T.E) : ChainLift O.Pt O.Pt' O.π := by
  refine ChainLift.torsor' O fun C => ?_
  have hν : O.nu = T.nu := by
    funext w; simp only [OffStep.nu, CertPush.nu, hg, hE]
  rw [hPt, hν]
  exact T.pushData C

end BezoutCounterexample.Constructive
