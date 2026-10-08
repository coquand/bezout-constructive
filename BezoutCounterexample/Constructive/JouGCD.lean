import BezoutCounterexample.Constructive.GenericPrime
import BezoutCounterexample.Jouanolou

/-!
# Jouanolou rings over GCD domains (`~/COLL/bezout-gcd.tex`, §5–6, generic-prime route)

Let `B` be a GCD domain with a zero test and `c = (c₀, …, c_r)` a row with `c₀ ≠ 0` and no common
non-unit divisor. Then `J_B(c)` is a GCD domain (`hasGcd_jou`).

No prime among the `cᵢ` is needed, so HM's Kaplansky prime `π ∈ 𝔭` (`ReesData.exists_prime_mem`)
disappears from the torsor step and the tower of HM is unchanged. The proof puts the generic
prime inside: with `B' = B[λ₀, …, λ_r]` and `π = Σ cᵢ λᵢ` (prime by `prime_generic`),

* `genEquiv`: `J_{B'}(π, c) ≅ J_B(c)[σ', λ]`, by the substitution `τᵢ = σᵢ + λᵢ σ'`
  (`σ'` is the coordinate paired with `π`);
* `J_{B'}(π, c)` has gcds by Nagata at `π` (`hasGcd_of_away`): modulo `π` it is
  `J_{B'/π}(c̄)`, a domain since `π ∤ c₀` (degree); inverting `π` gives a polynomial ring over
  `B'[1/π]`;
* gcds descend from `J_B(c)[σ', λ]` to `J_B(c)` (`hasGcd_of_mvPolynomial`): a divisor of a
  nonzero constant is a constant (total degree).

Inputs besides the GCD structure: zero tests, inductive Noetherianity of `B` (for the
`π`-adic valuation, `NBar.exists_val`) and a decision of divisibility by `π` in `J_{B'}(π, c)`
(Gröbner, in the f.p. case).
-/

namespace BezoutCounterexample.Constructive

open MvPolynomial

section Descent

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
/-- The zero test passes to `R[X₁, …, Xₙ]`. -/
lemma mvPolynomial_eq_zero_or (hz : ∀ a : R, a = 0 ∨ a ≠ 0) :
    ∀ (n : ℕ) (f : MvPolynomial (Fin n) R), f = 0 ∨ f ≠ 0
  | 0 => eq_zero_or_of_ringEquiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)) hz
  | n + 1 => eq_zero_or_of_ringEquiv (MvPolynomial.finSuccEquiv R n).toRingEquiv
      (polynomial_eq_zero_or (mvPolynomial_eq_zero_or hz n))

/-- A divisor of a nonzero constant is a constant. -/
lemma exists_eq_C_of_dvd_C {n : ℕ} {f : MvPolynomial (Fin n) R} {a : R} (ha : a ≠ 0)
    (h : f ∣ C a) : ∃ g, f = C g := by
  obtain ⟨e, he⟩ := h
  have hf0 : f ≠ 0 := by rintro rfl; rw [zero_mul, C_eq_zero] at he; exact ha he
  have he0 : e ≠ 0 := by rintro rfl; rw [mul_zero, C_eq_zero] at he; exact ha he
  have := totalDegree_mul_of_isDomain (R := R) hf0 he0
  rw [← he, totalDegree_C] at this
  exact ⟨_, totalDegree_eq_zero_iff_eq_C.1 (by omega)⟩

omit [IsDomain R] in
lemma dvd_of_C_dvd_C {n : ℕ} {a b : R} (h : (C a : MvPolynomial (Fin n) R) ∣ C b) : a ∣ b := by
  simpa using (C_dvd_iff_dvd_coeff _ _).1 h 0

/-- **Descent of gcds** from `R[X₁, …, Xₙ]` to `R`. -/
theorem hasGcd_of_mvPolynomial (hz : ∀ a : R, a = 0 ∨ a ≠ 0) {n : ℕ}
    (h : HasGcd (MvPolynomial (Fin n) R)) : HasGcd R := by
  intro a b
  rcases hz a with rfl | ha
  · exact ⟨b, isGcd_zero_left b⟩
  obtain ⟨G, hGa, hGb, hGc⟩ := h (C a) (C b)
  obtain ⟨g, rfl⟩ := exists_eq_C_of_dvd_C ha hGa
  exact ⟨g, dvd_of_C_dvd_C hGa, dvd_of_C_dvd_C hGb,
    fun c hca hcb => dvd_of_C_dvd_C (hGc _ (_root_.map_dvd C hca) (_root_.map_dvd C hcb))⟩

/-- The zero test passes to localisations of a domain. -/
lemma localization_eq_zero_or (hz : ∀ a : R, a = 0 ∨ a ≠ 0) (S : Submonoid R)
    (hS : S ≤ nonZeroDivisors R) (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L]
    (x : L) : x = 0 ∨ x ≠ 0 := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
  rcases hz a with rfl | ha
  · exact Or.inl (IsLocalization.mk'_zero _)
  · refine Or.inr fun h => ha ?_
    obtain ⟨⟨m, hm⟩, hm0⟩ := (IsLocalization.mk'_eq_zero_iff a s).1 h
    exact (mul_eq_zero.1 hm0).resolve_left (nonZeroDivisors.ne_zero (hS hm))

end Descent

section Generic

variable {B : Type*} [CommRing B] {r : ℕ} (c : Fin (r + 1) → B)

/-- The generic combination `π = Σ cᵢ λᵢ ∈ B[λ₀, …, λ_r]`. -/
noncomputable def genπ : MvPolynomial (Fin (r + 1)) B := ∑ i, C (c i) * X i

/-- The row `(π, c₀, …, c_r)` over `B[λ]`. -/
noncomputable def genRow : Fin (r + 1 + 1) → MvPolynomial (Fin (r + 1)) B :=
  Fin.cons (genπ c) fun i => C (c i)

/-- `J_{B[λ]}(π, c)`. -/
abbrev genJ := Jou.J (genRow c)

/-- `π` in `J_{B[λ]}(π, c)`. -/
noncomputable abbrev genπJ : genJ c :=
  algebraMap (MvPolynomial (Fin (r + 1)) B) (genJ c) (genπ c)

end Generic

lemma eval₂Hom_rel {R : Type*} [CommRing R] {S : Type*} [CommRing S] {n : ℕ} (c : Fin n → R)
    (f : R →+* S) (g : Fin n → S) : eval₂Hom f g (Jou.rel c) = ∑ i, f (c i) * g i - 1 := by
  rw [Jou.rel_eq]; simp

section Equiv

variable {B : Type*} [CommRing B] {r : ℕ} (c : Fin (r + 1) → B)


/-- `λᵢ` in `J_{B[λ]}(π, c)`. -/
noncomputable abbrev lamD (i : Fin (r + 1)) : genJ c :=
  algebraMap (MvPolynomial (Fin (r + 1)) B) (genJ c) (X i)

/-- The coordinates `σ'_k` of `J_{B[λ]}(π, c)`. -/
noncomputable abbrev sigD (k : Fin (r + 1 + 1)) : (genJ c) := Jou.σ (genRow c) k

/-- `B[λ] → J_B(c)[σ', λ]`: `λᵢ ↦ X_{i+1}`. -/
noncomputable def betaHom : (MvPolynomial (Fin (r + 1)) B) →+* (MvPolynomial (Fin (r + 1 + 1)) (Jou.J c)) :=
  eval₂Hom (C.comp (algebraMap B (Jou.J c))) fun i => X i.succ

omit [CommRing B] in
lemma betaHom_C [CommRing B] (b : B) : betaHom c (C b) = C (algebraMap B (Jou.J c) b) := by
  simp [betaHom]

lemma betaHom_genπ : betaHom c (genπ c) = ∑ i, C (algebraMap B (Jou.J c) (c i)) * X i.succ := by
  simp [betaHom, genπ]

/-- The images in `J_B(c)[σ', λ]` of the coordinates of `J_{B[λ]}(π, c)`. -/
noncomputable def vPsi : Fin (r + 1 + 1) → (MvPolynomial (Fin (r + 1 + 1)) (Jou.J c)) := Fin.cons (X 0) fun i => C (Jou.σ c i) - X i.succ * X 0

set_option maxHeartbeats 2000000 in
lemma psi_rel : eval₂Hom (betaHom c) (vPsi c) (Jou.rel (genRow c)) = 0 := by
  rw [eval₂Hom_rel (genRow c) (betaHom c) (vPsi c), Fin.sum_univ_succ]
  have h0 : genRow c 0 = genπ c := rfl
  have hs : ∀ i, genRow c i.succ = C (c i) := fun i => rfl
  have v0 : vPsi c 0 = X 0 := rfl
  have vs : ∀ i, vPsi c i.succ = C (Jou.σ c i) - X i.succ * X 0 := fun i => rfl
  simp only [h0, hs, v0, vs, betaHom_C, betaHom_genπ]
  have h := congrArg (C : Jou.J c → (MvPolynomial (Fin (r + 1 + 1)) (Jou.J c))) (Jou.sum_σ_mul c)
  simp only [map_sum, map_one, map_mul] at h
  rw [← h, Finset.sum_mul, ← Finset.sum_add_distrib, sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `J_{B[λ]}(π, c) → J_B(c)[σ', λ]`: `σ'₀ ↦ X₀`, `σ'_{i+1} ↦ τᵢ - λᵢ σ'`. -/
noncomputable def psiHom : (genJ c) →+* (MvPolynomial (Fin (r + 1 + 1)) (Jou.J c)) :=
  Ideal.Quotient.lift _ (eval₂Hom (betaHom c) (vPsi c)) (fun a ha => by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, psi_rel, mul_zero])

/-- `J_B(c) → J_{B[λ]}(π, c)`: `τᵢ ↦ σ'_{i+1} + λᵢ σ'₀`. -/
noncomputable def gammaHom : Jou.J c →+* (genJ c) :=
  Ideal.Quotient.lift _ (eval₂Hom ((algebraMap (MvPolynomial (Fin (r + 1)) B) (genJ c)).comp C)
    fun i => sigD c i.succ + lamD c i * sigD c 0) (fun a ha => by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul]
      refine mul_eq_zero_of_right _ ?_
      have h : sigD c 0 * ∑ i, algebraMap (MvPolynomial (Fin (r + 1)) B) (genJ c) (C (c i)) * lamD c i +
          ∑ i, sigD c i.succ * algebraMap (MvPolynomial (Fin (r + 1)) B) (genJ c) (C (c i)) = 1 := by
        have h0 := Jou.sum_σ_mul (genRow c)
        rw [Fin.sum_univ_succ] at h0
        rw [← h0]
        congr 1
        show sigD c 0 * _ = sigD c 0 * algebraMap (MvPolynomial (Fin (r + 1)) B) (genJ c) (genπ c)
        rw [genπ, map_sum]
        simp only [map_mul]
      refine (eval₂Hom_rel c ((algebraMap (MvPolynomial (Fin (r + 1)) B) (genJ c)).comp C) _).trans ?_
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← h, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_eq_zero fun i _ => by ring)

/-- `J_B(c)[σ', λ] → J_{B[λ]}(π, c)`. -/
noncomputable def phiHom : (MvPolynomial (Fin (r + 1 + 1)) (Jou.J c)) →+* (genJ c) :=
  eval₂Hom (gammaHom c) (Fin.cons (sigD c 0) (lamD c))

lemma sigma_eq (i : Fin (r + 1)) :
    Jou.σ c i = Ideal.Quotient.mk (Ideal.span {Jou.rel c}) (X i) := rfl

lemma sigD_eq (k : Fin (r + 1 + 1)) :
    sigD c k = Ideal.Quotient.mk (Ideal.span {Jou.rel (genRow c)}) (X k) := rfl

lemma algD_eq (x : (MvPolynomial (Fin (r + 1)) B)) :
    algebraMap (MvPolynomial (Fin (r + 1)) B) (genJ c) x = Ideal.Quotient.mk (Ideal.span {Jou.rel (genRow c)}) (C x) := rfl

lemma algJ_eq (b : B) :
    algebraMap B (Jou.J c) b = Ideal.Quotient.mk (Ideal.span {Jou.rel c}) (C b) := rfl

lemma psi_sigD (k : Fin (r + 1 + 1)) : psiHom c (sigD c k) = vPsi c k := by
  rw [sigD_eq, psiHom, Ideal.Quotient.lift_mk, eval₂Hom_X']

lemma psi_algD (x : (MvPolynomial (Fin (r + 1)) B)) : psiHom c (algebraMap (MvPolynomial (Fin (r + 1)) B) (genJ c) x) = betaHom c x := by
  rw [algD_eq, psiHom, Ideal.Quotient.lift_mk, eval₂Hom_C]

lemma gamma_sigma (i : Fin (r + 1)) :
    gammaHom c (Jou.σ c i) = sigD c i.succ + lamD c i * sigD c 0 := by
  rw [sigma_eq, gammaHom, Ideal.Quotient.lift_mk, eval₂Hom_X']

lemma gamma_algJ (b : B) : gammaHom c (algebraMap B (Jou.J c) b) = algebraMap (MvPolynomial (Fin (r + 1)) B) (genJ c) (C b) := by
  rw [algJ_eq, gammaHom, Ideal.Quotient.lift_mk, eval₂Hom_C]; rfl

lemma psi_comp_gamma : (psiHom c).comp (gammaHom c) = C := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply]
    rw [← algJ_eq, gamma_algJ, psi_algD, betaHom_C]
  · intro i
    simp only [RingHom.comp_apply]
    rw [← sigma_eq, gamma_sigma, map_add, map_mul, psi_sigD, psi_sigD, psi_algD]
    simp only [vPsi, Fin.cons_zero, Fin.cons_succ, betaHom, eval₂Hom_X']
    ring

lemma psi_comp_phi : (psiHom c).comp (phiHom c) = RingHom.id (MvPolynomial (Fin (r + 1 + 1)) (Jou.J c)) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp only [RingHom.comp_apply, phiHom, eval₂Hom_C, RingHom.id_apply]
    exact RingHom.congr_fun (psi_comp_gamma c) z
  · intro k
    simp only [RingHom.comp_apply, phiHom, eval₂Hom_X', RingHom.id_apply]
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [Fin.cons_zero, psi_sigD, vPsi]
    · simp only [Fin.cons_succ, lamD, psi_algD, betaHom, eval₂Hom_X']

lemma phi_comp_beta : (phiHom c).comp (betaHom c) = algebraMap (MvPolynomial (Fin (r + 1)) B) (genJ c) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, betaHom, eval₂Hom_C, phiHom]
    rw [gamma_algJ]
  · intro i
    simp only [RingHom.comp_apply, betaHom, eval₂Hom_X', phiHom, Fin.cons_succ]

lemma phi_comp_psi : (phiHom c).comp (psiHom c) = RingHom.id (genJ c) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro x
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [← algD_eq, psi_algD]
    exact RingHom.congr_fun (phi_comp_beta c) x
  · intro k
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [← sigD_eq, psi_sigD]
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [vPsi, Fin.cons_zero, phiHom, eval₂Hom_X']
    · simp only [vPsi, Fin.cons_succ, map_sub, map_mul, phiHom, eval₂Hom_C, eval₂Hom_X',
        Fin.cons_zero]
      rw [gamma_sigma]; ring

/-- **The substitution `τᵢ = σᵢ + λᵢ σ'`**: `J_B(c)[σ', λ] ≅ J_{B[λ]}(π, c)`. -/
noncomputable def genEquiv : (MvPolynomial (Fin (r + 1 + 1)) (Jou.J c)) ≃+* (genJ c) :=
  RingEquiv.ofRingHom (phiHom c) (psiHom c) (phi_comp_psi c) (psi_comp_phi c)

end Equiv

section Main

variable {B : Type*} [CommRing B] [IsDomain B] {r : ℕ} (c : Fin (r + 1) → B)

omit [IsDomain B] in
lemma genπ_coeff (i : Fin (r + 1)) : (genπ c).coeff (Finsupp.single i 1) = c i :=
  coeff_single_linear c i

/-- `π` divides no nonzero constant. -/
lemma not_dvd_genπ (hc0 : c 0 ≠ 0) {b : B} (hb : b ≠ 0) : ¬ genπ c ∣ C b := by
  intro h
  obtain ⟨g, hg⟩ := exists_eq_C_of_dvd_C hb h
  have := congrArg (fun f : MvPolynomial (Fin (r + 1)) B => f.coeff (Finsupp.single 0 1)) hg
  simp only [genπ_coeff, coeff_C] at this
  split_ifs at this with h0
  · exact absurd h0.symm (Finsupp.single_ne_zero.2 one_ne_zero)
  · exact hc0 this

/-- **Jouanolou rings over GCD domains are GCD domains**, for a row with no common non-unit
divisor; no prime element among the `cᵢ` is needed. -/
theorem hasGcd_jou (hG : HasGcd B) (hz : ∀ b : B, b = 0 ∨ b ≠ 0) (hN : PolyIndNoeth B)
    (hc0 : c 0 ≠ 0) (hrel : ∀ e : B, (∀ i, e ∣ c i) → IsUnit e)
    (hzJ : ∀ z : Jou.J c, z = 0 ∨ z ≠ 0)
    (hdvd : ∀ z : genJ c, genπJ c ∣ z ∨ ¬ genπJ c ∣ z) : HasGcd (Jou.J c) := by
  obtain ⟨hGB', hzB'⟩ := hasGcd_mvPolynomial hG hz (r + 1)
  have hπ : Prime (genπ c) := prime_generic hG hz c hc0 hrel
  have : IsDomain (Jou.J c) := Jou.isDomain (l := 0) hc0
  have : IsDomain (genJ c) := Jou.isDomain (c := genRow c) (l := 0) hπ.ne_zero
  -- `π` is prime in `J_{B[λ]}(π, c)`
  have hπD : Prime (genπJ c) := by
    have hne : genπJ c ≠ 0 := fun h => hπ.ne_zero
      (Jou.algebraMap_injective (c := genRow c) (l := 0) hπ.ne_zero (by rw [map_zero]; exact h))
    rw [← Ideal.span_singleton_prime hne, ← Ideal.Quotient.isDomain_iff_prime]
    have : IsDomain (MvPolynomial (Fin (r + 1)) B ⧸ Ideal.span {genπ c}) :=
      (Ideal.Quotient.isDomain_iff_prime _).2 ((Ideal.span_singleton_prime hπ.ne_zero).2 hπ)
    have hm : (Ideal.Quotient.mk (Ideal.span {genπ c}) ∘ genRow c) 1 ≠ 0 := by
      simp only [Function.comp_apply, ne_eq, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact not_dvd_genπ c hc0 hc0
    have := Jou.isDomain (c := Ideal.Quotient.mk (Ideal.span {genπ c}) ∘ genRow c) (l := 1) hm
    exact (Jou.quotEquiv (genRow c) (genπ c)).toMulEquiv.isDomain_iff.2 inferInstance
  -- `J_{B[λ]}(π, c)[1/π]` is a polynomial ring over `B[λ][1/π]`
  let L := Jou.LocP (genRow c) 0
  let _ : Algebra (genJ c) L := (Jou.elimLoc (genRow c) 0).toAlgebra
  have : IsLocalization.Away (genπJ c) L := Jou.isLocalization_elim (genRow c) 0
  have hS : Submonoid.powers (genπ c) ≤ nonZeroDivisors (MvPolynomial (Fin (r + 1)) B) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero
  have : IsDomain (Localization.Away (genπ c)) := IsLocalization.isDomain_localization hS
  have hGL0 := hasGcd_of_isLocalization (Submonoid.powers (genπ c))
    (Localization.Away (genπ c)) hGB' hzB'
  have hzL0 := localization_eq_zero_or hzB' _ hS (Localization.Away (genπ c))
  have hGL : HasGcd L := (hasGcd_mvPolynomial hGL0 hzL0 (r + 1)).1
  -- zero test and valuation on `J_{B[λ]}(π, c)`
  have hzD : ∀ z : genJ c, z = 0 ∨ z ≠ 0 :=
    eq_zero_or_of_ringEquiv (genEquiv c).symm (mvPolynomial_eq_zero_or hzJ (r + 1 + 1))
  have hND : IndNoeth (genJ c) := IndNoeth.of_surjective (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective ((hN.mvPolynomial (r + 1)) (r + 1 + 1))
  have hval : ∀ a : genJ c, a ≠ 0 → ∃ n : ℕ, ∃ x, a = genπJ c ^ n * x ∧ ¬ genπJ c ∣ x :=
    fun a ha => match hND with
      | .step h => (h a).exists_val hπD.not_isUnit hdvd a [] rfl ha
          (fun _ hx => absurd hx List.not_mem_nil)
  -- Nagata at `π`, then descent along the substitution
  have hGD : HasGcd (genJ c) := hasGcd_of_away hπD L hzD hval hGL
  exact hasGcd_of_mvPolynomial hzJ (hasGcd_of_ringEquiv (genEquiv c) hGD)

end Main

end BezoutCounterexample.Constructive
