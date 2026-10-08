import BezoutCounterexample.Constructive.MinPrime

/-!
# Explicit points: an effective Nullstellensatz (option 2, M4/(G2))

* `NullJac n`: for an explicit prime `P` of `Rₙ = ℚ[Y₁, …, Yₙ]` and `a ∉ P`, a point `z : Rₙ → L` into
  a finite factorial extension `L/ℚ` (a tower of `AdjoinRoot`s) with `z(P) = 0` and `z(a) ≠ 0`
  (`HasPoint`). Induction on `n` (`jac`), the step with the data of Perdry's step (`Lasker`):
  `P' = P ∩ R` prime with factorial `K = Frac(R ⧸ P')`, `G = φ ĝ`.
  - `G = 0`: `P = P' R[X]`; a point `z'` of `R` with `z'(c) ≠ 0` (`c` the leading coefficient of
    `φ a`), then `X ↦ k ∈ ℕ` a non-root of `z'(a)` (`exists_nat_nonroot`).
  - `G ≠ 0`: `G` is irreducible (`P` prime), `UG + V φ(a) = 1`; with denominators `d₁, d₂` and the
    leading coefficient `ℓ` of the truncation `u'` of `ĝ` (`pseudo_rep`), a point `z'` with
    `z'(d₁ d₂ ℓ) ≠ 0`; `X ↦` a root of an irreducible factor of `z'(u')` over `L'` (M2). Elements of
    `P` vanish by pseudo-division, `a` does not by the Bézout relation.
* The point is onto `L` (`L = ℚ[z(Y₁), …, z(Yₙ)]`): each `AdjoinRoot` step adjoins exactly the
  image of `X`; so `ker z` is maximal in the positive sense (inverses are images).
* `HasPres.exists_point`: the Nullstellensatz with explicit points for a presented ring: if
  `1 ∉ (l)`, a ring hom `z : A → L`, `L/ℚ` finite with a zero test, vanishing on `l` (minimal prime
  over the lifted list and the relations, then `NullJac`, then descent along the presentation).
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open Polynomial

section Aux

/-- A non-root among `0, 1, …, deg p`. -/
lemma exists_nat_nonroot {F : Type*} [Field F] [CharZero F] (hz : ∀ x : F, x = 0 ∨ x ≠ 0)
    {p : F[X]} (hp : p ≠ 0) : ∃ k : ℕ, p.eval (k : F) ≠ 0 := by
  have hdec : ∀ k : Fin (p.natDegree + 1), p.eval ((k : ℕ) : F) ≠ 0 ∨ ¬ p.eval ((k : ℕ) : F) ≠ 0 :=
    fun k => (hz _).elim (fun h => Or.inr fun h' => h' h) Or.inl
  rcases Finset.exists_or_forall_not' (Finset.univ : Finset (Fin (p.natDegree + 1))) hdec with
    ⟨k, -, hk⟩ | hall
  · exact ⟨k, hk⟩
  · exfalso
    apply hp
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (f := fun k : Fin (p.natDegree + 1) => ((k : ℕ) : F))
      (fun a b h => Fin.ext (Nat.cast_injective h)) (fun k => ?_) (by simp)
    rcases hz (p.eval ((k : ℕ) : F)) with h | h
    · exact h
    · exact absurd h (hall k (Finset.mem_univ _))

/-- A nonconstant polynomial over a factorial field has an irreducible factor. -/
lemma FactorialField.exists_irreducible_dvd {F : Type*} [Field F] (hF : FactorialField F)
    {g : F[X]} (hg : 0 < g.natDegree) : ∃ p, Irreducible p ∧ p ∣ g := by
  have hg0 : g ≠ 0 := fun h => by rw [h, natDegree_zero] at hg; exact lt_irrefl 0 hg
  obtain ⟨u, l, hu, hl, hgl⟩ := hF.exists_factorisation hg0
  cases l with
  | nil =>
    rw [List.prod_nil, mul_one] at hgl
    rw [hgl, natDegree_eq_zero_of_isUnit hu] at hg
    exact absurd hg (lt_irrefl 0)
  | cons p l =>
    refine ⟨p, hl p (List.mem_cons_self ..), ?_⟩
    rw [hgl, List.prod_cons]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _

end Aux

/-- A point killing `P` and not `a`, in a finite factorial extension of `ℚ`. -/
def HasPoint {n : ℕ} (P : List (MvPolynomial (Fin n) ℚ)) (a : MvPolynomial (Fin n) ℚ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L) (_ : CharZero L)
    (_ : FactorialField L) (z : MvPolynomial (Fin n) ℚ →+* L),
    (∀ x ∈ lspan P, z x = 0) ∧ z a ≠ 0 ∧ Function.Surjective z

/-- The effective Nullstellensatz in Jacobson form. -/
def NullJac (n : ℕ) : Prop :=
  ∀ P : List (MvPolynomial (Fin n) ℚ), (lspan P).IsPrime → ∀ a, a ∉ lspan P → HasPoint P a

section Step

variable {n : ℕ} {L : List (MvPolynomial (Fin n) ℚ)} {K : Type} [Field K]
  [Algebra (MvPolynomial (Fin n) ℚ ⧸ lspan L) K] [IsFractionRing (MvPolynomial (Fin n) ℚ ⧸ lspan L) K]

/-- The pseudo-division representation behind `saturation`. -/
theorem pseudo_rep (hzK : ∀ x : K, x = 0 ∨ x ≠ 0) {g : MvPolynomial (Fin (n + 1)) ℚ}
    (hdeg : 0 < (phi L (K := K) g).natDegree) :
    ∃ u' : (MvPolynomial (Fin n) ℚ)[X], u'.map (iota L) = phi L (K := K) g ∧
      u'.natDegree = (phi L (K := K) g).natDegree ∧ u'.leadingCoeff ∉ lspan L ∧
      ∀ f, phi L (K := K) g ∣ phi L f → ∃ (m : ℕ) (q r : (MvPolynomial (Fin n) ℚ)[X]),
        C u'.leadingCoeff ^ m * MvPolynomial.finSuccEquiv ℚ n f = q * u' + r ∧
          r.map (iota L (K := K)) = 0 := by
  set E := MvPolynomial.finSuccEquiv ℚ n
  set G := phi L (K := K) g with hG
  set d := G.natDegree
  set u := E g
  set a := u.coeff d
  have hcoeff : ∀ i, G.coeff i = iota L (K := K) (u.coeff i) := fun i => by
    rw [hG, phi_apply, coeff_map]
  have ha : iota L (K := K) a = G.leadingCoeff := (hcoeff d).symm
  have ha0 : a ∉ lspan L := fun h => by
    have : G.leadingCoeff = 0 := by rw [← ha, (iota_eq_zero (K := K)).2 h]
    rw [leadingCoeff_eq_zero] at this
    have hd0 : d = 0 := by simp only [d, this, natDegree_zero]
    omega
  set u' := truncAt u d
  have hmap : u'.map (iota L) = G := by
    ext i
    rw [coeff_map, coeff_truncAt]
    split_ifs with h
    · exact (hcoeff i).symm
    · rw [map_zero, coeff_eq_zero_of_natDegree_lt (not_le.1 h)]
  have ha' : a ≠ 0 := fun h => ha0 (h ▸ Ideal.zero_mem _)
  have hu'd : u'.natDegree = d := le_antisymm (natDegree_truncAt_le u d)
    (le_natDegree_of_ne_zero (by rw [coeff_truncAt, if_pos le_rfl]; exact ha'))
  have hlc : u'.leadingCoeff = a := by
    rw [leadingCoeff, hu'd, coeff_truncAt, if_pos le_rfl]
  have hzR : ∀ x : MvPolynomial (Fin n) ℚ, x = 0 ∨ x ≠ 0 := (hasPres_mvPolynomial n).zeroTest
  refine ⟨u', hmap, hu'd, by rw [hlc]; exact ha0, fun f hf => ?_⟩
  obtain ⟨m, q, r, hqr, hr⟩ := pseudo_div hzR (g := u') (by rw [hu'd]; exact hdeg) (E f)
  refine ⟨m, q, r, hqr, ?_⟩
  rw [hlc] at hqr
  have hdvd : G ∣ r.map (iota L) := by
    have h1 := congrArg (Polynomial.map (iota L (K := K))) hqr
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, map_C,
      hmap, ← phi_apply] at h1
    have h2 : r.map (iota L) = C (iota L a) ^ m * phi L f - q.map (iota L) * G := by
      rw [h1]; ring
    rw [h2]
    exact dvd_sub (dvd_mul_of_dvd_right hf _) (dvd_mul_left _ _)
  rcases polynomial_eq_zero_or hzK (r.map (iota L)) with h0 | h0
  · exact h0
  exfalso
  have := natDegree_le_of_dvd hdvd h0
  have := natDegree_map_le (f := iota L (K := K)) (p := r)
  rw [hu'd] at hr
  omega

variable [(lspan L).IsPrime] {I : List (MvPolynomial (Fin (n + 1)) ℚ)}

/-- **The step of the Nullstellensatz.** -/
theorem nullJac_step (IH : NullJac n) (hFF : FactorialField K) [CharZero K]
    (hLI : ∀ h, jY h ∈ lspan I ↔ h ∈ lspan L) (hI : (lspan I).IsPrime)
    {a : MvPolynomial (Fin (n + 1)) ℚ} (ha : a ∉ lspan I) : HasPoint I a := by
  letI : Nontrivial K := DivisionRing.toNontrivial
  have hP : (lspan L).IsPrime := inferInstance
  have hzK := hFF.zero
  set E := MvPolynomial.finSuccEquiv ℚ n
  obtain ⟨g₀, hg₀d, hg₀m⟩ := exists_gcd_list hzK (I.map (phi L (K := K)))
  obtain ⟨g, hg, d₀, hd₀, hG⟩ := exists_mem_of_mem_span hg₀m
  set G := phi L (K := K) g with hGdef
  have hd₀' : iota L (K := K) d₀ ≠ 0 := fun h => hd₀ ((iota_eq_zero (K := K)).1 h)
  have hCu : IsUnit (C (iota L (K := K) d₀)) := (IsUnit.mk0 _ hd₀').map C
  have hGdvd : ∀ f ∈ lspan I, G ∣ phi L (K := K) f := by
    intro f hf
    have h1 : g₀ ∣ phi L (K := K) f := dvd_of_mem_lspan hg₀d (mem_lspan_map _ hf)
    rw [hG]; exact (hCu.mul_left_dvd).2 h1
  have hker := ker_le I hLI
  -- coefficients killed by `ι` are killed by any point of `P'`
  have hkillz : ∀ {L' : Type} [Field L'] (z' : MvPolynomial (Fin n) ℚ →+* L'),
      (∀ x ∈ lspan L, z' x = 0) → ∀ v : (MvPolynomial (Fin n) ℚ)[X],
        v.map (iota L (K := K)) = 0 → v.map z' = 0 := by
    intro L' _ z' hz' v hv
    ext i
    rw [coeff_map, coeff_zero]
    apply hz'
    rw [← iota_eq_zero (K := K)]
    have := congrArg (fun p => p.coeff i) hv
    simpa [coeff_map] using this
  rcases polynomial_eq_zero_or hzK G with hG0 | hG0
  · -- `P = P' R[X]`
    have hφa : phi L (K := K) a ≠ 0 := fun h => ha (hker ((mem_ker_phi (K := K) a).1 h))
    set c := (E a).coeff (phi L (K := K) a).natDegree
    have hc : iota L (K := K) c ≠ 0 := by
      have := leadingCoeff_ne_zero.2 hφa
      rwa [leadingCoeff, phi_apply, coeff_map] at this
    have hcP : c ∉ lspan L := fun h => hc ((iota_eq_zero (K := K)).2 h)
    obtain ⟨L', iF, iA, iFD, iC, hFF', z', hz'P, hz'c, hz's⟩ := IH L hP c hcP
    set A' := (E a).map z'
    have hA' : A' ≠ 0 := fun h => hz'c (by
      have := congrArg (fun p => p.coeff (phi L (K := K) a).natDegree) h
      simpa [A', coeff_map] using this)
    obtain ⟨k, hk⟩ := exists_nat_nonroot hFF'.zero hA'
    let z : MvPolynomial (Fin (n + 1)) ℚ →+* L' :=
      (evalRingHom (k : L')).comp ((mapRingHom z').comp
        (E : MvPolynomial (Fin (n + 1)) ℚ →+* (MvPolynomial (Fin n) ℚ)[X]))
    refine ⟨L', iF, iA, iFD, iC, hFF', z, fun x hx => ?_, ?_, fun y => ?_⟩
    · have hφx : phi L (K := K) x = 0 := by
        have := hGdvd x hx; rw [hG0] at this; exact zero_dvd_iff.1 this
      have : (E x).map z' = 0 := hkillz z' hz'P _ (by rw [← phi_apply]; exact hφx)
      show ((E x).map z').eval (k : L') = 0
      rw [this, eval_zero]
    · simpa [z, A'] using hk
    · obtain ⟨x, rfl⟩ := hz's y
      exact ⟨jY x, by simp [z, E, finSuccEquiv_jY]⟩
  -- `G ≠ 0`
  have hcoef : ∀ i, G.coeff i = iota L (K := K) ((E g).coeff i) := fun i => by
    rw [hGdef, phi_apply, coeff_map]
  have hdegG : 0 < G.natDegree := by
    rcases Nat.eq_zero_or_pos G.natDegree with h0 | h0
    · exfalso
      have hGC : G = C (G.coeff 0) := eq_C_of_natDegree_eq_zero h0
      have hdiff : g - jY ((E g).coeff 0) ∈ lspan I := hker ((mem_ker_phi (K := K) _).1 (by
        rw [map_sub, phi_jY, ← hcoef 0, ← hGdef, ← hGC, sub_self]))
      have hc0I : jY ((E g).coeff 0) ∈ lspan I := by
        have := Ideal.sub_mem _ hg hdiff; rwa [sub_sub_cancel] at this
      apply hG0
      rw [hGC, hcoef 0, (iota_eq_zero (K := K)).2 ((hLI _).1 hc0I), C_0]
    · exact h0
  obtain ⟨as, has, -, hsat⟩ := saturation hzK hLI hg hdegG
  have has' : iota L (K := K) as ≠ 0 := fun h => has ((iota_eq_zero (K := K)).1 h)
  have hjas : ∀ m : ℕ, jY as ^ m ∉ lspan I := fun m h =>
    has ((hLI as).1 (hI.mem_of_pow_mem _ h))
  -- `G` is irreducible since `P` is prime
  have hirr : Irreducible G := by
    rcases hFF.irreducible_or_split hdegG with h | ⟨G₁, G₂, h12, hG₁, hG₂⟩
    · exact h
    exfalso
    obtain ⟨u₁, d₁, hd₁, hu₁⟩ := exists_lift_phi (L := L) (K := K) G₁
    obtain ⟨u₂, d₂, hd₂, hu₂⟩ := exists_lift_phi (L := L) (K := K) G₂
    have hd₁' : iota L (K := K) d₁ ≠ 0 := fun h => hd₁ ((iota_eq_zero (K := K)).1 h)
    have hd₂' : iota L (K := K) d₂ ≠ 0 := fun h => hd₂ ((iota_eq_zero (K := K)).1 h)
    have hG₁0 : G₁ ≠ 0 := fun h => by rw [h, natDegree_zero] at hG₁; exact lt_irrefl 0 hG₁
    have hG₂0 : G₂ ≠ 0 := fun h => by rw [h, natDegree_zero] at hG₂; exact lt_irrefl 0 hG₂
    have hdeg12 := natDegree_mul hG₁0 hG₂0
    rw [← h12] at hdeg12
    have hne : ∀ (w : MvPolynomial (Fin (n + 1)) ℚ) (c : K) (H : K[X]), c ≠ 0 →
        phi L (K := K) w = C c * H → H ≠ 0 → H.natDegree < G.natDegree → w ∉ lspan I := by
      intro w c H hc hw hH hlt hwI
      have h1 := hGdvd w hwI
      rw [hw] at h1
      have := natDegree_le_of_dvd h1 (mul_ne_zero (by simpa using hc) hH)
      rw [natDegree_C_mul hc] at this
      omega
    have hdvd : G ∣ phi L (K := K) (u₁ * u₂) :=
      ⟨C (iota L d₁) * C (iota L d₂), by rw [map_mul, hu₁, hu₂, h12]; ring⟩
    obtain ⟨m, hm⟩ := hsat _ hdvd
    rcases hI.mem_or_mem (show (jY as ^ m * u₁) * u₂ ∈ lspan I by rw [mul_assoc]; exact hm)
      with h | h
    · refine hne _ (iota L as ^ m * iota L d₁) G₁ (mul_ne_zero (pow_ne_zero _ has') hd₁') ?_
        hG₁0 (by omega) h
      rw [map_mul, map_pow, phi_jY, hu₁, C_mul, C_pow]; ring
    · exact hne u₂ _ G₂ hd₂' hu₂ hG₂0 (by omega) h
  -- `G ∤ φ a`
  have hGa : ¬ G ∣ phi L (K := K) a := fun h => by
    obtain ⟨m, hm⟩ := hsat a h
    rcases hI.mem_or_mem hm with h1 | h1
    · exact hjas m h1
    · exact ha h1
  obtain ⟨U, V, hUV⟩ := (hirr.coprime_iff_not_dvd).2 hGa
  obtain ⟨Uh, d₁, hd₁, hUh⟩ := exists_lift_phi (L := L) (K := K) U
  obtain ⟨Vh, d₂, hd₂, hVh⟩ := exists_lift_phi (L := L) (K := K) V
  set w := Uh * g * jY d₂ + Vh * a * jY d₁ - jY (d₁ * d₂) with hw
  have hφw : phi L (K := K) w = 0 := by
    rw [hw, map_sub, map_add, map_mul, map_mul, map_mul, map_mul, phi_jY, phi_jY, phi_jY, hUh, hVh,
      ← hGdef, map_mul, C_mul]
    linear_combination (C (iota L (K := K) d₁) * C (iota L (K := K) d₂)) * hUV
  obtain ⟨u', hu'map, hu'deg, hℓ, hrep⟩ := pseudo_rep hzK hdegG
  set ℓ := u'.leadingCoeff
  have he : d₁ * d₂ * ℓ ∉ lspan L := fun h => by
    rcases hP.mem_or_mem h with h | h
    · exact (hP.mem_or_mem h).elim hd₁ hd₂
    · exact hℓ h
  obtain ⟨L', iF, iA, iFD, iC, hFF', z', hz'P, hz'e, hz's⟩ := IH L hP _ he
  have hz1 : z' d₁ ≠ 0 := fun h => hz'e (by rw [map_mul, map_mul, h]; ring)
  have hz2 : z' d₂ ≠ 0 := fun h => hz'e (by rw [map_mul, map_mul, h]; ring)
  have hzℓ : z' ℓ ≠ 0 := fun h => hz'e (by rw [map_mul, h, mul_zero])
  set g' := u'.map z'
  have hg'deg : g'.natDegree = u'.natDegree := natDegree_map_of_leadingCoeff_ne_zero z' hzℓ
  obtain ⟨p, hp, hpg⟩ := hFF'.exists_irreducible_dvd (g := g')
    (by rw [hg'deg, hu'deg]; exact hdegG)
  haveI : Fact (Irreducible p) := ⟨hp⟩
  letI : Nontrivial (AdjoinRoot p) := DivisionRing.toNontrivial
  let h : (MvPolynomial (Fin n) ℚ)[X] →+* AdjoinRoot p :=
    eval₂RingHom ((AdjoinRoot.of p).comp z') (AdjoinRoot.root p)
  have hh : ∀ v, h v = AdjoinRoot.mk p (v.map z') := fun v => by
    show v.eval₂ ((AdjoinRoot.of p).comp z') (AdjoinRoot.root p) = _
    rw [← eval₂_map, ← AdjoinRoot.aeval_eq, aeval_def, AdjoinRoot.algebraMap_eq]
  have hkill : ∀ v, v.map (iota L (K := K)) = 0 → h v = 0 := fun v hv => by
    rw [hh, hkillz z' hz'P v hv, map_zero]
  have hu'0 : h u' = 0 := by rw [hh]; exact AdjoinRoot.mk_eq_zero.2 hpg
  have hEg : h (E g) = 0 := by
    have : E g = u' + (E g - u') := by ring
    rw [this, map_add, hu'0, zero_add]
    exact hkill _ (by rw [Polynomial.map_sub, ← phi_apply, hu'map, sub_self])
  have hof : ∀ c, h (C c) = AdjoinRoot.of p (z' c) := fun c => by
    show (C c).eval₂ _ _ = _; rw [eval₂_C]; rfl
  have hofinj : Function.Injective (AdjoinRoot.of p) := (AdjoinRoot.of p).injective
  let z : MvPolynomial (Fin (n + 1)) ℚ →+* AdjoinRoot p :=
    h.comp (E : MvPolynomial (Fin (n + 1)) ℚ →+* (MvPolynomial (Fin n) ℚ)[X])
  have hzE : ∀ x, z x = h (E x) := fun _ => rfl
  have hFD : Module.Finite L' (AdjoinRoot p) := (AdjoinRoot.powerBasis hp.ne_zero).finite
  refine ⟨AdjoinRoot p, inferInstance, inferInstance, Module.Finite.trans L' _,
    charZero_of_injective_algebraMap (algebraMap L' (AdjoinRoot p)).injective,
    factorialField_adjoin hFF', z, fun x hx => ?_, ?_, fun y => ?_⟩
  · obtain ⟨m, q, r, hqr, hr⟩ := hrep x (hGdvd x hx)
    have h1 := congrArg h hqr
    rw [map_mul, map_pow, hof, map_add, map_mul, hu'0, mul_zero, zero_add, hkill r hr] at h1
    rw [hzE]
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd (pow_eq_zero_iff'.1 h2).1 ((map_ne_zero_iff _ hofinj).2 hzℓ)
    · exact h2
  · intro hza
    have h1 : h (E w) = 0 := hkill _ (by rw [← phi_apply]; exact hφw)
    have h2 : h (E w) = h (E Uh) * h (E g) * AdjoinRoot.of p (z' d₂) +
        h (E Vh) * h (E a) * AdjoinRoot.of p (z' d₁) - AdjoinRoot.of p (z' (d₁ * d₂)) := by
      have hEj : ∀ c, E (jY c) = C c := finSuccEquiv_jY
      simp only [hw, map_sub, map_add, map_mul, hEj, hof]
    have hza' : h (E a) = 0 := hza
    rw [h2, hEg, hza'] at h1
    simp only [mul_zero, zero_mul, zero_add, zero_sub, neg_eq_zero] at h1
    exact (map_ne_zero_iff _ hofinj).2 (by rw [map_mul]; exact mul_ne_zero hz1 hz2) h1
  · obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
    obtain ⟨v, rfl⟩ := Polynomial.map_surjective z' hz's q
    exact ⟨E.symm v, by rw [hzE, AlgEquiv.apply_symm_apply, hh]⟩

end Step

section Induction

theorem nullJac_zero : NullJac 0 := by
  intro P hP a ha
  let e := MvPolynomial.isEmptyAlgEquiv ℚ (Fin 0)
  have hz : ∀ f : MvPolynomial (Fin 0) ℚ, f = 0 ∨ f ≠ 0 := (hasPres_mvPolynomial 0).zeroTest
  have hunit : ∀ f : MvPolynomial (Fin 0) ℚ, f ≠ 0 → f * e.symm (e f)⁻¹ = 1 := fun f hf =>
    e.injective (by
      rw [map_mul, AlgEquiv.apply_symm_apply, mul_inv_cancel₀ (fun h => hf (e.injective (by
        rw [h, map_zero]))), map_one])
  refine ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, factorialField_rat,
    (e : MvPolynomial (Fin 0) ℚ →+* ℚ), fun x hx => ?_, ?_, fun y => ⟨e.symm y, by simp⟩⟩
  · rcases hz x with h | h
    · rw [h]; exact map_zero _
    · exact absurd ((Ideal.eq_top_iff_one _).2 (hunit x h ▸ Ideal.mul_mem_right _ _ hx))
        hP.ne_top
  · intro h
    have : a = 0 := e.injective (by rw [map_zero]; exact h)
    exact ha (this ▸ Ideal.zero_mem _)

theorem nullJac_succ {n : ℕ} (IH : NullJac n) : NullJac (n + 1) := by
  intro P hP a ha
  obtain ⟨L, hLI⟩ := exists_elim0 P
  have hP' : (lspan L).IsPrime := by
    have : lspan L = (lspan P).comap (jY (n := n)) := by
      ext h; rw [Ideal.mem_comap]; exact (hLI h).symm
    rw [this]; exact Ideal.comap_isPrime _ _
  rcases fln n L with h1 | ⟨x, y, hxy, hx, hy⟩ | ⟨-, K, _, _, hK, hFF, hchar⟩
  · exact absurd ((Ideal.eq_top_iff_one _).2 h1) hP'.ne_top
  · exact absurd (hP'.mem_or_mem hxy) (by rintro (h | h) <;> contradiction)
  · haveI := hP'
    haveI := hchar
    exact nullJac_step IH hFF hLI hP ha

/-- **The effective Nullstellensatz** (Jacobson form, explicit points) for `ℚ[Y₁, …, Yₙ]`. -/
theorem nullJac : ∀ n, NullJac n
  | 0 => nullJac_zero
  | n + 1 => nullJac_succ (nullJac n)

end Induction

/-- **(G2): explicit points of a presented ring.** If `1 ∉ (l)`, a ring hom onto a finite
extension `L/ℚ` with a zero test, vanishing on `l`. -/
theorem HasPres.exists_point {A : Type} [CommRing A] (h : HasPres A) (l : List A)
    (h1 : (1 : A) ∉ lspan l) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L) (z : A →+* L),
      (∀ x : L, x = 0 ∨ x ≠ 0) ∧ (∀ x ∈ l, z x = 0) ∧ Function.Surjective z := by
  obtain ⟨n, G, ⟨e⟩⟩ := h
  let π : MvPolynomial (Fin n) ℚ →+* A := e.toRingHom.comp (Ideal.Quotient.mk _)
  have hπ : Function.Surjective π := e.surjective.comp Ideal.Quotient.mk_surjective
  have hkerπ : ∀ x, π x = 0 ↔ x ∈ lspan G := fun x => by
    simp only [π, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨J, rfl⟩ := exists_list_lift π hπ l
  have hI0 : (lspan (J ++ G)).map π = lspan (J.map π) := by
    rw [← lspan_map, List.map_append]
    refine le_antisymm ?_ (Ideal.span_mono fun x hx => List.mem_append_left _ hx)
    rw [lspan, Ideal.span_le]
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact Ideal.subset_span hx
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
      rw [SetLike.mem_coe, (hkerπ g).2 (Ideal.subset_span hg)]
      exact Ideal.zero_mem _
  have h1' : (1 : MvPolynomial (Fin n) ℚ) ∉ lspan (J ++ G) := fun h' => h1 (by
    rw [← hI0, ← map_one π]; exact Ideal.mem_map_of_mem _ h')
  obtain ⟨P, hIP, ⟨hPp, -⟩, -⟩ := Constructive.exists_minimal_prime (J ++ G) h1'
  have h1P : (1 : MvPolynomial (Fin n) ℚ) ∉ lspan P := fun h => hPp.ne_top
    ((Ideal.eq_top_iff_one _).2 h)
  obtain ⟨L, iF, iA, iFD, -, hFF, z, hzP, -, hzs⟩ := nullJac n P hPp 1 h1P
  have hkz : RingHom.ker π ≤ RingHom.ker z := fun x hx =>
    hzP x (hIP (Ideal.span_mono (fun y hy => List.mem_append_right _ hy) ((hkerπ x).1 hx)))
  -- through the quotient (no section of `π`): `(G) ⊆ ker z`, then `e⁻¹`
  have hGz : ∀ x ∈ lspan G, z x = 0 := fun x hx =>
    RingHom.mem_ker.1 (hkz (RingHom.mem_ker.2 ((hkerπ x).2 hx)))
  let zA : A →+* L := (Ideal.Quotient.lift (lspan G) z hGz).comp e.symm.toRingHom
  have hzA : ∀ x, zA (π x) = z x := fun x => by
    simp only [zA, π, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
  refine ⟨L, iF, iA, iFD, zA, hFF.zero, fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    rw [hzA]
    exact hzP x (hIP (Ideal.subset_span (List.mem_append_left _ hx)))
  · obtain ⟨x, rfl⟩ := hzs y
    exact ⟨π x, hzA x⟩

end BezoutCounterexample.Constructive
