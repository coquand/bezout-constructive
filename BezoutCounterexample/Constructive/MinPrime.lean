import BezoutCounterexample.Constructive.Lasker
import BezoutCounterexample.Constructive.PolyBar
import BezoutCounterexample.Constructive.ChainLiftUnique

/-!
# Minimal primes over an explicit ideal of `ℚ[Y₁, …, Yₙ]` (option 2, M3b; Perdry 2004, Thm 4.4)

* `exists_prime_cover`: for every explicit `I` there is a finite list of explicit primes `Pᵢ ⊇ I`
  (each with a factorial fraction field, `PrimeFF`) such that every prime `Q ⊇ I` contains some
  `Pᵢ`; the list is nonempty when `1 ∉ I`. The split tree of the strong primality test (`fln`):
  at a split `ab ∈ J`, `a, b ∉ J`, recurse on `J + (a)` and `J + (b)`. Termination by bar
  induction on `IndNoeth ℚ[Y]` (`polyBar`): the added elements form a list each of whose entries
  is outside the ideal of the older ones, so the `good` case of `NBar` never occurs.
  Nonemptiness: `1 ∈ J + (a)` and `1 ∈ J + (b)` give `1 ∈ J + (ab) = J`.
* `HasPres.exists_prime_cover`, `HasPres.gens_of_minimalPrime`: the same in a presented ring; every
  minimal prime over an explicit ideal is explicit.
* `exists_minimal_prime`: if `1 ∉ I`, an explicit prime `P ⊇ I` with factorial fraction field
  which is minimal over `I`: every prime `Q` with `I ⊆ Q ⊆ P` equals `P`. A minimal element of
  the finite list for the decidable inclusion (`mem_dec`).
-/

noncomputable section

namespace BezoutCounterexample.Constructive

section General

variable {A : Type*} [CommRing A]

lemma lspan_cons (a : A) (J : List A) :
    lspan (a :: J) = Ideal.span {a} ⊔ lspan J := by
  rw [lspan, lspan, ← Ideal.span_union]
  congr 1
  ext x
  simp [List.mem_cons]

lemma lspan_le_cons' (a : A) (J : List A) : lspan J ≤ lspan (a :: J) := by
  rw [lspan_cons]; exact le_sup_right

lemma mem_lspan_cons_self (a : A) (J : List A) : a ∈ lspan (a :: J) :=
  Ideal.subset_span (List.mem_cons_self ..)

/-- `1 ∈ J + (a)` and `1 ∈ J + (b)` with `ab ∈ J` give `1 ∈ J`. -/
lemma one_mem_of_split {a b : A} {J : List A} (hab : a * b ∈ lspan J)
    (ha : (1 : A) ∈ lspan (a :: J)) (hb : (1 : A) ∈ lspan (b :: J)) : (1 : A) ∈ lspan J := by
  rw [lspan_cons, Submodule.mem_sup] at ha hb
  obtain ⟨x, hx, i, hi, hxi⟩ := ha
  obtain ⟨y, hy, j, hj, hyj⟩ := hb
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have h1 : (1 : A) = r * s * (a * b) + r * a * j + i * (s * b + j) := by
    linear_combination (-(s * b + j)) * hxi - hyj
  rw [h1]
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hab) (Ideal.mul_mem_left _ _ hj))
    (Ideal.mul_mem_right _ _ hi)

/-- Perdry, Lemma 4.3: `xᵐ ∈ J + (a)`, `xᵐ' ∈ J + (b)`, `ab ∈ J` give `x^(m+m') ∈ J`. -/
lemma pow_mem_of_split {a b : A} {J : List A} (hab : a * b ∈ lspan J) {x : A} {m m' : ℕ}
    (ha : x ^ m ∈ lspan (a :: J)) (hb : x ^ m' ∈ lspan (b :: J)) : x ^ (m + m') ∈ lspan J := by
  rw [lspan_cons, Submodule.mem_sup] at ha hb
  obtain ⟨y, hy, i, hi, hxi⟩ := ha
  obtain ⟨y', hy', j, hj, hyj⟩ := hb
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hy'
  have h1 : x ^ (m + m') = r * s * (a * b) + r * a * j + i * (s * b + j) := by
    rw [pow_add, ← hxi, ← hyj]; ring
  rw [h1]
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hab) (Ideal.mul_mem_left _ _ hj))
    (Ideal.mul_mem_right _ _ hi)

/-- A minimal element of a nonempty finite list for a decidable preorder-like relation. -/
lemma exists_minimal {α : Type*} (le : α → α → Prop) (hdec : ∀ x y, le x y ∨ ¬ le x y)
    (htrans : ∀ x y z, le x y → le y z → le x z) :
    ∀ l : List α, l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, le y x → le x y
  | [], h => absurd rfl h
  | [x], _ => ⟨x, List.mem_singleton_self x, fun y hy hyx => by
      rw [List.mem_singleton.1 hy] at hyx ⊢; exact hyx⟩
  | x :: y :: l, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_minimal le hdec htrans (y :: l) (List.cons_ne_nil _ _)
    rcases hdec x m with hxm | hxm
    · -- `x ≤ m`: `x` is minimal
      refine ⟨x, List.mem_cons_self .., fun z hz hzx => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hzx
      · exact htrans _ _ _ hxm (hmin z hz (htrans _ _ _ hzx hxm))
    · refine ⟨m, List.mem_cons_of_mem _ hm, fun z hz hzm => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact absurd hzm hxm
      · exact hmin z hz hzm

end General

section Cover

variable {n : ℕ}

/-- A finite list of explicit primes covering the primes over `I`. -/
def PrimeCover (I : List (MvPolynomial (Fin n) ℚ)) : Prop :=
  ∃ Ps : List (List (MvPolynomial (Fin n) ℚ)),
    (∀ P ∈ Ps, lspan I ≤ lspan P ∧ PrimeFF (lspan P)) ∧
    (∀ Q : Ideal (MvPolynomial (Fin n) ℚ), Q.IsPrime → lspan I ≤ Q → ∃ P ∈ Ps, lspan P ≤ Q) ∧
    ((1 : MvPolynomial (Fin n) ℚ) ∉ lspan I → Ps ≠ []) ∧
    (∀ x, (∀ P ∈ Ps, x ∈ lspan P) → ∃ k : ℕ, x ^ k ∈ lspan I)

/-- Each entry lies outside the ideal of the older entries and `I₀`. -/
def PFree (I₀ : List (MvPolynomial (Fin n) ℚ)) : List (MvPolynomial (Fin n) ℚ) → Prop
  | [] => True
  | a :: l => a ∉ lspan (l ++ I₀) ∧ PFree I₀ l

theorem cover_of_nbar (I₀ : List (MvPolynomial (Fin n) ℚ)) {l : List (MvPolynomial (Fin n) ℚ)}
    (hl : NBar l) : PFree I₀ l → PrimeCover (l ++ I₀) := by
  induction hl with
  | @good a l ha =>
    intro hf
    exact absurd ((Ideal.span_mono fun x hx => List.mem_append_left _ hx) ha) hf.1
  | @step l _ ih =>
    intro hf
    have hdec := (hasPres_mvPolynomial n).mem_dec
    rcases fln n (l ++ I₀) with h1 | ⟨a, b, hab, ha, hb⟩ | hP
    · exact ⟨[], fun _ h => absurd h List.not_mem_nil, fun Q hQ hle =>
        absurd ((Ideal.eq_top_iff_one _).2 (hle h1)) hQ.ne_top, fun h => absurd h1 h,
        fun x _ => ⟨0, by rw [pow_zero]; exact h1⟩⟩
    · obtain ⟨Pa, hPa, hca, hna, hra⟩ := ih a ⟨ha, hf⟩
      obtain ⟨Pb, hPb, hcb, hnb, hrb⟩ := ih b ⟨hb, hf⟩
      simp only [List.cons_append] at hPa hca hna hra hPb hcb hnb hrb
      refine ⟨Pa ++ Pb, fun P hP => ?_, fun Q hQ hle => ?_, fun h1 => ?_, fun x hx => ?_⟩
      · rcases List.mem_append.1 hP with hP | hP
        · exact ⟨(lspan_le_cons' a _).trans (hPa P hP).1, (hPa P hP).2⟩
        · exact ⟨(lspan_le_cons' b _).trans (hPb P hP).1, (hPb P hP).2⟩
      · rcases hQ.mem_or_mem (hle hab) with haQ | hbQ
        · obtain ⟨P, hP, hPQ⟩ := hca Q hQ (by
            rw [lspan_cons]
            exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 haQ) hle)
          exact ⟨P, List.mem_append_left _ hP, hPQ⟩
        · obtain ⟨P, hP, hPQ⟩ := hcb Q hQ (by
            rw [lspan_cons]
            exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hbQ) hle)
          exact ⟨P, List.mem_append_right _ hP, hPQ⟩
      · rcases hdec (a :: (l ++ I₀)) 1 with ha1 | ha1
        · rcases hdec (b :: (l ++ I₀)) 1 with hb1 | hb1
          · exact absurd (one_mem_of_split hab ha1 hb1) h1
          · intro h; exact hnb hb1 (List.append_eq_nil_iff.1 h).2
        · intro h; exact hna ha1 (List.append_eq_nil_iff.1 h).1
      · obtain ⟨m, hm⟩ := hra x fun P hP => hx P (List.mem_append_left _ hP)
        obtain ⟨m', hm'⟩ := hrb x fun P hP => hx P (List.mem_append_right _ hP)
        exact ⟨m + m', pow_mem_of_split hab hm hm'⟩
    · exact ⟨[l ++ I₀], fun P hP' => by rw [List.mem_singleton.1 hP']; exact ⟨le_rfl, hP⟩,
        fun Q _ hle => ⟨l ++ I₀, List.mem_singleton_self _, hle⟩, fun _ => List.cons_ne_nil _ _,
        fun x hx => ⟨1, by rw [pow_one]; exact hx _ (List.mem_singleton_self _)⟩⟩

/-- **Primes over `I` are covered by finitely many explicit primes** (Perdry, Thm 4.4). -/
theorem exists_prime_cover (I : List (MvPolynomial (Fin n) ℚ)) : PrimeCover I := by
  have := cover_of_nbar I (polyBar n) trivial
  simpa using this

/-- **An explicit minimal prime** over an explicit proper ideal, with factorial fraction field. -/
theorem exists_minimal_prime (I : List (MvPolynomial (Fin n) ℚ))
    (h1 : (1 : MvPolynomial (Fin n) ℚ) ∉ lspan I) :
    ∃ P : List (MvPolynomial (Fin n) ℚ), lspan I ≤ lspan P ∧ PrimeFF (lspan P) ∧
      ∀ Q : Ideal (MvPolynomial (Fin n) ℚ), Q.IsPrime → lspan I ≤ Q → Q ≤ lspan P →
        Q = lspan P := by
  obtain ⟨Ps, hPs, hcov, hne, -⟩ := exists_prime_cover I
  have hdec := (hasPres_mvPolynomial n).mem_dec
  let le : List (MvPolynomial (Fin n) ℚ) → List (MvPolynomial (Fin n) ℚ) → Prop :=
    fun P P' => lspan P ≤ lspan P'
  have hle : ∀ P P', le P P' ∨ ¬ le P P' := by
    intro P P'
    have hdecP : ∀ x, x ∉ lspan P' ∨ ¬ x ∉ lspan P' := fun x =>
      (hdec P' x).elim (fun h => Or.inr fun h' => h' h) Or.inl
    rcases Multiset.exists_or_forall_not' (P : Multiset _) hdecP with ⟨x, hx, hxP⟩ | hall
    · exact Or.inr fun h => hxP (h (Ideal.subset_span (Multiset.mem_coe.1 hx)))
    · refine Or.inl ?_
      show lspan P ≤ lspan P'
      rw [lspan, Ideal.span_le]
      intro x hx
      rcases hdec P' x with h | h
      · exact h
      · exact absurd h (hall x (Multiset.mem_coe.2 hx))
  obtain ⟨P, hP, hmin⟩ := exists_minimal le hle (fun _ _ _ h₁ h₂ => h₁.trans h₂) Ps (hne h1)
  refine ⟨P, (hPs P hP).1, (hPs P hP).2, fun Q hQ hIQ hQP => ?_⟩
  obtain ⟨P', hP', hP'Q⟩ := hcov Q hQ hIQ
  exact le_antisymm hQP ((hmin P' hP' (hP'Q.trans hQP)).trans hP'Q)

/-- Intersection of finitely many explicit ideals. -/
theorem exists_inter_lists {n : ℕ} :
    ∀ Ps : List (List (MvPolynomial (Fin n) ℚ)), ∃ N : List (MvPolynomial (Fin n) ℚ),
      ∀ x, x ∈ lspan N ↔ ∀ P ∈ Ps, x ∈ lspan P
  | [] => ⟨[1], fun x => ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => by
      rw [lspan_singleton, Ideal.span_singleton_one]; trivial⟩⟩
  | P :: Ps => by
    obtain ⟨N, hN⟩ := exists_inter_lists Ps
    obtain ⟨M, hM⟩ := exists_inter_list P N
    refine ⟨M, fun x => ?_⟩
    rw [hM, Submodule.mem_inf, hN]
    exact ⟨fun ⟨h1, h2⟩ Q hQ => (List.mem_cons.1 hQ).elim (fun h => h ▸ h1) (h2 Q),
      fun h => ⟨h P (List.mem_cons_self ..), fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)⟩⟩

/-- **Explicit radical** (Perdry, Prop. 4.1): `√I` is the intersection of the explicit primes. -/
theorem exists_radical {n : ℕ} (I : List (MvPolynomial (Fin n) ℚ)) :
    ∃ N : List (MvPolynomial (Fin n) ℚ), lspan N = (lspan I).radical := by
  obtain ⟨Ps, hPs, -, -, hrad⟩ := exists_prime_cover I
  obtain ⟨N, hN⟩ := exists_inter_lists Ps
  refine ⟨N, le_antisymm (fun x hx => hrad x ((hN x).1 hx)) fun x ⟨k, hk⟩ => ?_⟩
  exact (hN x).2 fun P hP => (hPs P hP).2.1.mem_of_pow_mem k ((hPs P hP).1 hk)

end Cover

section Pres

lemma exists_list_lift {R S : Type*} (f : R → S) (hf : Function.Surjective f) :
    ∀ l : List S, ∃ l' : List R, l'.map f = l
  | [] => ⟨[], rfl⟩
  | y :: l => by
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨l', rfl⟩ := exists_list_lift f hf l
    exact ⟨x :: l', rfl⟩

lemma lspan_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (l : List R) :
    lspan (l.map f) = (lspan l).map f := by
  refine le_antisymm ?_ ?_
  · rw [lspan, Ideal.span_le]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span hx)
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_lspan_map f hx

/-- `PrimeFF` passes along a surjection whose kernel lies in the prime. -/
theorem PrimeFF.map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) {P : Ideal R} (hker : RingHom.ker f ≤ P) (hP : PrimeFF P) :
    PrimeFF (P.map f) := by
  obtain ⟨hPp, K, _, _, hK, hFF, hchar⟩ := hP
  let g : R →+* K := (algebraMap (R ⧸ P) K).comp (Ideal.Quotient.mk P)
  have hg : ∀ r, g r = 0 ↔ r ∈ P := fun r => by
    rw [RingHom.comp_apply, ← Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨fun h => IsFractionRing.injective _ K (by rw [h, map_zero]), fun h => by
      rw [h, map_zero]⟩
  have hkg : RingHom.ker f ≤ RingHom.ker g := fun r hr => (hg r).2 (hker hr)
  -- the induced map `S → K`, by unique choice (its value at `s` does not depend on the preimage)
  have hfg : ∀ r r', f r = f r' → g r = g r' := fun r r' h => by
    have : r - r' ∈ RingHom.ker f := by rw [RingHom.mem_ker, map_sub, h, sub_self]
    have h' := hkg this
    rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at h'
  have hex : ∀ s : S, ∃! k : K, ∃ r, f r = s ∧ g r = k := fun s => by
    obtain ⟨r, rfl⟩ := hf s
    exact ⟨g r, ⟨r, rfl, rfl⟩, fun k ⟨r', hr', hk⟩ => hk ▸ hfg r' r hr'⟩
  let ψf : S → K := fun s => (uniqueChoice (hex s)).1
  have hψf : ∀ r, ψf (f r) = g r := fun r => by
    obtain ⟨r', hr', hk⟩ := (uniqueChoice (hex (f r))).2
    exact hk.symm.trans (hfg r' r hr')
  let ψ : S →+* K :=
    { toFun := ψf
      map_one' := by rw [← map_one f, hψf, map_one]
      map_mul' := fun a b => by
        obtain ⟨x, rfl⟩ := hf a; obtain ⟨y, rfl⟩ := hf b
        rw [← map_mul, hψf, hψf, hψf, map_mul]
      map_zero' := by rw [← map_zero f, hψf, map_zero]
      map_add' := fun a b => by
        obtain ⟨x, rfl⟩ := hf a; obtain ⟨y, rfl⟩ := hf b
        rw [← map_add, hψf, hψf, hψf, map_add] }
  have hψ : ∀ r, ψ (f r) = g r := hψf
  have hmem : ∀ r, f r ∈ P.map f ↔ r ∈ P := fun r => by
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' f hf, sup_of_le_left hker]
  refine primeFF_of_hom ψ (fun s => ?_) (fun z => ?_) hFF hchar
  · obtain ⟨r, rfl⟩ := hf s
    rw [hψ, hg, hmem]
  · obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ P) z
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨f u, f v, ?_, by rw [hψ, hψ]; rfl⟩
    rw [hψ]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ K)).2 (nonZeroDivisors.ne_zero hy)

/-- **An explicit minimal prime in a presented ring**, with factorial fraction field. -/
theorem HasPres.exists_minimal_prime {A : Type} [CommRing A] (h : HasPres A) (I : List A)
    (h1 : (1 : A) ∉ lspan I) :
    ∃ P : List A, lspan I ≤ lspan P ∧ PrimeFF (lspan P) ∧
      ∀ Q : Ideal A, Q.IsPrime → lspan I ≤ Q → Q ≤ lspan P → Q = lspan P := by
  obtain ⟨n, G, ⟨e⟩⟩ := h
  let π : MvPolynomial (Fin n) ℚ →+* A := e.toRingHom.comp (Ideal.Quotient.mk _)
  have hπ : Function.Surjective π := e.surjective.comp Ideal.Quotient.mk_surjective
  have hkerπ : ∀ x, π x = 0 ↔ x ∈ lspan G := fun x => by
    simp only [π, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker π = lspan G := by ext x; exact hkerπ x
  obtain ⟨J, rfl⟩ := exists_list_lift π hπ I
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
  obtain ⟨P, hIP, hPF, hmin⟩ := Constructive.exists_minimal_prime (J ++ G) h1'
  have hGP : lspan G ≤ lspan P :=
    (Ideal.span_mono fun x hx => List.mem_append_right _ hx).trans hIP
  have hcm : Ideal.comap π ((lspan P).map π) = lspan P := by
    rw [Ideal.comap_map_of_surjective' π hπ, hker, sup_of_le_left hGP]
  refine ⟨P.map π, ?_, ?_, fun Q hQ hIQ hQP => ?_⟩
  · rw [lspan_map, lspan_map]
    exact Ideal.map_mono ((Ideal.span_mono fun x hx => List.mem_append_left _ hx).trans hIP)
  · rw [lspan_map]; exact PrimeFF.map π hπ (hker ▸ hGP) hPF
  · have hQ' : (Q.comap π).IsPrime := Ideal.comap_isPrime π Q
    have h1 : lspan (J ++ G) ≤ Q.comap π := by
      rw [lspan, Ideal.span_le]
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hIQ (Ideal.subset_span (List.mem_map_of_mem hx))
      · show π x ∈ Q
        rw [(hkerπ x).2 (Ideal.subset_span hx)]; exact Q.zero_mem
    have h2 : Q.comap π ≤ lspan P := by
      intro x hx
      have : π x ∈ (lspan P).map π := by rw [← lspan_map]; exact hQP hx
      rw [← hcm]; exact this
    have := hmin _ hQ' h1 h2
    rw [lspan_map, ← this, Ideal.map_comap_of_surjective π hπ]

/-- **Explicit prime cover in a presented ring**: finitely many explicit primes over `(l)`
(with factorial fraction fields) such that every prime over `(l)` contains one of them. -/
theorem HasPres.exists_prime_cover {A : Type} [CommRing A] (h : HasPres A) (l : List A) :
    ∃ Ps : List (List A), (∀ P ∈ Ps, lspan l ≤ lspan P ∧ PrimeFF (lspan P)) ∧
      ∀ Q : Ideal A, Q.IsPrime → lspan l ≤ Q → ∃ P ∈ Ps, lspan P ≤ Q := by
  obtain ⟨n, G, ⟨e⟩⟩ := h
  let π : MvPolynomial (Fin n) ℚ →+* A := e.toRingHom.comp (Ideal.Quotient.mk _)
  have hπ : Function.Surjective π := e.surjective.comp Ideal.Quotient.mk_surjective
  have hkerπ : ∀ x, π x = 0 ↔ x ∈ lspan G := fun x => by
    simp only [π, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker π = lspan G := by ext x; exact hkerπ x
  obtain ⟨J, rfl⟩ := exists_list_lift π hπ l
  obtain ⟨Ps, hPs, hcov, -, -⟩ := Constructive.exists_prime_cover (J ++ G)
  refine ⟨Ps.map (fun P => P.map π), fun P' hP' => ?_, fun Q hQ hlQ => ?_⟩
  · obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hP'
    have hJP : lspan J ≤ lspan P :=
      (Ideal.span_mono fun x hx => List.mem_append_left _ hx).trans (hPs P hP).1
    have hGP : lspan G ≤ lspan P :=
      (Ideal.span_mono fun x hx => List.mem_append_right _ hx).trans (hPs P hP).1
    refine ⟨by rw [lspan_map, lspan_map]; exact Ideal.map_mono hJP, ?_⟩
    rw [lspan_map]; exact PrimeFF.map π hπ (hker ▸ hGP) (hPs P hP).2
  · have hQ' : (Q.comap π).IsPrime := Ideal.comap_isPrime π Q
    have h1 : lspan (J ++ G) ≤ Q.comap π := by
      rw [lspan, Ideal.span_le]
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hlQ (Ideal.subset_span (List.mem_map_of_mem hx))
      · show π x ∈ Q
        rw [(hkerπ x).2 (Ideal.subset_span hx)]; exact Q.zero_mem
    obtain ⟨P, hP, hPQ⟩ := hcov _ hQ' h1
    exact ⟨P.map π, List.mem_map_of_mem hP, by
      rw [lspan_map]; exact Ideal.map_le_iff_le_comap.2 hPQ⟩

/-- **Every minimal prime over an explicit ideal of a presented ring is explicit** (and has a
factorial fraction field). -/
theorem HasPres.gens_of_minimalPrime {A : Type} [CommRing A] (h : HasPres A) (l : List A)
    {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (lspan l).minimalPrimes) :
    ∃ pgens : List A, 𝔭 = lspan pgens ∧ PrimeFF 𝔭 := by
  obtain ⟨Ps, hPs, hcov⟩ := h.exists_prime_cover l
  obtain ⟨P, hP, hP𝔭⟩ := hcov 𝔭 h𝔭.1.1 h𝔭.1.2
  have heq : 𝔭 = lspan P := le_antisymm (h𝔭.2 ⟨(hPs P hP).2.1, (hPs P hP).1⟩ hP𝔭) hP𝔭
  exact ⟨P, heq, heq ▸ (hPs P hP).2⟩

/-- **Explicit radical in a presented ring.** -/
theorem HasPres.exists_radical {A : Type} [CommRing A] (h : HasPres A) (l : List A) :
    ∃ N : List A, lspan N = (lspan l).radical := by
  obtain ⟨n, G, ⟨e⟩⟩ := h
  let π : MvPolynomial (Fin n) ℚ →+* A := e.toRingHom.comp (Ideal.Quotient.mk _)
  have hπ : Function.Surjective π := e.surjective.comp Ideal.Quotient.mk_surjective
  have hkerπ : ∀ x, π x = 0 ↔ x ∈ lspan G := fun x => by
    simp only [π, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, map_eq_zero_iff _ e.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker π = lspan G := by ext x; exact hkerπ x
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
  have hcm : Ideal.comap π ((lspan (J ++ G)).map π) = lspan (J ++ G) := by
    rw [Ideal.comap_map_of_surjective' π hπ, hker,
      sup_of_le_left (Ideal.span_mono fun x hx => List.mem_append_right _ hx)]
  obtain ⟨N, hN⟩ := Constructive.exists_radical (J ++ G)
  refine ⟨N.map π, ?_⟩
  rw [lspan_map, hN, ← hI0]
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun x ⟨k, hk⟩ =>
    ⟨k, by rw [← map_pow]; exact Ideal.mem_map_of_mem _ hk⟩) fun y ⟨k, hk⟩ => ?_
  obtain ⟨x, rfl⟩ := hπ y
  have : x ^ k ∈ Ideal.comap π ((lspan (J ++ G)).map π) := by
    rw [Ideal.mem_comap, map_pow]; exact hk
  rw [hcm] at this
  exact Ideal.mem_map_of_mem _ ⟨k, this⟩

end Pres

end BezoutCounterexample.Constructive
