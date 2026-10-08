import BezoutCounterexample.Constructive.MinPrime

/-!
# Explicit component lists (Task D, R2; roadmap `docs/invariant-constructive.md` §4.2 m1–m3, m7)

The minimal primes over an explicit ideal `(l)` of a presented ring form an **explicit list**,
replacing Mathlib's `minimalPrimes` (`Ideal.exists_minimalPrimes_le`,
`Ideal.finite_minimalPrimes_of_isNoetherianRing`, `Ideal.sInf_minimalPrimes`,
`Ideal.radical_eq_sInf`) and the count `Set.ncard`.

* `HasPres.exists_prime_cover_rad`: `HasPres.exists_prime_cover` together with nonemptiness and
  the elementwise radical identity of the Lasker tree (`PrimeCover`): `x` in every entry gives
  `xᵏ ∈ (l)`.
* `exists_antichain`: for a decidable preorder, every finite list contains an antichain of its
  entries which lies below every entry. Only case analysis on decided propositions.
* `IsCompList l Cs`: `Cs` is an explicit list of the minimal primes over `(l)`: every entry is
  a prime with factorial fraction field, minimal over `(l)`; the entries are pairwise distinct;
  every prime over `(l)` contains an entry (completeness); `⋂ Cs ⊆ √(l)` elementwise.
* `HasPres.exists_compList`: such a list exists (deduplication by (G), `HasPres.mem_dec`).
* `IsCompList.mem_iff`, `IsCompList.length_eq`: two component lists have the same entries up to
  ideal equality, hence the same length. `NumComp l k` (the count `c`) is well defined:
  `exists_numComp`, `NumComp.unique`.
* `HasPres.existsUnique_numComp`, `HasPres.existsUnique_compSet`: the `∃!` interface (see the
  section note: unique choice, not `Σ`).
* `IsCompList.one_mem_sup_colon` (m5): the separating element by the elementwise radical identity
  and CRT, with no minimal primes.
* `HasPres.exists_mem_ne_zero`: the first nonzero explicit generator (R6).
* `Comp l`: the component record replacing `h𝔭 : 𝔭 ∈ (lspan l).minimalPrimes` (m7);
  `IsCompList.exists_le` replaces `Ideal.exists_minimalPrimes_le` (m3).
-/

namespace BezoutCounterexample.Constructive

section Antichain

variable {α : Type*} (le : α → α → Prop)

/-- A decided property is decided on a finite list. -/
lemma list_exists_or_forall {P : α → Prop} (hP : ∀ x, P x ∨ ¬ P x) :
    ∀ l : List α, (∃ x ∈ l, P x) ∨ ∀ x ∈ l, ¬ P x
  | [] => Or.inr fun _ h => absurd h List.not_mem_nil
  | y :: l => by
    rcases hP y with hy | hy
    · exact Or.inl ⟨y, List.mem_cons_self .., hy⟩
    · rcases list_exists_or_forall hP l with ⟨x, hx, hPx⟩ | h
      · exact Or.inl ⟨x, List.mem_cons_of_mem _ hx, hPx⟩
      · exact Or.inr fun x hx => (List.mem_cons.1 hx).elim (fun h' => h' ▸ hy) (h x)

/-- Filtering a list by a decided property, as a sublist. -/
lemma exists_sublist_filter {P : α → Prop} (hP : ∀ x, P x ∨ ¬ P x) :
    ∀ l : List α, ∃ l' : List α, l'.Sublist l ∧ (∀ x ∈ l', P x) ∧ ∀ x ∈ l, P x → x ∈ l'
  | [] => ⟨[], List.Sublist.slnil, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h
      List.not_mem_nil⟩
  | y :: l => by
    obtain ⟨l', hs, hP', hc⟩ := exists_sublist_filter hP l
    rcases hP y with hy | hy
    · refine ⟨y :: l', hs.cons_cons y, fun x hx => ?_, fun x hx hPx => ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hy
        · exact hP' x hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hc x hx hPx)
    · refine ⟨l', hs.cons y, hP', fun x hx hPx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact absurd hPx hy
      · exact hc x hx hPx

/-- In a list of pairwise incomparable entries, `le` between entries is symmetric. -/
lemma pairwise_incomp_le {l : List α} (hl : l.Pairwise fun x y => ¬ le x y ∧ ¬ le y x) :
    ∀ {a b : α}, a ∈ l → b ∈ l → le a b → le b a := by
  induction hl with
  | nil => intro a _ ha; exact absurd ha List.not_mem_nil
  | @cons x t hx _ ih =>
    intro a b ha hb hab
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact hab
      · exact absurd hab (hx b hb').1
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd hab (hx a ha').2
      · exact ih ha' hb' hab

/-- **Antichain extraction**: every finite list contains a pairwise incomparable list of its
entries lying below every entry. -/
theorem exists_antichain (hdec : ∀ x y, le x y ∨ ¬ le x y) (hrefl : ∀ x, le x x)
    (htrans : ∀ x y z, le x y → le y z → le x z) :
    ∀ l : List α, ∃ c : List α, (∀ x ∈ c, x ∈ l) ∧ (∀ y ∈ l, ∃ x ∈ c, le x y) ∧
      c.Pairwise fun x y => ¬ le x y ∧ ¬ le y x
  | [] => ⟨[], fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
      List.Pairwise.nil⟩
  | y :: t => by
    obtain ⟨c, hct, hcov, hpw⟩ := exists_antichain hdec hrefl htrans t
    rcases list_exists_or_forall (fun x => hdec x y) c with ⟨x, hx, hxy⟩ | hno
    · refine ⟨c, fun z hz => List.mem_cons_of_mem _ (hct z hz), fun z hz => ?_, hpw⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨x, hx, hxy⟩
      · exact hcov z hz
    · obtain ⟨c', hs, hP, hcP⟩ :=
        exists_sublist_filter (P := fun x => ¬ le y x)
          (fun x => (hdec y x).elim (fun h => Or.inr fun h' => h' h) Or.inl) c
      refine ⟨y :: c', fun z hz => ?_, fun z hz => ?_, ?_⟩
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hct z (hs.subset hz))
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨z, List.mem_cons_self .., hrefl z⟩
        · obtain ⟨x, hx, hxz⟩ := hcov z hz
          rcases hdec y x with hyx | hyx
          · exact ⟨y, List.mem_cons_self .., htrans _ _ _ hyx hxz⟩
          · exact ⟨x, List.mem_cons_of_mem _ (hcP x hx hyx), hxz⟩
      · refine List.Pairwise.cons (fun x hx => ⟨hP x hx, hno x (hs.subset hx)⟩) (hpw.sublist hs)

end Antichain

section Pres

variable {A : Type} [CommRing A]

/-- **Explicit prime cover with the radical identity** in a presented ring: finitely many
explicit primes over `(l)`, with factorial fraction fields, such that every prime over `(l)`
contains one; nonempty when `1 ∉ (l)`; and an element of every entry has a power in `(l)`. -/
theorem HasPres.exists_prime_cover_rad (h : HasPres A) (l : List A) :
    ∃ Ps : List (List A), (∀ P ∈ Ps, lspan l ≤ lspan P ∧ PrimeFF (lspan P)) ∧
      (∀ Q : Ideal A, Q.IsPrime → lspan l ≤ Q → ∃ P ∈ Ps, lspan P ≤ Q) ∧
      ((1 : A) ∉ lspan l → Ps ≠ []) ∧
      ∀ x, (∀ P ∈ Ps, x ∈ lspan P) → ∃ k : ℕ, x ^ k ∈ lspan l := by
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
  obtain ⟨Ps, hPs, hcov, hne, hrad⟩ := Constructive.exists_prime_cover (J ++ G)
  have hGP : ∀ P ∈ Ps, lspan G ≤ lspan P := fun P hP =>
    (Ideal.span_mono fun x hx => List.mem_append_right _ hx).trans (hPs P hP).1
  refine ⟨Ps.map (fun P => P.map π), fun P' hP' => ?_, fun Q hQ hlQ => ?_, fun h1 => ?_,
    fun y hy => ?_⟩
  · obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hP'
    have hJP : lspan J ≤ lspan P :=
      (Ideal.span_mono fun x hx => List.mem_append_left _ hx).trans (hPs P hP).1
    refine ⟨by rw [lspan_map, lspan_map]; exact Ideal.map_mono hJP, ?_⟩
    rw [lspan_map]; exact PrimeFF.map π hπ (hker ▸ hGP P hP) (hPs P hP).2
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
  · have h1' : (1 : MvPolynomial (Fin n) ℚ) ∉ lspan (J ++ G) := fun h' => h1 (by
      rw [← hI0, ← map_one π]; exact Ideal.mem_map_of_mem _ h')
    intro h0
    exact hne h1' (List.map_eq_nil_iff.1 h0)
  · obtain ⟨x, rfl⟩ := hπ y
    obtain ⟨k, hk⟩ := hrad x fun P hP => by
      have hm : π x ∈ (lspan P).map π := by
        rw [← lspan_map]; exact hy _ (List.mem_map_of_mem hP)
      have hcm : Ideal.comap π ((lspan P).map π) = lspan P := by
        rw [Ideal.comap_map_of_surjective' π hπ, hker, sup_of_le_left (hGP P hP)]
      rw [← hcm]; exact hm
    refine ⟨k, ?_⟩
    rw [← hI0, ← map_pow]
    exact Ideal.mem_map_of_mem _ hk

/-- **An explicit list of the minimal primes over `(l)`.** -/
structure IsCompList (l : List A) (Cs : List (List A)) : Prop where
  le : ∀ C ∈ Cs, lspan l ≤ lspan C
  primeFF : ∀ C ∈ Cs, PrimeFF (lspan C)
  minimal : ∀ C ∈ Cs, ∀ Q : Ideal A, Q.IsPrime → lspan l ≤ Q → Q ≤ lspan C → Q = lspan C
  cover : ∀ Q : Ideal A, Q.IsPrime → lspan l ≤ Q → ∃ C ∈ Cs, lspan C ≤ Q
  distinct : Cs.Pairwise fun C C' => lspan C ≠ lspan C'
  rad : ∀ x, (∀ C ∈ Cs, x ∈ lspan C) → ∃ k : ℕ, x ^ k ∈ lspan l
  ne_nil : (1 : A) ∉ lspan l → Cs ≠ []

/-- Inclusion of explicit ideals is decided by (G). -/
lemma HasPres.le_dec (h : HasPres A) (P P' : List A) :
    lspan P ≤ lspan P' ∨ ¬ lspan P ≤ lspan P' := by
  have hdec := h.mem_dec
  rcases list_exists_or_forall (P := fun x => x ∉ lspan P')
    (fun x => (hdec P' x).elim (fun h => Or.inr fun h' => h' h) Or.inl) P with
    ⟨x, hx, hxP⟩ | hall
  · exact Or.inr fun h => hxP (h (Ideal.subset_span hx))
  · refine Or.inl ?_
    rw [lspan, Ideal.span_le]
    intro x hx
    rcases hdec P' x with h | h
    · exact h
    · exact absurd h (hall x hx)

/-- **Component lists exist** (deduplication of the Lasker cover by (G)). -/
theorem HasPres.exists_compList (h : HasPres A) (l : List A) : ∃ Cs, IsCompList l Cs := by
  obtain ⟨Ps, hPs, hcov, hne, hrad⟩ := h.exists_prime_cover_rad l
  obtain ⟨Cs, hCP, hCcov, hpw⟩ := exists_antichain (fun P P' : List A => lspan P ≤ lspan P')
    h.le_dec (fun _ => le_rfl) (fun _ _ _ h₁ h₂ => h₁.trans h₂) Ps
  have hmin : ∀ C ∈ Cs, ∀ Q : Ideal A, Q.IsPrime → lspan l ≤ Q → Q ≤ lspan C →
      Q = lspan C := by
    intro C hC Q hQ hlQ hQC
    obtain ⟨P, hP, hPQ⟩ := hcov Q hQ hlQ
    obtain ⟨C', hC', hC'P⟩ := hCcov P hP
    exact le_antisymm hQC ((pairwise_incomp_le _ hpw hC' hC
      ((hC'P.trans hPQ).trans hQC)).trans (hC'P.trans hPQ))
  refine ⟨Cs, fun C hC => (hPs C (hCP C hC)).1, fun C hC => (hPs C (hCP C hC)).2, hmin,
    fun Q hQ hlQ => ?_, hpw.imp fun {C C'} hn heq => hn.1 (le_of_eq heq),
    fun x hx => hrad x fun P hP => ?_, fun h1 h0 => ?_⟩
  · obtain ⟨P, hP, hPQ⟩ := hcov Q hQ hlQ
    obtain ⟨C, hC, hCP'⟩ := hCcov P hP
    exact ⟨C, hC, hCP'.trans hPQ⟩
  · obtain ⟨C, hC, hCP'⟩ := hCcov P hP
    exact hCP' (hx C hC)
  · obtain ⟨P, hP⟩ := List.exists_mem_of_ne_nil Ps (hne h1)
    obtain ⟨C, hC, -⟩ := hCcov P hP
    rw [h0] at hC
    exact absurd hC List.not_mem_nil

namespace IsCompList

variable {l : List A} {Cs : List (List A)} (hC : IsCompList l Cs)
include hC

lemma isPrime {C : List A} (hCm : C ∈ Cs) : (lspan C).IsPrime := (hC.primeFF C hCm).1

/-- **A prime over `(l)` contains a component** (replaces `Ideal.exists_minimalPrimes_le`). -/
lemma exists_le {Q : Ideal A} (hQ : Q.IsPrime) (hlQ : lspan l ≤ Q) :
    ∃ C ∈ Cs, lspan C ≤ Q := hC.cover Q hQ hlQ

/-- The entries of a component list are exactly the minimal primes over `(l)`. -/
lemma mem_minimalPrimes {C : List A} (hCm : C ∈ Cs) : lspan C ∈ (lspan l).minimalPrimes :=
  ⟨⟨hC.isPrime hCm, hC.le C hCm⟩, fun Q hQ hQC => (hC.minimal C hCm Q hQ.1 hQ.2 hQC).ge⟩

lemma exists_eq_of_mem_minimalPrimes {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ (lspan l).minimalPrimes) :
    ∃ C ∈ Cs, lspan C = 𝔭 := by
  obtain ⟨C, hCm, hC𝔭⟩ := hC.cover 𝔭 h𝔭.1.1 h𝔭.1.2
  exact ⟨C, hCm, le_antisymm hC𝔭 (h𝔭.2 ⟨hC.isPrime hCm, hC.le C hCm⟩ hC𝔭)⟩

/-- An entry of one component list is (as an ideal) an entry of any other. -/
lemma exists_eq {Ds : List (List A)} (hD : IsCompList l Ds) {C : List A} (hCm : C ∈ Cs) :
    ∃ D ∈ Ds, lspan D = lspan C := by
  obtain ⟨D, hDm, hDC⟩ := hD.cover _ (hC.isPrime hCm) (hC.le C hCm)
  exact ⟨D, hDm, hC.minimal C hCm _ (hD.isPrime hDm) (hD.le D hDm) hDC⟩

lemma nodup_map : (Cs.map lspan).Nodup := by
  rw [List.Nodup, List.pairwise_map]; exact hC.distinct

/-- **The count is well defined**: two component lists have the same length. -/
theorem length_eq {Ds : List (List A)} (hD : IsCompList l Ds) : Cs.length = Ds.length := by
  have hsub : ∀ {Xs Ys : List (List A)}, IsCompList l Xs → IsCompList l Ys →
      Xs.map lspan ⊆ Ys.map lspan := by
    intro Xs Ys hX hY 𝔭 h𝔭
    obtain ⟨C, hCm, rfl⟩ := List.mem_map.1 h𝔭
    obtain ⟨D, hDm, hDC⟩ := hX.exists_eq hY hCm
    exact List.mem_map.2 ⟨D, hDm, hDC⟩
  have h1 := hC.nodup_map.length_le_of_subset (hsub hC hD)
  have h2 := hD.nodup_map.length_le_of_subset (hsub hD hC)
  rw [List.length_map, List.length_map] at h1 h2
  exact le_antisymm h1 h2

/-- **Radical identity**: `⋂ Cs = √(l)`, elementwise. -/
lemma mem_all_iff (x : A) : (∀ C ∈ Cs, x ∈ lspan C) ↔ ∃ k : ℕ, x ^ k ∈ lspan l :=
  ⟨hC.rad x, fun ⟨k, hk⟩ C hCm => (hC.isPrime hCm).mem_of_pow_mem k (hC.le C hCm hk)⟩

end IsCompList

/-- `c = k`: the number of components of `V(l)` is `k`. -/
def NumComp (l : List A) (k : ℕ) : Prop := ∃ Cs, IsCompList l Cs ∧ Cs.length = k

theorem HasPres.exists_numComp (h : HasPres A) (l : List A) : ∃ k, NumComp l k := by
  obtain ⟨Cs, hC⟩ := h.exists_compList l
  exact ⟨Cs.length, Cs, hC, rfl⟩

theorem NumComp.unique {l : List A} {k k' : ℕ} (h : NumComp l k) (h' : NumComp l k') : k = k' := by
  obtain ⟨Cs, hC, rfl⟩ := h
  obtain ⟨Ds, hD, rfl⟩ := h'
  exact hC.length_eq hD

/-! ### Uniquely determined values (`∃!`), for unique choice downstream

The constructions above are proofs of `∃` in `Prop`, by case analysis on decided disjunctions
(`Or`), so they cannot be turned into `Σ`-valued functions. **Option chosen for the interface of
`towerResult` (Task A): `∃!`.** The count and the set of component ideals are uniquely determined,
and Task A extracts them by unique choice. A component *list* is unique only up to order and
choice of generators, so data built from a component (the next ring) should be built from the
uniquely determined ideal, or proved independent of the generators. -/

theorem HasPres.existsUnique_numComp (h : HasPres A) (l : List A) : ∃! k, NumComp l k := by
  obtain ⟨k, hk⟩ := h.exists_numComp l
  exact ⟨k, hk, fun k' hk' => hk'.unique hk⟩

/-- The set of components `{𝔭₁, …, 𝔭ᵣ}` is uniquely determined. -/
theorem HasPres.existsUnique_compSet (h : HasPres A) (l : List A) :
    ∃! S : Set (Ideal A), ∃ Cs, IsCompList l Cs ∧ ∀ 𝔭, 𝔭 ∈ S ↔ ∃ C ∈ Cs, lspan C = 𝔭 := by
  obtain ⟨Cs, hC⟩ := h.exists_compList l
  refine ⟨{𝔭 | ∃ C ∈ Cs, lspan C = 𝔭}, ⟨Cs, hC, fun _ => Iff.rfl⟩, ?_⟩
  rintro S ⟨Ds, hD, hS⟩
  ext 𝔭
  rw [hS]
  constructor
  · rintro ⟨D, hDm, rfl⟩
    obtain ⟨C, hCm, hCD⟩ := hD.exists_eq hC hDm
    exact ⟨C, hCm, hCD⟩
  · rintro ⟨C, hCm, rfl⟩
    exact hC.exists_eq hD hCm

/-! ### The separating element (m5): `⋂ 𝔭ᵢ ⊆ √P` elementwise, plus CRT -/

/-- CRT step: if `C` is comaximal with every entry of `Ds` not equal to it, there is `e ≡ 1`
modulo `C` with `e · C` inside every entry of `Ds`. -/
lemma exists_sep_aux (C : List A) : ∀ Ds : List (List A),
    (∀ D ∈ Ds, lspan D = lspan C ∨ (1 : A) ∈ lspan C ⊔ lspan D) →
    ∃ e : A, 1 - e ∈ lspan C ∧ ∀ D ∈ Ds, ∀ y ∈ lspan C, e * y ∈ lspan D
  | [], _ => ⟨1, by rw [sub_self]; exact Ideal.zero_mem _, fun _ h => absurd h List.not_mem_nil⟩
  | D :: Ds, hc => by
    obtain ⟨e, he, hDs⟩ := exists_sep_aux C Ds fun D' hD' => hc D' (List.mem_cons_of_mem _ hD')
    rcases hc D (List.mem_cons_self ..) with heq | h1
    · refine ⟨e, he, fun D' hD' y hy => ?_⟩
      rcases List.mem_cons.1 hD' with rfl | hD'
      · rw [heq]; exact Ideal.mul_mem_left _ _ hy
      · exact hDs D' hD' y hy
    · obtain ⟨c, hc', d, hd, hcd⟩ := Submodule.mem_sup.1 h1
      refine ⟨e * d, ?_, fun D' hD' y hy => ?_⟩
      · have : 1 - e * d = (1 - e) + e * c := by linear_combination (-e) * hcd
        rw [this]
        exact Ideal.add_mem _ he (Ideal.mul_mem_left _ _ hc')
      · rcases List.mem_cons.1 hD' with rfl | hD'
        · rw [show e * d * y = e * y * d by ring]
          exact Ideal.mul_mem_left _ _ hd
        · rw [mul_assoc, mul_left_comm]
          exact Ideal.mul_mem_left _ _ (hDs D' hD' y hy)

/-- **The separating element** (m5, replacing `Ideal.sInf_minimalPrimes` in
`one_mem_sup_colon`): if the components are pairwise equal or comaximal and `(l)` is radical,
then `1 ∈ C + ((l) : C)`, for any colon list `K` of `(l) : C`. -/
theorem IsCompList.one_mem_sup_colon {l : List A} {Cs : List (List A)} (hC : IsCompList l Cs)
    {C : List A} (hcomax : ∀ D ∈ Cs, lspan D = lspan C ∨ (1 : A) ∈ lspan C ⊔ lspan D)
    (hrad : ∀ (x : A) (k : ℕ), x ^ k ∈ lspan l → x ∈ lspan l) (K : List A)
    (hK : ∀ x, x ∈ lspan K ↔ ∀ y ∈ lspan C, x * y ∈ lspan l) :
    (1 : A) ∈ lspan C ⊔ lspan K := by
  obtain ⟨e, he, hDs⟩ := exists_sep_aux C Cs hcomax
  have heK : e ∈ lspan K := (hK e).2 fun y hy => by
    obtain ⟨k, hk⟩ := hC.rad (e * y) fun D hD => hDs D hD y hy
    exact hrad _ k hk
  have : (1 : A) = (1 - e) + e := by ring
  rw [this]
  exact Submodule.add_mem_sup he heK

/-- Equality of explicit ideals is decided by (G). -/
lemma HasPres.eq_dec (h : HasPres A) (P P' : List A) : lspan P = lspan P' ∨ lspan P ≠ lspan P' := by
  rcases h.le_dec P P' with h1 | h1
  · rcases h.le_dec P' P with h2 | h2
    · exact Or.inl (le_antisymm h1 h2)
    · exact Or.inr fun he => h2 he.ge
  · exact Or.inr fun he => h1 he.le


/-- **The first nonzero explicit generator** (replaces `Submodule.exists_mem_ne_zero_of_ne_bot`):
`x = 0` is decided by (G) (`x ∈ lspan []`), so a nonzero explicit ideal has a nonzero generator,
found by testing the generators in order. -/
theorem HasPres.exists_mem_ne_zero (h : HasPres A) (l : List A) (hl : lspan l ≠ ⊥) :
    ∃ f ∈ l, f ≠ 0 := by
  have h0 : lspan ([] : List A) ≤ ⊥ := by
    rw [lspan, Ideal.span_le]; intro y hy; exact absurd hy List.not_mem_nil
  have hz : ∀ x : A, x = 0 ∨ x ≠ 0 := fun x => by
    rcases h.mem_dec [] x with hx | hx
    · exact Or.inl (Ideal.mem_bot.1 (h0 hx))
    · exact Or.inr fun hx0 => hx (hx0 ▸ Ideal.zero_mem _)
  rcases list_exists_or_forall (P := fun x : A => x ≠ 0)
    (fun x => (hz x).elim (fun hx0 => Or.inr fun h' => h' hx0) Or.inl) l with he | hall
  · exact he
  · refine absurd (le_antisymm ?_ bot_le) hl
    rw [lspan, Ideal.span_le]
    intro x hx
    rcases hz x with hx0 | hx0
    · exact Ideal.mem_bot.2 hx0
    · exact absurd hx0 (hall x hx)

/-- **A component of `V(l)`**, as data: explicit generators of a prime with factorial fraction
field, minimal over `(l)`. Replaces the hypothesis `h𝔭 : 𝔭 ∈ (lspan l).minimalPrimes`. -/
structure Comp (l : List A) where
  gens : List A
  primeFF : PrimeFF (lspan gens)
  le : lspan l ≤ lspan gens
  minimal : ∀ Q : Ideal A, Q.IsPrime → lspan l ≤ Q → Q ≤ lspan gens → Q = lspan gens

namespace Comp

variable {l : List A}

lemma isPrime (P : Comp l) : (lspan P.gens).IsPrime := P.primeFF.1

lemma mem_minimalPrimes (P : Comp l) : lspan P.gens ∈ (lspan l).minimalPrimes :=
  ⟨⟨P.isPrime, P.le⟩, fun Q hQ hQC => (P.minimal Q hQ.1 hQ.2 hQC).ge⟩

/-- The entries of a component list, as components. -/
def ofMem {Cs : List (List A)} (hC : IsCompList l Cs) {C : List A} (hCm : C ∈ Cs) : Comp l :=
  ⟨C, hC.primeFF C hCm, hC.le C hCm, hC.minimal C hCm⟩

/-- Every component is an entry of every component list. -/
lemma exists_mem {Cs : List (List A)} (hC : IsCompList l Cs) (P : Comp l) :
    ∃ C ∈ Cs, lspan C = lspan P.gens := by
  obtain ⟨C, hCm, hCP⟩ := hC.cover _ P.isPrime P.le
  exact ⟨C, hCm, P.minimal _ (hC.isPrime hCm) (hC.le C hCm) hCP⟩

end Comp

end Pres

end BezoutCounterexample.Constructive
