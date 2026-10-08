import BezoutCounterexample.Naive.Kronecker
import BezoutCounterexample.MainTheorem

/-!
# The naive Kronecker tower `R_naive`

Starting from `A₀ = ℚ[x, y]`, each step adjoins, for one pair `(a, b)`, two indeterminates
`σ, τ` and the fractions `a/g`, `b/g` with `g = a σ + b τ` (`Naive.U`). The pairs are scheduled as
in Construction 5.1 of Hägg–Mörtberg. The union `R_naive` is a Bézout domain (`RN.isBezout`);
no smoothness, factoriality or principalization is involved.

We also prove the generic form of the last step of Theorem 1.1: over any domain `S` with a map
`A₀ → S` for which the five-element obstruction holds, `M` has no Smith normal form.
-/

noncomputable section

namespace BezoutCounterexample.Naive

open MvPolynomial

/-! ## Countability of a Kronecker step -/

lemma U_eq_range {R : Type*} [CommRing R] [IsDomain R] (a b : R) :
    U a b = (aeval ![σ, τ, algebraMap R (KF R) a / gen a b, algebraMap R (KF R) b / gen a b] :
      MvPolynomial (Fin 4) R →ₐ[R] KF R).range := by
  rw [← Algebra.adjoin_range_eq_range_aeval, U, gens]
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.exists_fin_zero_pi, IsEmpty.exists_iff,
    or_false]
  constructor
  · rintro (h | h | h | h) <;> simp [h]
  · rintro (h | h | h | h) <;> simp [← h]

instance countable_U {R : Type*} [CommRing R] [IsDomain R] [Countable R] (a b : R) :
    Countable (U a b) := by
  set f := (aeval ![σ, τ, algebraMap R (KF R) a / gen a b, algebraMap R (KF R) b / gen a b] :
      MvPolynomial (Fin 4) R →ₐ[R] KF R)
  have hsurj : Function.Surjective
      (fun p : MvPolynomial (Fin 4) R => (⟨f p, by rw [U_eq_range]; exact ⟨p, rfl⟩⟩ : U a b)) := by
    rintro ⟨u, hu⟩
    rw [U_eq_range] at hu
    obtain ⟨p, rfl⟩ := hu
    exact ⟨p, rfl⟩
  exact hsurj.countable

/-! ## The stages -/

/-- A stage of the naive tower: a countable domain together with the images `e i j` of the
pairs enumerated so far. -/
structure NStage where
  /-- The ring. -/
  A : Type
  [commRing : CommRing A]
  [isDomain : IsDomain A]
  [countable : Countable A]
  /-- For `i ≤ n`, `e i j` is the image of the `j`-th pair of stage `i`. -/
  e : ℕ → ℕ → A × A

attribute [instance] NStage.commRing NStage.isDomain NStage.countable

/-- A surjection `ℕ → A × A`. -/
def chooseSurj (A : Type) [Countable A] [Nonempty A] : ℕ → A × A :=
  Classical.choose (exists_surjective_nat (A × A))

theorem chooseSurj_surjective (A : Type) [Countable A] [Nonempty A] :
    Function.Surjective (chooseSurj A) :=
  Classical.choose_spec (exists_surjective_nat (A × A))

/-- The pair processed at step `n`. -/
def NStage.pair (S : NStage) (n : ℕ) : S.A × S.A :=
  S.e (pairing.symm n).1 (pairing.symm n).2

/-- The initial stage `A₀ = ℚ[x, y]`. -/
def initial : NStage where
  A := A₀
  e _ := chooseSurj A₀

/-- The next stage: the Kronecker step for the pair `S.pair n`. -/
def next (n : ℕ) (S : NStage) : NStage where
  A := U (S.pair n).1 (S.pair n).2
  e i j :=
    if i ≤ n then Prod.map (algebraMap S.A _) (algebraMap S.A _) (S.e i j)
    else chooseSurj (U (S.pair n).1 (S.pair n).2) j

/-- The stages of the naive tower. -/
def stage (n : ℕ) : NStage := Nat.rec initial (fun n S => next n S) n

/-- The ring at stage `n`. -/
abbrev NA (n : ℕ) : Type := (stage n).A

/-- The pair processed at step `n`. -/
def pairAt (n : ℕ) : NA n × NA n := (stage n).pair n

/-- `NA (n + 1)` is the Kronecker step of `NA n` for `pairAt n`. -/
lemma NA_succ (n : ℕ) : NA (n + 1) = U (pairAt n).1 (pairAt n).2 := rfl

/-- The inclusion `NA n → NA (n + 1)`. -/
def incl (n : ℕ) : NA n →+* NA (n + 1) := algebraMap (NA n) (U (pairAt n).1 (pairAt n).2)

lemma incl_injective (n : ℕ) : Function.Injective (incl n) := algebraMap_U_injective _ _

/-- The pair processed at step `n` becomes principal in `NA (n + 1)`. -/
theorem span_pairAt_map_isPrincipal (n : ℕ) :
    ((Ideal.span {(pairAt n).1, (pairAt n).2} : Ideal (NA n)).map (incl n)).IsPrincipal :=
  ⟨⟨_, span_pair_eq (pairAt n).1 (pairAt n).2⟩⟩

/-- The enumeration of stage `i`. -/
def η (i : ℕ) : ℕ → NA i × NA i := (stage i).e i

/-! ### The composite maps `NA i → NA j` -/

def inclLEFun {i j : ℕ} (h : i ≤ j) (a : NA i) : NA j :=
  Nat.leRecOn h (fun {k} (b : NA k) => incl k b) a

lemma inclLEFun_self (i : ℕ) (a : NA i) : inclLEFun (le_refl i) a = a :=
  Nat.leRecOn_self _

lemma inclLEFun_succ {i j : ℕ} (h : i ≤ j) (a : NA i) :
    inclLEFun (h.trans (Nat.le_succ j)) a = incl j (inclLEFun h a) :=
  Nat.leRecOn_succ h _

lemma inclLEFun_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : NA i) :
    inclLEFun (hij.trans hjk) a = inclLEFun hjk (inclLEFun hij a) :=
  Nat.leRecOn_trans hij hjk _

/-- The composite `NA i → NA j` for `i ≤ j`. -/
def inclLE {i j : ℕ} (h : i ≤ j) : NA i →+* NA j where
  toFun := inclLEFun h
  map_one' := by
    induction j, h using Nat.le_induction with
    | base => exact inclLEFun_self i 1
    | succ k hik ih => rw [inclLEFun_succ hik, ih, map_one]
  map_mul' a b := by
    induction j, h using Nat.le_induction with
    | base => simp only [inclLEFun_self]
    | succ k hik ih => rw [inclLEFun_succ hik, inclLEFun_succ hik, inclLEFun_succ hik, ih,
        map_mul]
  map_zero' := by
    induction j, h using Nat.le_induction with
    | base => exact inclLEFun_self i 0
    | succ k hik ih => rw [inclLEFun_succ hik, ih, map_zero]
  map_add' a b := by
    induction j, h using Nat.le_induction with
    | base => simp only [inclLEFun_self]
    | succ k hik ih => rw [inclLEFun_succ hik, inclLEFun_succ hik, inclLEFun_succ hik, ih,
        map_add]

lemma inclLE_apply {i j : ℕ} (h : i ≤ j) (a : NA i) : inclLE h a = inclLEFun h a := rfl

lemma inclLE_self (i : ℕ) (a : NA i) : inclLE (le_refl i) a = a := inclLEFun_self i a

lemma inclLE_succ {i j : ℕ} (h : i ≤ j) (a : NA i) :
    inclLE (h.trans (Nat.le_succ j)) a = incl j (inclLE h a) := inclLEFun_succ h a

lemma inclLE_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : NA i) :
    inclLE (hij.trans hjk) a = inclLE hjk (inclLE hij a) := inclLEFun_trans hij hjk a

lemma inclLE_succ_self (n : ℕ) (a : NA n) : inclLE (Nat.le_succ n) a = incl n a := by
  rw [← inclLE_self n a, ← inclLE_succ (le_refl n), inclLE_self]

lemma inclLE_injective {i j : ℕ} (h : i ≤ j) : Function.Injective (inclLE h) :=
  Nat.leRecOn_injective h _ (fun k => incl_injective k)

instance directedSystem :
    DirectedSystem (fun n => (NA n : Type)) fun _ _ h => ⇑(inclLE h) where
  map_self i a := inclLE_self i a
  map_map _ _ _ hij hjk a := (inclLE_trans hij hjk a).symm

/-- `A₀ → NA n`. -/
def ι (n : ℕ) : A₀ →+* NA n := inclLE (Nat.zero_le n)

lemma ι_succ (n : ℕ) (a : A₀) : ι (n + 1) a = incl n (ι n a) :=
  inclLE_succ (Nat.zero_le n) a

/-! ### The enumerations -/

theorem η_surjective (i : ℕ) : Function.Surjective (η i) := by
  cases i with
  | zero => exact chooseSurj_surjective A₀
  | succ n =>
    have : η (n + 1) = chooseSurj (NA (n + 1)) := by
      funext j
      simp [η, stage, next]
      rfl
    rw [this]
    exact chooseSurj_surjective _

theorem e_eq {i : ℕ} (j : ℕ) {n : ℕ} (h : i ≤ n) :
    (stage n).e i j = Prod.map (inclLE h) (inclLE h) (η i j) := by
  induction n, h using Nat.le_induction with
  | base => ext <;> simp [η, inclLE_self]
  | succ k hik ih =>
    have h1 : (stage (k + 1)).e i j = Prod.map (incl k) (incl k) ((stage k).e i j) := by
      show (next k (stage k)).e i j = _
      simp only [next, hik, ite_true]
      rfl
    rw [h1, ih]
    ext <;> simp only [Prod.map_fst, Prod.map_snd] <;> exact (inclLE_succ hik _).symm

theorem pairAt_eq (i j : ℕ) :
    pairAt (pairing (i, j)) =
      Prod.map (inclLE (left_le_pairing i j)) (inclLE (left_le_pairing i j)) (η i j) := by
  have h := e_eq j (left_le_pairing i j)
  rw [pairAt, NStage.pair, Equiv.symm_apply_apply]
  exact h

end BezoutCounterexample.Naive

namespace BezoutCounterexample

open Naive

/-! ## The ring `R_naive` -/

/-- **The naive Kronecker–Bézout ring** `R_naive = ⋃ NA n`. -/
def RN : Type := Ring.DirectLimit (fun n => (NA n : Type)) fun _ _ h => ⇑(inclLE h)

namespace RN

instance : CommRing RN := inferInstanceAs (CommRing (Ring.DirectLimit _ _))

def of (n : ℕ) : NA n →+* RN := Ring.DirectLimit.of (fun n => (NA n : Type)) _ n

lemma of_inclLE {i j : ℕ} (h : i ≤ j) (a : NA i) : of j (inclLE h a) = of i a :=
  Ring.DirectLimit.of_f (G := fun n => (NA n : Type)) (f := fun _ _ h => ⇑(inclLE h)) h a

lemma of_incl (n : ℕ) (a : NA n) : of (n + 1) (incl n a) = of n a := by
  rw [← inclLE_succ_self, of_inclLE]

lemma of_injective (n : ℕ) : Function.Injective (of n) :=
  Ring.DirectLimit.of_injective (G := fun n => (NA n : Type)) (fun _ _ h => inclLE h)
    (fun _ _ h => inclLE_injective h) n

lemma exists_of (r : RN) : ∃ n a, of n a = r := Ring.DirectLimit.exists_of r

lemma exists_of_fin (k : ℕ) (v : Fin k → RN) :
    ∃ (n : ℕ) (w : Fin k → NA n), ∀ t, of n (w t) = v t := by
  induction k with
  | zero => exact ⟨0, Fin.elim0, fun t => Fin.elim0 t⟩
  | succ k ih =>
    obtain ⟨n, w, hw⟩ := ih (fun t => v t.castSucc)
    obtain ⟨m, a, ha⟩ := exists_of (v (Fin.last k))
    refine ⟨max n m, Fin.lastCases (inclLE (le_max_right n m) a)
      (fun t => inclLE (le_max_left n m) (w t)), fun t => ?_⟩
    induction t using Fin.lastCases with
    | last => simp only [Fin.lastCases_last, of_inclLE, ha]
    | cast t => simp only [Fin.lastCases_castSucc, of_inclLE, hw]

/-- `A₀ → R_naive`. -/
def ι : A₀ →+* RN := of 0

lemma of_ι (n : ℕ) (a : A₀) : of n (Naive.ι n a) = ι a :=
  of_inclLE (Nat.zero_le n) a

instance : Nontrivial RN := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have : of 0 0 = of 0 1 := by simpa using h
  exact zero_ne_one (of_injective 0 this)

instance isDomain : IsDomain RN := by
  have : NoZeroDivisors RN := ⟨fun {a b} hab => by
      obtain ⟨n, w, hw⟩ := exists_of_fin 2 ![a, b]
      have ha : of n (w 0) = a := hw 0
      have hb : of n (w 1) = b := hw 1
      have : w 0 * w 1 = 0 := by
        apply of_injective n
        rw [map_mul, ha, hb, hab, map_zero]
      rcases mul_eq_zero.1 this with h | h
      · left; rw [← ha, h, map_zero]
      · right; rw [← hb, h, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

/-- **`R_naive` is a Bézout domain**, by the Kronecker steps alone. -/
instance isBezout : IsBezout RN := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro a b
  obtain ⟨i, w, hw⟩ := exists_of_fin 2 ![a, b]
  obtain ⟨j, hj⟩ := η_surjective i (w 0, w 1)
  set n := pairing (i, j)
  have hpair : pairAt n = (inclLE (left_le_pairing i j) (w 0),
      inclLE (left_le_pairing i j) (w 1)) := by
    rw [pairAt_eq, hj]
    rfl
  obtain ⟨g, hg⟩ := span_pairAt_map_isPrincipal n
  have hg' : (Ideal.span {incl n (inclLE (left_le_pairing i j) (w 0)),
      incl n (inclLE (left_le_pairing i j) (w 1))} : Ideal (NA (n + 1))) = Ideal.span {g} := by
    refine Eq.trans ?_ hg
    rw [Ideal.map_span, Set.image_pair, hpair]
  have hmap := congrArg (Ideal.map (of (n + 1))) hg'
  rw [Ideal.map_span, Ideal.map_span, Set.image_pair, Set.image_singleton, of_incl, of_incl,
    of_inclLE, of_inclLE, hw 0, hw 1] at hmap
  exact ⟨⟨of (n + 1) g, by simpa using hmap⟩⟩

end RN

/-! ## The generic last step of Theorem 1.1 -/

section Generic

open Matrix

variable {S : Type*} [CommRing S] [IsDomain S] (ιS : A₀ →+* S)

/-- If the five-element obstruction holds over `S`, then `M` has no Smith normal form over `S`. -/
theorem not_hasSmithNormalForm_of_obstruction
    (hobs : ¬ ∃ p q u v μ : S, μ * (![p, q] ᵥ* (M.map ιS) ⬝ᵥ ![u, v]) = 1) :
    ¬ HasSmithNormalForm (M.map ιS) := by
  have span_entries : (Ideal.span {ιS (1 + x), ιS y, ιS (1 - x)} : Ideal S) = ⊤ := by
    have h := congrArg (Ideal.map ιS) span_entries_M
    rwa [Ideal.map_span, Ideal.map_top, Set.image_insert_eq, Set.image_pair] at h
  rintro ⟨G, hMG, hG⟩
  obtain ⟨d, hd, hdiv⟩ := (isSmithNormalForm_iff_chain G).1 hG
  have hd12 : d 0 ∣ d 1 := hdiv 0 (by norm_num)
  have htop : (Ideal.span {d 0, d 1} : Ideal S) = ⊤ := by
    have hGmem : ∀ i j, G i j ∈ (Ideal.span {d 0, d 1} : Ideal S) := by
      intro i j
      fin_cases i <;> fin_cases j
      · rw [hd]; exact Ideal.subset_span (by simp)
      · rw [hd]; simp
      · rw [hd]; simp
      · rw [hd]; exact Ideal.subset_span (by simp)
    have hM := hMG.entry_mem _ hGmem
    rw [eq_top_iff, ← span_entries, Ideal.span_le]
    rintro r (rfl | rfl | rfl)
    · simpa [M] using hM 0 0
    · simpa [M] using hM 0 1
    · simpa [M] using hM 1 1
  have hunit : IsUnit (d 0) := by
    have h : (Ideal.span {d 0, d 1} : Ideal S) = Ideal.span {d 0} := by
      rw [Ideal.span_insert, sup_eq_left.2 (Ideal.span_singleton_le_span_singleton.2 hd12)]
    rwa [h, Ideal.span_singleton_eq_top] at htop
  obtain ⟨P, Q, hPQ⟩ := hMG
  have h00 : ![(P : Matrix (Fin 2) (Fin 2) S) 0 0, (P : Matrix (Fin 2) (Fin 2) S) 0 1] ᵥ*
      (M.map ιS) ⬝ᵥ ![(Q : Matrix (Fin 2) (Fin 2) S) 0 0, (Q : Matrix (Fin 2) (Fin 2) S) 1 0] =
      d 0 := by
    have h : ((P : Matrix (Fin 2) (Fin 2) S) * M.map ιS * Q) 0 0 = d 0 := by
      rw [hPQ, hd]; simp
    rw [← h]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  obtain ⟨μ, hμ⟩ := hunit.exists_left_inv
  exact hobs ⟨_, _, _, _, μ, by rw [h00, hμ]⟩

/-- The obstruction transfers backwards along ring homomorphisms. -/
theorem obstruction_of_hom {S' : Type*} [CommRing S'] (ιS' : A₀ →+* S') (Φ : S →+* S')
    (hΦ : Φ.comp ιS = ιS')
    (hobs : ¬ ∃ p q u v μ : S', μ * (![p, q] ᵥ* (M.map ιS') ⬝ᵥ ![u, v]) = 1) :
    ¬ ∃ p q u v μ : S, μ * (![p, q] ᵥ* (M.map ιS) ⬝ᵥ ![u, v]) = 1 := by
  rintro ⟨p, q, u, v, μ, h⟩
  apply hobs
  refine ⟨Φ p, Φ q, Φ u, Φ v, Φ μ, ?_⟩
  rw [vecMul_M_dotProduct] at h ⊢
  have := congrArg Φ h
  simp only [map_mul, map_add, map_sub, map_one] at this
  rw [← hΦ]
  simpa using this

end Generic

end BezoutCounterexample
