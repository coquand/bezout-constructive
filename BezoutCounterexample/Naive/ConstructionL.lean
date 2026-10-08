import BezoutCounterexample.Naive.LaurentStep

/-!
# Construction 5.1 with Laurent steps

A copy of Construction 5.1 of Hägg–Mörtberg in which every principalization step is followed by
the Laurent step `A' ↦ A'[X₀, X₁][1/(X₀ X₁)]` (`PrincipalizationResult.withLaurent`). The proofs
are unchanged; the resulting ring `RL` is again a Bézout domain with the five-element obstruction,
and in addition every stage provides fresh units.
-/

noncomputable section

namespace BezoutCounterexample

open Set Topology

namespace CL

/-! ## Construction 5.1 -/

/-- Every finitely generated `ℚ`-algebra is countable, so once a stage `A` has been constructed we
may choose a surjection `ℕ → A × A`. -/
def chooseSurj (A : SmoothGCDDomain) : ℕ → A × A :=
  Classical.choose (exists_surjective_nat (A × A))

theorem chooseSurj_surjective (A : SmoothGCDDomain) :
    Function.Surjective (chooseSurj A) :=
  Classical.choose_spec (exists_surjective_nat (A × A))

/-- The data at stage `n` of Construction 5.1: the ring `A_n`, the compact set
`K_n ⊆ Spec(A_n)(ℝ)`, and, for `i ≤ n`, the image `e i j ∈ A_n × A_n` of the pair `η_i(j)`
(`e_eq`). -/
structure Stage where
  /-- The ring `A_n`. -/
  A : SmoothGCDDomain
  /-- The compact set `K_n`. -/
  K : Set (RealPt A)
  isCompact_K : IsCompact K
  /-- For `i ≤ n`, `e i j` is the image in `A_n` of `η_i(j)`. -/
  e : ℕ → ℕ → A × A

/-- The pair processed when passing from `A_n` to `A_{n+1}`: writing `n = ⟨i, j⟩`, it is `e i j`,
the image in `A_n` of `η_i(j)`. -/
def Stage.pair (S : Stage) (n : ℕ) : S.A × S.A :=
  S.e (pairing.symm n).1 (pairing.symm n).2

/-- The step for a pair `(a, b)` with `a = 0` or `b = 0`: the ideal `(a, b)` is principal, and we
put `A_{n+1} = A_n` and `K_{n+1} = K_n`. -/
def trivialStep (S : Stage) (a b : S.A) (h : a = 0 ∨ b = 0) :
    PrincipalizationResult S.A (Ideal.span {a, b}) S.K where
  A' := S.A
  f := AlgHom.id ℚ S.A
  K' := S.K
  injective := Function.injective_id
  principal := by
    rw [Ideal.map_span, Set.image_pair]
    rcases h with rfl | rfl
    · exact ⟨⟨b, show _ = Ideal.span {b} by simp⟩⟩
    · exact ⟨⟨a, show _ = Ideal.span {a} by rw [Set.pair_comm]; simp⟩⟩
  isCompact := S.isCompact_K
  monotone := IsMonotoneSurjOn.id S.K

/-- The step for a pair `(a, b)` with `a ≠ 0` and `b ≠ 0`: write `a = c a'` and `b = c b'` with
`a'` and `b'` coprime (possible as `A_n` is a UFD), apply Proposition 4.6 to the ideal
`(a', b') A_n` and the compact set `K_n`, and let `A_{n+1}` and `K_{n+1}` be the resulting ring
and compact set. Then `(a, b) A_{n+1} = c (a', b') A_{n+1}` is principal. -/
def principalizationStep (S : Stage) (a b : S.A) (ha : a ≠ 0) (hb : b ≠ 0) :
    PrincipalizationResult S.A (Ideal.span {a, b}) S.K :=
  let t := coprimeFactors a b hb
  let D := principalizationResult S.A (Ideal.span {t.2.1, t.2.2}) (span_coprimeFactors_ne_bot ha hb)
    S.K S.isCompact_K
  { A' := D.A'
    f := D.f
    K' := D.K'
    injective := D.injective
    principal := by
      -- `(a, b) A_{n+1} = c (a', b') A_{n+1} = (c g)`
      obtain ⟨g, hg⟩ := D.principal
      refine ⟨⟨D.f t.1 * g, ?_⟩⟩
      rw [map_span_pair_eq_mul D.f (coprimeFactors_spec a b hb).1 (coprimeFactors_spec a b hb).2.1,
        hg, Ideal.span_singleton_mul_span_singleton]
    isCompact := D.isCompact
    monotone := D.monotone }

/-- In the case `a, b ≠ 0`, Proposition 4.6 makes `(a', b') A_{n+1}` principal. -/
theorem principalizationStep_principal (S : Stage) (a b : S.A) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((Ideal.span {(coprimeFactors a b hb).2.1, (coprimeFactors a b hb).2.2} : Ideal S.A).map
      (principalizationStep S a b ha hb).f).IsPrincipal :=
  (principalizationResult _ _ (span_coprimeFactors_ne_bot ha hb) S.K S.isCompact_K).principal

/-- In the case `a, b ≠ 0`: `(a, b) A_{n+1} = c (a', b') A_{n+1}`. -/
theorem principalizationStep_map_span (S : Stage) (a b : S.A) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Ideal.span {a, b} : Ideal S.A).map (principalizationStep S a b ha hb).f =
      Ideal.span {(principalizationStep S a b ha hb).f (coprimeFactors a b hb).1} *
        (Ideal.span {(coprimeFactors a b hb).2.1, (coprimeFactors a b hb).2.2} : Ideal S.A).map
          (principalizationStep S a b ha hb).f :=
  map_span_pair_eq_mul _ (coprimeFactors_spec a b hb).1 (coprimeFactors_spec a b hb).2.1

open Classical in
/-- **One step of Construction 5.1**, for the pair `(a, b)` of `A_n`: if `a = 0` or `b = 0` then
`A_{n+1} = A_n` and `K_{n+1} = K_n` (`trivialStep`); otherwise we extract the greatest common
divisor and apply Proposition 4.6 to the coprime pair (`principalizationStep`). -/
def step (S : Stage) (a b : S.A) : PrincipalizationResult S.A (Ideal.span {a, b}) S.K :=
  if h : a = 0 ∨ b = 0 then trivialStep S a b h
  else principalizationStep S a b (not_or.1 h).1 (not_or.1 h).2

theorem step_of_eq_zero (S : Stage) (a b : S.A) (h : a = 0 ∨ b = 0) :
    step S a b = trivialStep S a b h := by
  rw [step, dite_eq_left h]

theorem step_of_ne_zero (S : Stage) (a b : S.A) (ha : a ≠ 0) (hb : b ≠ 0) :
    step S a b = principalizationStep S a b ha hb := by
  rw [step, dite_eq_right (not_or.2 ⟨ha, hb⟩)]

/-- The stage `A_0 = ℚ[x, y]`, `K_0 = K₀`, with the surjection `η_0 : ℕ → A_0 × A_0`. -/
def initialStage : Stage where
  A := A₀SGD
  K := K₀
  isCompact_K := isCompact_K₀
  e _ := chooseSurj A₀SGD

/-- Passing from stage `n` to stage `n + 1`: the pair `S.pair n` is processed by `step`, the
earlier pairs `e i j` (`i ≤ n`) are mapped to the new ring, and the surjection `η_{n+1}` is chosen
for the new ring. -/
def nextStage (n : ℕ) (S : Stage) : Stage where
  A := (step S (S.pair n).1 (S.pair n).2).withLaurent.A'
  K := (step S (S.pair n).1 (S.pair n).2).withLaurent.K'
  isCompact_K := (step S (S.pair n).1 (S.pair n).2).withLaurent.isCompact
  e i j :=
    if i ≤ n then
      Prod.map (step S (S.pair n).1 (S.pair n).2).withLaurent.f (step S (S.pair n).1 (S.pair n).2).withLaurent.f (S.e i j)
    else chooseSurj (step S (S.pair n).1 (S.pair n).2).withLaurent.A' j

lemma nextStage_e_of_le (n : ℕ) (S : Stage) {i : ℕ} (h : i ≤ n) (j : ℕ) :
    (nextStage n S).e i j = Prod.map (step S (S.pair n).1 (S.pair n).2).withLaurent.f
      (step S (S.pair n).1 (S.pair n).2).withLaurent.f (S.e i j) := by
  simp only [nextStage, h, ite_true]

lemma nextStage_e_succ (n : ℕ) (S : Stage) (j : ℕ) :
    (nextStage n S).e (n + 1) j = chooseSurj (step S (S.pair n).1 (S.pair n).2).withLaurent.A' j := by
  simp [nextStage]

/-- The stages of Construction 5.1. -/
def stage (n : ℕ) : Stage := Nat.rec initialStage (fun n S => nextStage n S) n

theorem stage_zero : stage 0 = initialStage := rfl

theorem stage_succ (n : ℕ) : stage (n + 1) = nextStage n (stage n) := rfl

/-- The ring `A_n`. -/
abbrev A (n : ℕ) : SmoothGCDDomain := (stage n).A

/-- The compact set `K_n ⊆ Spec(A_n)(ℝ)`. -/
abbrev K (n : ℕ) : Set (RealPt (A n)) := (stage n).K

/-- The surjection `η_i : ℕ → A_i × A_i` chosen once `A_i` has been constructed. -/
def η (i : ℕ) : ℕ → A i × A i := (stage i).e i

/-- The pair `(a, b)` processed when passing from `A_n` to `A_{n+1}`. -/
def pairAt (n : ℕ) : A n × A n := (stage n).pair n

/-- The step from `A_n` to `A_{n+1}`. -/
abbrev stepAt (n : ℕ) : PrincipalizationResult (A n) (Ideal.span {(pairAt n).1, (pairAt n).2})
    (K n) :=
  (step (stage n) (pairAt n).1 (pairAt n).2).withLaurent

/-- The injection `A_n ↪ A_{n+1}`. -/
def incl (n : ℕ) : A n →ₐ[ℚ] A (n + 1) := (stepAt n).f

theorem A_zero : A 0 = A₀SGD := rfl

theorem K_zero : K 0 = K₀ := rfl

/-- Every `K_n` is compact. -/
theorem isCompact_K (n : ℕ) : IsCompact (K n) := (stage n).isCompact_K

/-- Every map `A_n → A_{n+1}` is injective. -/
theorem incl_injective (n : ℕ) : Function.Injective (incl n) := (stepAt n).injective

/-- Every induced map `K_{n+1} → K_n` is a monotone surjection. -/
theorem isMonotoneSurjOn_incl (n : ℕ) :
    IsMonotoneSurjOn (RealPt.comap (incl n : A n →+* A (n + 1))) (K (n + 1)) (K n) :=
  (stepAt n).monotone

/-- The pair processed when passing from `A_n` to `A_{n+1}` generates a principal ideal of
`A_{n+1}`. -/
theorem span_pairAt_map_isPrincipal (n : ℕ) :
    ((Ideal.span {(pairAt n).1, (pairAt n).2} : Ideal (A n)).map (incl n)).IsPrincipal :=
  (stepAt n).principal

/-! ### The composite maps `A_i → A_j` -/

/-- The composite `A_i → A_j` for `i ≤ j`, as a function. -/
def inclLEFun {i j : ℕ} (h : i ≤ j) (a : A i) : A j :=
  Nat.leRecOn h (fun {k} (b : A k) => incl k b) a

lemma inclLEFun_self (i : ℕ) (a : A i) : inclLEFun (le_refl i) a = a :=
  Nat.leRecOn_self _

lemma inclLEFun_succ {i j : ℕ} (h : i ≤ j) (a : A i) :
    inclLEFun (h.trans (Nat.le_succ j)) a = incl j (inclLEFun h a) :=
  Nat.leRecOn_succ h _

lemma inclLEFun_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : A i) :
    inclLEFun (hij.trans hjk) a = inclLEFun hjk (inclLEFun hij a) :=
  Nat.leRecOn_trans hij hjk _

/-- The composite `A_i → A_j` for `i ≤ j`, as a ring homomorphism. -/
def inclLE {i j : ℕ} (h : i ≤ j) : A i →+* A j where
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

lemma inclLE_apply {i j : ℕ} (h : i ≤ j) (a : A i) : inclLE h a = inclLEFun h a := rfl

lemma inclLE_self (i : ℕ) (a : A i) : inclLE (le_refl i) a = a := inclLEFun_self i a

lemma inclLE_succ {i j : ℕ} (h : i ≤ j) (a : A i) :
    inclLE (h.trans (Nat.le_succ j)) a = incl j (inclLE h a) := inclLEFun_succ h a

lemma inclLE_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (a : A i) :
    inclLE (hij.trans hjk) a = inclLE hjk (inclLE hij a) := inclLEFun_trans hij hjk a

lemma inclLE_succ_self (n : ℕ) (a : A n) : inclLE (Nat.le_succ n) a = incl n a := by
  rw [← inclLE_self n a, ← inclLE_succ (le_refl n), inclLE_self]

/-- The composites `A_i → A_j` are injective. -/
lemma inclLE_injective {i j : ℕ} (h : i ≤ j) : Function.Injective (inclLE h) :=
  Nat.leRecOn_injective h _ (fun k => incl_injective k)

instance directedSystem :
    DirectedSystem (fun n => (A n : Type)) fun _ _ h => ⇑(inclLE h) where
  map_self i a := inclLE_self i a
  map_map _ _ _ hij hjk a := (inclLE_trans hij hjk a).symm

/-- The injection `A₀ ↪ A_n`, identifying `A₀` with its image in `A_n`. -/
def ι (n : ℕ) : A₀ →+* A n := inclLE (Nat.zero_le n)

lemma ι_zero (a : A₀) : ι 0 a = a := inclLE_self 0 a

lemma ι_succ (n : ℕ) (a : A₀) : ι (n + 1) a = incl n (ι n a) :=
  inclLE_succ (Nat.zero_le n) a

/-! ### The surjections `η_i` and the pairs processed -/

/-- `η_i : ℕ → A_i × A_i` is surjective. -/
theorem η_surjective (i : ℕ) : Function.Surjective (η i) := by
  cases i with
  | zero => exact chooseSurj_surjective A₀SGD
  | succ n =>
    have : η (n + 1) = chooseSurj (A (n + 1)) := funext fun j => nextStage_e_succ n (stage n) j
    rw [this]
    exact chooseSurj_surjective _

/-- For `i ≤ n`, `e i j` at stage `n` is the image in `A_n` of `η_i(j)`. -/
theorem e_eq {i : ℕ} (j : ℕ) {n : ℕ} (h : i ≤ n) :
    (stage n).e i j = Prod.map (inclLE h) (inclLE h) (η i j) := by
  induction n, h using Nat.le_induction with
  | base => ext <;> simp [η, inclLE_self]
  | succ k hik ih =>
    have h1 : (stage (k + 1)).e i j = Prod.map (incl k) (incl k) ((stage k).e i j) :=
      nextStage_e_of_le k (stage k) hik j
    rw [h1, ih]
    ext <;> simp only [Prod.map_fst, Prod.map_snd] <;> exact (inclLE_succ hik _).symm

/-- **The pair processed at step `n = ⟨i, j⟩`** is the image in `A_n` of `η_i(j)`. -/
theorem pairAt_eq (i j : ℕ) :
    pairAt (pairing (i, j)) =
      Prod.map (inclLE (left_le_pairing i j)) (inclLE (left_le_pairing i j)) (η i j) := by
  have h := e_eq j (left_le_pairing i j)
  rw [pairAt, Stage.pair, Equiv.symm_apply_apply]
  exact h

/-! ### Real points: the composite `K_n → K_0` and (5.2) -/

/-- **Lemma 2.2 applied to the transition maps**: the composite `K_n → K_0` is a monotone
surjection. -/
theorem isMonotoneSurjOn_ι (n : ℕ) : IsMonotoneSurjOn (RealPt.comap (ι n)) (K n) K₀ := by
  induction n with
  | zero =>
    have : RealPt.comap (ι 0) = fun z => z := by
      funext z
      ext a
      exact congrArg z (ι_zero a)
    rw [this]
    exact IsMonotoneSurjOn.id K₀
  | succ n ih =>
    have : RealPt.comap (ι (n + 1)) =
        RealPt.comap (ι n) ∘ RealPt.comap (incl n : A n →+* A (n + 1)) := by
      funext z
      ext a
      simp only [Function.comp_apply, RealPt.comap_apply, ι_succ]
      rfl
    rw [this]
    exact IsMonotoneSurjOn.trans (isCompact_K (n + 1)) ih (isMonotoneSurjOn_incl n)

/-- `K_n` maps to `K_0`. -/
theorem mapsTo_K₀ (n : ℕ) : MapsTo (RealPt.comap (ι n)) (K n) K₀ :=
  (isMonotoneSurjOn_ι n).1

/-- `Δ` vanishes at every point of `K_n`. -/
theorem Δ_eq_zero (n : ℕ) {z : RealPt (A n)} (hz : z ∈ K n) : z (ι n Δ) = 0 :=
  mapsTo_K₀ n hz

/-- The functions `x`, `y` satisfy `x² + y² = 1` on `K_n`. -/
theorem circle (n : ℕ) {z : RealPt (A n)} (hz : z ∈ K n) :
    z (ι n x) ^ 2 + z (ι n y) ^ 2 = 1 :=
  K₀_circle (mapsTo_K₀ n hz)

/-- Every `K_n` is nonempty. -/
theorem K_nonempty (n : ℕ) : (K n).Nonempty := by
  induction n with
  | zero => exact ⟨circlePt 0, circlePt_mem 0⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨hmaps, hq⟩ := isMonotoneSurjOn_incl n
    obtain ⟨w, -⟩ := hq.surjective ⟨z, hz⟩
    exact ⟨w.1, w.2⟩

/-- **(5.2)** (`eq:nonorientable-stages`): for every `n`, the line bundle `L_n = L_{x,y}` on
`K_n` is nonorientable. It is the pullback of `L₀` along the composite `K_n → K_0` of the
transition maps, which is a monotone surjection by Lemma 2.2 (`isMonotoneSurjOn_ι`); hence
Lemma 2.1 applies. -/
theorem nonorientable (n : ℕ) :
    ¬ IsOrientable (fun z : K n => z.1 (ι n x)) (fun z : K n => z.1 (ι n y)) :=
  not_isOrientable_pullback (ι n) x y (isCompact_K n) (isMonotoneSurjOn_ι n)
    (fun _ hz => K₀_circle hz) L₀_not_isOrientable

end CL

open CL

/-! ## The ring `R = ⋃ A_n` -/

/-- **The ring `R = ⋃_{n ≥ 0} A_n`** (5.1), the direct limit of the injections
`A_0 ↪ A_1 ↪ A_2 ↪ ⋯` of Construction 5.1. -/
def RL : Type := Ring.DirectLimit (fun n => (A n : Type)) fun _ _ h => ⇑(inclLE h)

namespace RL

instance : CommRing RL := inferInstanceAs (CommRing (Ring.DirectLimit _ _))

/-- The inclusion `A_n ↪ RL`. -/
def of (n : ℕ) : A n →+* RL := Ring.DirectLimit.of (fun n => (A n : Type)) _ n

lemma of_inclLE {i j : ℕ} (h : i ≤ j) (a : A i) : of j (inclLE h a) = of i a :=
  Ring.DirectLimit.of_f (G := fun n => (A n : Type)) (f := fun _ _ h => ⇑(inclLE h)) h a

lemma of_incl (n : ℕ) (a : A n) : of (n + 1) (incl n a) = of n a := by
  rw [← inclLE_succ_self, of_inclLE]

/-- Every `A_n → RL` is injective: we identify `A_n` with its image in `RL`. -/
lemma of_injective (n : ℕ) : Function.Injective (of n) :=
  Ring.DirectLimit.of_injective (G := fun n => (A n : Type)) (fun _ _ h => inclLE h)
    (fun _ _ h => inclLE_injective h) n

lemma exists_of (r : RL) : ∃ n a, of n a = r := Ring.DirectLimit.exists_of r

/-- Any finite family of elements of `RL` lies in a single `A_n`. -/
lemma exists_of_fin (k : ℕ) (v : Fin k → RL) :
    ∃ (n : ℕ) (w : Fin k → A n), ∀ t, of n (w t) = v t := by
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

/-- The inclusion `A₀ ↪ RL`. -/
def ι : A₀ →+* RL := of 0

lemma of_ι (n : ℕ) (a : A₀) : of n (CL.ι n a) = ι a :=
  of_inclLE (Nat.zero_le n) a

/-- `A₀ → RL` is injective. -/
lemma ι_injective : Function.Injective ι := of_injective 0

instance : Nontrivial RL := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have : of 0 0 = of 0 1 := by simpa using h
  exact zero_ne_one (of_injective 0 this)

/-- An increasing union of domains is a domain. -/
instance isDomain : IsDomain RL := by
  have : NoZeroDivisors RL := ⟨fun {a b} hab => by
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

/-- `RL` is countable, because every `A_n` is countable. -/
instance countable : Countable RL := by
  have : Function.Surjective fun p : Σ n, (A n : Type) => of p.1 p.2 := by
    intro r
    obtain ⟨n, a, h⟩ := exists_of r
    exact ⟨⟨n, a⟩, h⟩
  exact this.countable

/-- **`RL` is a Bézout domain.** Let `a, b ∈ RL`; choose `i` with `a, b ∈ A_i` and `j` with
`η_i(j) = (a, b)`. This pair is processed when passing from `A_n` to `A_{n+1}`, `n = ⟨i, j⟩`,
so `(a, b) A_{n+1} = g A_{n+1}` for some `g ∈ A_{n+1}`; extension to `RL` gives `(a, b) RL = g RL`. -/
instance isBezout : IsBezout RL := by
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
      incl n (inclLE (left_le_pairing i j) (w 1))} : Ideal (A (n + 1))) = Ideal.span {g} := by
    refine Eq.trans ?_ hg
    rw [Ideal.map_span, Set.image_pair, hpair]
  have hmap := congrArg (Ideal.map (of (n + 1))) hg'
  rw [Ideal.map_span, Ideal.map_span, Set.image_pair, Set.image_singleton, of_incl, of_incl,
    of_inclLE, of_inclLE, hw 0, hw 1] at hmap
  exact ⟨⟨of (n + 1) g, by simpa using hmap⟩⟩

/-- `RL` is a `ℚ`-algebra (it contains `ℚ ⊆ A₀`). -/
instance : Algebra ℚ RL := ((ι).comp (algebraMap ℚ A₀)).toAlgebra

/-- `RL` has characteristic zero, since it contains `ℚ`. -/
instance charZero : CharZero RL :=
  charZero_of_injective_algebraMap (algebraMap ℚ RL).injective

end RL

end BezoutCounterexample
