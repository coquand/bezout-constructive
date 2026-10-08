import BezoutCounterexample.Constructive.FactorialField
import BezoutCounterexample.Constructive.PrimitiveShift
import Mathlib.FieldTheory.Separable

/-!
# Simple algebraic extensions of factorial fields (option 2, M2b; Kronecker/Trager, MRR VII)

`K` factorial of characteristic `0`, `p ∈ K[Y]` irreducible, `L = K[Y] ⧸ (p)` with `α` the root.
For `f ∈ L[X]` put `B = L[X] ⧸ (f)` and `θ_c = X + c α ∈ B` (`c ∈ ℕ ⊆ K`).

* `exists_primitive_shift'` (`Constructive/PrimitiveShift`, constructive, no trusted primitive): if `f`
  is separable (`IsCoprime f f'`), some `θ_c` (`c ∈ ℕ`) is annihilated by a nonzero `μ ∈ K[T]` and
  `K[T] → B`, `T ↦ θ_c`, is surjective. Proof by the `∂_T` trick: `θ_T = X + Tα` in `B[T]` has a
  separable annihilator `Q` over `K(T)` (`B[T]` is reduced), and `∂_T(Q(θ_T)) = 0` gives
  `d(T) α, d(T) X ∈ K[T][θ_T]` with `d ≠ 0`; specialising at `c` with `d(c) ≠ 0` makes `θ_c` primitive.
  (It replaced the former `@[cprim]` `exists_primitive_shift` with its ¬¬-argument via splitting fields.)
* `fsAt_of_primitive` (**recovery**, constructive, no squarefreeness): if `θ = X + cα` generates
  `B` and `μ(θ) = 0`, `μ ≠ 0`, then every factor `g` of `f` is associated to
  `gcd_L(f, (∏J)(X + cα))` for a sublist `J` of a factorisation of `μ` over `K`: take `q₀` with
  `q₀(θ) = g`, `h = gcd(μ, q₀) = aμ + b q₀`; then `h ∼ ∏J`, `g ∣ h(X + cα)` and
  `gcd(f, h(X + cα)) ∣ q₀(X + cα) ≡ g`.
* `fsAt_mul`: the factor search at `a` and `b` gives it at `a b` (a factor `g` of `ab` with
  constant `gcd(g, a)` divides `b`).
* `factorSearch_adjoin`: strong induction on `deg f`, splitting off `gcd(f, f')` until `f` is
  separable. `factorialField_adjoin : FactorialField K → FactorialField (AdjoinRoot p)`.
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open Polynomial

/-- Factor search at one polynomial. -/
def FSAt {F : Type*} [CommRing F] (f : F[X]) : Prop :=
  ∀ d : ℕ, (∃ g : F[X], 0 < g.natDegree ∧ g.natDegree ≤ d ∧ g ∣ f) ∨
    ∀ g : F[X], g ∣ f → g.natDegree ≤ d → g.natDegree = 0

section Generic

variable {F : Type*} [Field F] (hz : ∀ x : F, x = 0 ∨ x ≠ 0)
include hz

/-- The factor search is closed under products. -/
theorem fsAt_mul {a b : F[X]} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : FSAt a) (hb : FSAt b) :
    FSAt (a * b) := by
  intro d
  rcases ha d with ⟨g, h1, h2, h3⟩ | ha'
  · exact Or.inl ⟨g, h1, h2, dvd_mul_of_dvd_left h3 b⟩
  rcases hb d with ⟨g, h1, h2, h3⟩ | hb'
  · exact Or.inl ⟨g, h1, h2, dvd_mul_of_dvd_right h3 a⟩
  refine Or.inr fun g hg hgd => ?_
  have hg0 : g ≠ 0 := fun h => mul_ne_zero ha0 hb0 (zero_dvd_iff.1 (h ▸ hg))
  obtain ⟨G, u, v, hG, huv⟩ := bezout_field hz g a
  have hG0 : G ≠ 0 := fun h => hg0 (zero_dvd_iff.1 (h ▸ hG.1))
  have hdeg : G.natDegree = 0 := ha' G hG.2.1 ((natDegree_le_of_dvd hG.1 hg0).trans hgd)
  have hcop : IsCoprime g a := isCoprime_of_isGcd_unit huv
    (isUnit_of_natDegree_eq_zero_field hG0 hdeg)
  exact hb' g (hcop.dvd_of_dvd_mul_left hg) hgd

omit hz in
lemma natDegree_eq_of_isGcd {f q G G' : F[X]} (hf : f ≠ 0) (h1 : IsGcd G f q) (h2 : IsGcd G' f q) :
    G.natDegree = G'.natDegree := by
  have hG : G ≠ 0 := fun h => hf (zero_dvd_iff.1 (h ▸ h1.1))
  have hG' : G' ≠ 0 := fun h => hf (zero_dvd_iff.1 (h ▸ h2.1))
  exact le_antisymm (natDegree_le_of_dvd (h2.2.2 G h1.1 h1.2.1) hG')
    (natDegree_le_of_dvd (h1.2.2 G' h2.1 h2.2.1) hG)

end Generic

section Adjoin

variable {K : Type*} [Field K] {p : K[X]} [Fact (Irreducible p)]

variable (hK : FactorialField K)
include hK

/-- **Recovery**: with a primitive `θ = X + cα` and an annihilator, factor search at `f`. -/
theorem fsAt_of_primitive {f : (AdjoinRoot p)[X]} (hf0 : f ≠ 0) (c : K)
    {μ : K[X]} (hμ : μ ≠ 0) (hμθ : aeval (theta f c) μ = 0)
    (hsurj : ∀ b : AdjoinRoot f, ∃ q : K[X], aeval (theta f c) q = b) : FSAt f := by
  set L := AdjoinRoot p
  have hzL : ∀ x : L, x = 0 ∨ x ≠ 0 := zeroTest_adjoin hK
  -- the lift `q ↦ q(X + cα)` and its compatibility with `θ`
  let ψ : K[X] →ₐ[K] L[X] := aeval (X + C (algebraMap K L c * AdjoinRoot.root p))
  let mkK : L[X] →ₐ[K] AdjoinRoot f := (AdjoinRoot.mkₐ f).restrictScalars K
  have hmk : ∀ q : K[X], AdjoinRoot.mk f (ψ q) = aeval (theta f c) q := by
    intro q
    have : mkK (ψ q) = aeval (mkK (X + C (algebraMap K L c * AdjoinRoot.root p))) q :=
      (aeval_algHom_apply mkK _ q).symm
    have hX : mkK (X + C (algebraMap K L c * AdjoinRoot.root p)) = theta f c := by
      simp only [mkK, AlgHom.restrictScalars_apply, map_add]
      rfl
    rw [hX] at this
    exact this
  obtain ⟨u, l, hu, hl, hμl⟩ := hK.exists_factorisation hμ
  intro d
  let P : List K[X] → Prop := fun J =>
    ∃ G : L[X], IsGcd G f (ψ J.prod) ∧ 0 < G.natDegree ∧ G.natDegree ≤ d
  have hP : ∀ J, P J ∨ ¬ P J := by
    intro J
    obtain ⟨G, hG⟩ := exists_isGcd_polynomial_field L hzL f (ψ J.prod)
    rcases Decidable.em (0 < G.natDegree ∧ G.natDegree ≤ d) with h | h
    · exact Or.inl ⟨G, hG, h⟩
    · refine Or.inr fun ⟨G', hG', h'⟩ => h ?_
      rw [natDegree_eq_of_isGcd hf0 hG hG']; exact h'
  rcases Multiset.exists_or_forall_not' (l.sublists : Multiset (List K[X])) hP with
    ⟨J, -, G, hG, h1, h2⟩ | hn
  · exact Or.inl ⟨G, h1, h2, hG.1⟩
  refine Or.inr fun g hg hgd => ?_
  rcases Nat.eq_zero_or_pos g.natDegree with h0 | hpos
  · exact h0
  exfalso
  have hg0 : g ≠ 0 := fun h => hf0 (zero_dvd_iff.1 (h ▸ hg))
  obtain ⟨q₀, hq₀⟩ := hsurj (AdjoinRoot.mk f g)
  obtain ⟨h, a, b, hh, hab⟩ := bezout_field hK.zero μ q₀
  have hhl : h ∣ l.prod := by
    have := hh.1; rw [hμl] at this; exact hu.dvd_mul_left.1 this
  obtain ⟨J, hJ, w, hw⟩ := hK.exists_sublist_associated l hl h hhl
  obtain ⟨G, hG⟩ := exists_isGcd_polynomial_field L hzL f (ψ J.prod)
  have hJψ : ψ J.prod = ψ h * ψ (w : K[X]) := by rw [← hw, map_mul]
  have hwu : IsUnit (ψ (w : K[X])) := w.isUnit.map ψ
  -- `g ∣ ψ h`
  have hgh : g ∣ ψ h := by
    have hmkh : AdjoinRoot.mk f (ψ h) = AdjoinRoot.mk f (ψ b * g) := by
      rw [hmk, ← hab, map_add, map_mul, map_mul, hμθ, mul_zero, zero_add, map_mul, hmk, hq₀]
    have := (AdjoinRoot.mk_eq_mk.1 hmkh)
    have h3 := dvd_add (hg.trans this) (dvd_mul_left g (ψ b))
    rwa [sub_add_cancel] at h3
  have hgG : g ∣ G := hG.2.2 g hg (by rw [hJψ]; exact dvd_mul_of_dvd_left hgh _)
  -- `G ∣ g`
  have hGh : G ∣ ψ h := by
    have := hG.2.1; rw [hJψ] at this; exact hwu.dvd_mul_right.1 this
  have hGq : G ∣ ψ q₀ := by
    obtain ⟨k, hk⟩ := hh.2.1
    exact hGh.trans ⟨ψ k, by rw [hk, map_mul]⟩
  have hGg : G ∣ g := by
    have h3 : f ∣ ψ q₀ - g := AdjoinRoot.mk_eq_mk.1 (by rw [hmk, hq₀])
    have h4 := dvd_sub hGq (hG.1.trans h3)
    rwa [sub_sub_cancel] at h4
  have hG0 : G ≠ 0 := fun h => hg0 (zero_dvd_iff.1 (h ▸ hGg))
  have hdeg : G.natDegree = g.natDegree :=
    le_antisymm (natDegree_le_of_dvd hGg hg0) (natDegree_le_of_dvd hgG hG0)
  have hP' : P J := ⟨G, hG, by rw [hdeg]; exact hpos, by rw [hdeg]; exact hgd⟩
  exact hn J (Multiset.mem_coe.2 hJ) hP'

/-- Factor search over `K[Y] ⧸ (p)`. -/
theorem factorSearch_adjoin [CharZero K] : FactorSearch (AdjoinRoot p) := by
  set L := AdjoinRoot p
  have hzL : ∀ x : L, x = 0 ∨ x ≠ 0 := zeroTest_adjoin hK
  -- the projection instance (otherwise inference goes through `Field.henselian`)
  letI : Nontrivial L := DivisionRing.toNontrivial
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  suffices H : ∀ n, ∀ f : L[X], f ≠ 0 → f.natDegree = n → FSAt f from
    fun f hf => H _ f hf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf hn
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · exact fun d => Or.inr fun g hg _ => by
      have := natDegree_le_of_dvd hg hf; omega
  obtain ⟨D, u, v, hD, huv⟩ := bezout_field hzL f (derivative f)
  have hf' : derivative f ≠ 0 := derivative_ne_zero.2 (by omega)
  have hDlt : D.natDegree < f.natDegree :=
    (natDegree_le_of_dvd hD.2.1 hf').trans_lt (natDegree_derivative_lt (by omega))
  have hD0 : D ≠ 0 := fun h => hf (zero_dvd_iff.1 (h ▸ hD.1))
  rcases Nat.eq_zero_or_pos D.natDegree with hD1 | hD1
  · have hcop : IsCoprime f (derivative f) :=
      isCoprime_of_isGcd_unit huv (isUnit_of_natDegree_eq_zero_field hD0 hD1)
    obtain ⟨c, ⟨μ, hμ, hμθ⟩, hsurj⟩ := exists_primitive_shift' hK hcop hpos
    exact fsAt_of_primitive hK hf (c : K) hμ hμθ hsurj
  obtain ⟨k, hk⟩ := hD.1
  have hk0 : k ≠ 0 := fun h => hf (by rw [hk, h, mul_zero])
  have hdeg := natDegree_mul hD0 hk0
  rw [← hk] at hdeg
  rw [hk]
  exact fsAt_mul hzL hD0 hk0 (ih _ (by omega) D hD0 rfl) (ih _ (by omega) k hk0 rfl)

/-- **`K ↝ K[Y] ⧸ (p)`**: a simple algebraic extension of a factorial field of characteristic
`0` is factorial. -/
theorem factorialField_adjoin [CharZero K] : FactorialField (AdjoinRoot p) :=
  ⟨zeroTest_adjoin hK, factorSearch_adjoin hK⟩

end Adjoin

end BezoutCounterexample.Constructive
