import BezoutCounterexample.Constructive.ValBar

/-!
# Nagata's criterion for GCD domains (`~/COLL/bezout-gcd.tex`, Proposition 5.1)

GCD domains are stated propositionally: `HasGcd A` says that every pair has a gcd. Read
constructively this is the gcd algorithm; no normalisation of associates is required (unlike
Mathlib's `NormalizedGCDMonoid`).

`hasGcd_of_away`: let `p` be a prime element of a domain `A` with decidable zero test and
computable `p`-adic valuations. If `A[1/p]` has gcds, so has `A`. Compared with Mathlib/HM's UFD
version (`Factoriality.of_isLocalization_away`), neither Noetherianity nor well-founded
divisibility is used; the valuation is the only finiteness input, and in the development it comes
from the bar (`IndNoeth.exists_val`).
-/

namespace BezoutCounterexample.Constructive

section Gcd

variable {A : Type*} [CommRing A]

/-- `g` is a gcd of `a` and `b`. -/
def IsGcd (g a b : A) : Prop := g ∣ a ∧ g ∣ b ∧ ∀ c, c ∣ a → c ∣ b → c ∣ g

/-- Every pair has a gcd. -/
def HasGcd (A : Type*) [CommRing A] : Prop := ∀ a b : A, ∃ g, IsGcd g a b

lemma isGcd_zero_left (b : A) : IsGcd b 0 b := ⟨dvd_zero b, dvd_rfl, fun _ _ h => h⟩

lemma isGcd_zero_right (a : A) : IsGcd a a 0 := ⟨dvd_rfl, dvd_zero a, fun _ h _ => h⟩

end Gcd

section Nagata

variable {A : Type*} [CommRing A] [IsDomain A] {p : A} (hp : Prime p)
include hp

/-- If `p ∤ c` and `c ∣ pʲ w`, then `c ∣ w`. -/
lemma dvd_of_dvd_pow_mul {c w : A} (hc : ¬ p ∣ c) : ∀ j : ℕ, c ∣ p ^ j * w → c ∣ w
  | 0, h => by rwa [pow_zero, one_mul] at h
  | j + 1, h => by
    apply dvd_of_dvd_pow_mul hc j
    obtain ⟨x, hx⟩ := h
    have hpx : p ∣ c * x := ⟨p ^ j * w, by rw [← hx]; ring⟩
    rcases hp.dvd_or_dvd hpx with h1 | ⟨x', rfl⟩
    · exact absurd h1 hc
    · refine ⟨x', mul_left_cancel₀ hp.ne_zero ?_⟩
      rw [← mul_assoc, ← pow_succ', hx]; ring

variable (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.Away p L]

/-- For `p ∤ c`, divisibility by `c` in `A[1/p]` descends to `A`. -/
lemma dvd_of_dvd_away {c b : A} (hc : ¬ p ∣ c) (h : algebraMap A L c ∣ algebraMap A L b) :
    c ∣ b := by
  obtain ⟨e, he⟩ := h
  obtain ⟨⟨f, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers p) e
  have h1 : algebraMap A L (b * p ^ n) = algebraMap A L (c * f) := by
    rw [map_mul, he, map_mul, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers p) L).1 h1
  refine dvd_of_dvd_pow_mul hp hc (k + n) ⟨p ^ k * f, ?_⟩
  simp only at hk
  rw [pow_add]; linear_combination hk

omit [IsDomain A] hp in
/-- Every nonzero element of `A[1/p]` is associated to some `e ∈ A` with `p ∤ e`. -/
lemma exists_assoc_away
    (hval : ∀ a : A, a ≠ 0 → ∃ n : ℕ, ∃ c : A, a = p ^ n * c ∧ ¬ p ∣ c)
    {x : L} (hx : x ≠ 0) :
    ∃ e : A, ¬ p ∣ e ∧ x ∣ algebraMap A L e ∧ algebraMap A L e ∣ x := by
  obtain ⟨⟨a, ⟨_, j, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers p) x
  have ha : a ≠ 0 := by
    rintro rfl; exact hx (IsLocalization.mk'_zero _)
  obtain ⟨n, e, rfl, he⟩ := hval a ha
  dsimp only at hx ⊢
  have hspec := IsLocalization.mk'_spec L (p ^ n * e) (⟨p ^ j, j, rfl⟩ : Submonoid.powers p)
  simp only at hspec
  have hun : IsUnit (algebraMap A L (p ^ n)) := IsLocalization.map_units L (⟨p ^ n, n, rfl⟩ : Submonoid.powers p)
  have huj : IsUnit (algebraMap A L (p ^ j)) := IsLocalization.map_units L (⟨p ^ j, j, rfl⟩ : Submonoid.powers p)
  refine ⟨e, he, ?_, ?_⟩
  · rw [← hun.dvd_mul_left, ← map_mul, ← hspec]
    exact dvd_mul_right _ _
  · rw [← huj.dvd_mul_right, hspec, map_mul]
    exact dvd_mul_left _ _

/-- **Nagata's criterion, GCD form.** -/
theorem hasGcd_of_away (hzero : ∀ a : A, a = 0 ∨ a ≠ 0)
    (hval : ∀ a : A, a ≠ 0 → ∃ n : ℕ, ∃ c : A, a = p ^ n * c ∧ ¬ p ∣ c)
    (hL : HasGcd L) : HasGcd A := by
  have hinj : Function.Injective (algebraMap A L) :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors hp.ne_zero)
  intro a b
  rcases hzero a with rfl | ha
  · exact ⟨b, isGcd_zero_left b⟩
  rcases hzero b with rfl | hb
  · exact ⟨a, isGcd_zero_right a⟩
  obtain ⟨m, a', rfl, ha'⟩ := hval a ha
  obtain ⟨n, b', rfl, hb'⟩ := hval b hb
  obtain ⟨gL, hga, hgb, hgc⟩ := hL (algebraMap A L a') (algebraMap A L b')
  have hgL : gL ≠ 0 := by
    rintro rfl
    apply ha
    have : algebraMap A L a' = 0 := zero_dvd_iff.1 hga
    rw [hinj (this.trans (map_zero _).symm), mul_zero]
  obtain ⟨e, he, hge, heg⟩ := exists_assoc_away L hval hgL
  have hea : e ∣ a' := dvd_of_dvd_away hp L he (heg.trans hga)
  have heb : e ∣ b' := dvd_of_dvd_away hp L he (heg.trans hgb)
  refine ⟨p ^ min m n * e, mul_dvd_mul (pow_dvd_pow p (min_le_left m n)) hea,
    mul_dvd_mul (pow_dvd_pow p (min_le_right m n)) heb, fun c hca hcb => ?_⟩
  have hc : c ≠ 0 := by
    rintro rfl; exact ha (zero_dvd_iff.1 hca)
  obtain ⟨r, c', rfl, hc'⟩ := hval c hc
  -- `r ≤ m` and `r ≤ n`
  have hle : ∀ (k : ℕ) (x : A), ¬ p ∣ x → p ^ r * c' ∣ p ^ k * x → r ≤ k := by
    intro k x hx h
    rcases Nat.lt_or_ge k r with hkr | hkr
    · exfalso
      apply hx
      have h1 : p ^ k * p ∣ p ^ k * x := by
        refine dvd_trans ?_ h
        rw [← pow_succ]
        exact dvd_mul_of_dvd_left (pow_dvd_pow p hkr) _
      exact (mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).1 h1
    · exact hkr
  have hrm := hle m a' ha' hca
  have hrn := hle n b' hb' hcb
  -- `c' ∣ e`
  have hca' : c' ∣ a' := dvd_of_dvd_pow_mul hp hc' m (dvd_trans (dvd_mul_left c' _) hca)
  have hcb' : c' ∣ b' := dvd_of_dvd_pow_mul hp hc' n (dvd_trans (dvd_mul_left c' _) hcb)
  have hce : c' ∣ e := dvd_of_dvd_away hp L hc'
    ((hgc _ (map_dvd _ hca') (map_dvd _ hcb')).trans hge)
  exact mul_dvd_mul (pow_dvd_pow p (le_min hrm hrn)) hce

end Nagata

end BezoutCounterexample.Constructive
