import BezoutCounterexample.Constructive.NagataGCD

/-!
# Nagata's criterion with an escape (D5; `docs/d5-plan.md`, step 3)

Dynamical form of `hasGcd_of_away`. There, `p` is prime, and primality is used only in
`dvd_of_dvd_pow_mul` (`p ∣ c x`, `p ∤ c` give `p ∣ x`). Here `p` is **prime up to `Q`**
(`hpQ : p ∣ x y → p ∣ x ∨ p ∣ y ∨ Q`); in the D5 use `p = s` in the torsor and `Q = RadSplit P`
(`torsor_s_dyn`).

Since the gcd property quantifies over all common divisors, the escape is per query:
`IsGcdQ Q g a b` says `g ∣ a`, `g ∣ b`, and `c ∣ g` for every common divisor `c`, each up to `Q`.
If `Q` holds, every `g` qualifies (`isGcdQ_of_Q`).

* `dvd_of_dvd_pow_mul_dyn`, `dvd_of_dvd_away_dyn`: the two divisibility descents, up to `Q`.
* `hasGcd_of_away_dyn`: if `A[1/p]` has gcds up to `Q`, so has `A`. The domain, zero test and
  `p`-adic valuations (`hval`, from the bar) are as in `hasGcd_of_away`; `p ≠ 0` replaces
  `hp.ne_zero`.
-/

namespace BezoutCounterexample.Constructive

section Gcd

variable {A : Type*} [CommRing A]

/-- `g` is a gcd of `a` and `b`, up to `Q`. -/
def IsGcdQ (Q : Prop) (g a b : A) : Prop :=
  (g ∣ a ∨ Q) ∧ (g ∣ b ∨ Q) ∧ ∀ c, c ∣ a → c ∣ b → c ∣ g ∨ Q

lemma isGcdQ_of_Q {Q : Prop} (hQ : Q) (g a b : A) : IsGcdQ Q g a b :=
  ⟨Or.inr hQ, Or.inr hQ, fun _ _ _ => Or.inr hQ⟩

lemma isGcdQ_of_isGcd (Q : Prop) {g a b : A} (h : IsGcd g a b) : IsGcdQ Q g a b :=
  ⟨Or.inl h.1, Or.inl h.2.1, fun c ha hb => Or.inl (h.2.2 c ha hb)⟩

end Gcd

section Nagata

variable {A : Type*} [CommRing A] [IsDomain A] {p : A} (hp0 : p ≠ 0) {Q : Prop}
  (hpQ : ∀ x y : A, p ∣ x * y → p ∣ x ∨ p ∣ y ∨ Q)

include hp0 hpQ in
/-- If `p ∤ c` and `c ∣ pʲ w`, then `c ∣ w`, up to `Q`. -/
lemma dvd_of_dvd_pow_mul_dyn {c w : A} (hc : ¬ p ∣ c) : ∀ j : ℕ, c ∣ p ^ j * w → c ∣ w ∨ Q
  | 0, h => Or.inl (by rwa [pow_zero, one_mul] at h)
  | j + 1, h => by
    obtain ⟨x, hx⟩ := h
    have hpx : p ∣ c * x := ⟨p ^ j * w, by rw [← hx]; ring⟩
    rcases hpQ _ _ hpx with h1 | ⟨x', rfl⟩ | hQ
    · exact absurd h1 hc
    · refine dvd_of_dvd_pow_mul_dyn hc j ⟨x', mul_left_cancel₀ hp0 ?_⟩
      rw [← mul_assoc, ← pow_succ', hx]; ring
    · exact Or.inr hQ

variable (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.Away p L]

include hp0 hpQ in
/-- For `p ∤ c`, divisibility by `c` in `A[1/p]` descends to `A`, up to `Q`. -/
lemma dvd_of_dvd_away_dyn {c b : A} (hc : ¬ p ∣ c) (h : algebraMap A L c ∣ algebraMap A L b) :
    c ∣ b ∨ Q := by
  obtain ⟨e, he⟩ := h
  obtain ⟨⟨f, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers p) e
  have h1 : algebraMap A L (b * p ^ n) = algebraMap A L (c * f) := by
    rw [map_mul, he, map_mul, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers p) L).1 h1
  refine dvd_of_dvd_pow_mul_dyn hp0 hpQ hc (k + n) ⟨p ^ k * f, ?_⟩
  simp only at hk
  rw [pow_add]; linear_combination hk

include hp0 hpQ in
/-- **Nagata's criterion, GCD form, up to `Q`.** -/
theorem hasGcd_of_away_dyn (hzero : ∀ a : A, a = 0 ∨ a ≠ 0)
    (hval : ∀ a : A, a ≠ 0 → ∃ n : ℕ, ∃ c : A, a = p ^ n * c ∧ ¬ p ∣ c)
    (hL : ∀ x y : L, ∃ g, IsGcdQ Q g x y) (a b : A) : ∃ g, IsGcdQ Q g a b := by
  have hinj : Function.Injective (algebraMap A L) :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors hp0)
  rcases hzero a with rfl | ha
  · exact ⟨b, isGcdQ_of_isGcd Q (isGcd_zero_left b)⟩
  rcases hzero b with rfl | hb
  · exact ⟨a, isGcdQ_of_isGcd Q (isGcd_zero_right a)⟩
  obtain ⟨m, a', rfl, ha'⟩ := hval a ha
  obtain ⟨n, b', rfl, hb'⟩ := hval b hb
  obtain ⟨gL, hga, hgb, hgc⟩ := hL (algebraMap A L a') (algebraMap A L b')
  rcases hga with hga | hQ
  swap; · exact ⟨0, isGcdQ_of_Q hQ _ _ _⟩
  rcases hgb with hgb | hQ
  swap; · exact ⟨0, isGcdQ_of_Q hQ _ _ _⟩
  have hgL : gL ≠ 0 := by
    rintro rfl
    apply ha
    have : algebraMap A L a' = 0 := zero_dvd_iff.1 hga
    rw [hinj (this.trans (map_zero _).symm), mul_zero]
  obtain ⟨e, he, hge, heg⟩ := exists_assoc_away L hval hgL
  rcases dvd_of_dvd_away_dyn hp0 hpQ L he (heg.trans hga) with hea | hQ
  swap; · exact ⟨0, isGcdQ_of_Q hQ _ _ _⟩
  rcases dvd_of_dvd_away_dyn hp0 hpQ L he (heg.trans hgb) with heb | hQ
  swap; · exact ⟨0, isGcdQ_of_Q hQ _ _ _⟩
  refine ⟨p ^ min m n * e, Or.inl (mul_dvd_mul (pow_dvd_pow p (min_le_left m n)) hea),
    Or.inl (mul_dvd_mul (pow_dvd_pow p (min_le_right m n)) heb), fun c hca hcb => ?_⟩
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
      exact (mul_dvd_mul_iff_left (pow_ne_zero k hp0)).1 h1
    · exact hkr
  have hrm := hle m a' ha' hca
  have hrn := hle n b' hb' hcb
  -- `c' ∣ e`, up to `Q`
  rcases dvd_of_dvd_pow_mul_dyn hp0 hpQ hc' m (dvd_trans (dvd_mul_left c' _) hca) with hca' | hQ
  swap; · exact Or.inr hQ
  rcases dvd_of_dvd_pow_mul_dyn hp0 hpQ hc' n (dvd_trans (dvd_mul_left c' _) hcb) with hcb' | hQ
  swap; · exact Or.inr hQ
  rcases hgc _ (map_dvd _ hca') (map_dvd _ hcb') with hcg | hQ
  swap; · exact Or.inr hQ
  rcases dvd_of_dvd_away_dyn hp0 hpQ L hc' (hcg.trans hge) with hce | hQ
  swap; · exact Or.inr hQ
  exact Or.inl (mul_dvd_mul (pow_dvd_pow p (le_min hrm hrn)) hce)

end Nagata

end BezoutCounterexample.Constructive
