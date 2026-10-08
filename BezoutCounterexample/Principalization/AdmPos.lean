import BezoutCounterexample.Principalization.StepPos
import BezoutCounterexample.Constructive.ChartP
import BezoutCounterexample.Constructive.PosF2

/-!
# Admissibility decided at a point (D3.4 (a), leaf)

Method 1 (`spread_run`, `MC.SA.step_run`) branches on `MC.Adm I J` by `by_cases`, and
`SA.step_data_Q` gets its first candidate from `¬ J.Adm I` by `by_contra` and (F2). Here the
branch is decided positively, in a local ring with `[Fact (PolyIndNoeth R)]` and a decided
residue field (`hdec`; at an explicit point: the point's zero test):

* `Constructive.quotDer`: a derivation preserving an ideal `J` descends to `R ⧸ J`;
* `Chart.IsCentred.head_or_escape` (positive (F2)): `g` lies in the head ideal `(xᵢ : eᵢ ≠ 0)`,
  or some tail derivative `∂^δ g` (`δ` supported where `eᵢ = 0`) is a unit. This is `pos_F2` on
  `R ⧸ head e` with the images of the tail coordinates (Rees bar from `PolyIndNoeth.quotient`);
* `MC.adm_or_witness`: for `I = (l)`, either `J.Adm I`, or a generator `f ∈ l` and `β₀` with
  `coeff_β₀(τ f) ≠ 0` and `λ_e(β₀) < 1`, which is the input of `SA.step_data_pos`. The head
  multi-indices with `λ_e(β) < 1` lie in an explicit box (`βᵢ ≤ den eᵢ`), and `mem_RF_iff_P`
  reduces admissibility to `head_or_escape` on finitely many `∂^β f`.

Leaf module; the consumers (Spread, Globalize) switch in the D3.5 integration diff.
-/

noncomputable section

namespace BezoutCounterexample.Constructive

section QuotDer

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The map `R ⧸ J → R ⧸ J` induced by a derivation preserving `J`. -/
def quotDerFun (J : Ideal R) (δ : Derivation ℚ R R) (hδ : ∀ x ∈ J, δ x ∈ J) : R ⧸ J → R ⧸ J :=
  fun y => Quotient.liftOn' y (fun r => Ideal.Quotient.mk J (δ r)) fun a b h => by
    rw [Submodule.quotientRel_def] at h
    rw [Ideal.Quotient.eq, ← map_sub]
    exact hδ _ h

lemma quotDerFun_mk (J : Ideal R) (δ : Derivation ℚ R R) (hδ : ∀ x ∈ J, δ x ∈ J) (r : R) :
    quotDerFun J δ hδ (Ideal.Quotient.mk J r) = Ideal.Quotient.mk J (δ r) := rfl

/-- **A derivation preserving `J` descends to `R ⧸ J`.** -/
def quotDer (J : Ideal R) (δ : Derivation ℚ R R) (hδ : ∀ x ∈ J, δ x ∈ J) :
    Derivation ℚ (R ⧸ J) (R ⧸ J) where
  toFun := quotDerFun J δ hδ
  map_add' a b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_add, quotDerFun_mk, quotDerFun_mk, quotDerFun_mk, map_add, map_add]
  map_smul' q a := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hs : ∀ y : R, q • Ideal.Quotient.mk J y = Ideal.Quotient.mk J (q • y) := fun y => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]
    rw [RingHom.id_apply, hs, quotDerFun_mk, quotDerFun_mk, δ.map_smul, hs]
  map_one_eq_zero' := by
    show quotDerFun J δ hδ (Ideal.Quotient.mk J 1) = 0
    rw [quotDerFun_mk, δ.map_one_eq_zero, map_zero]
  leibniz' a b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    show quotDerFun J δ hδ (Ideal.Quotient.mk J a * Ideal.Quotient.mk J b) = _
    rw [← map_mul, quotDerFun_mk, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
    rfl

lemma quotDer_mk (J : Ideal R) (δ : Derivation ℚ R R) (hδ : ∀ x ∈ J, δ x ∈ J) (r : R) :
    quotDer J δ hδ (Ideal.Quotient.mk J r) = Ideal.Quotient.mk J (δ r) := rfl

end QuotDer

/-- Finitely many decisions, over a list. -/
lemma list_forall_or_exists {α : Type*} {P : α → Prop} {E : Prop} :
    ∀ L : List α, (∀ a ∈ L, P a ∨ E) → (∀ a ∈ L, P a) ∨ E
  | [], _ => Or.inl fun _ h => absurd h List.not_mem_nil
  | a :: L, h => by
    rcases h a List.mem_cons_self with ha | he
    · rcases list_forall_or_exists L fun b hb => h b (List.mem_cons_of_mem _ hb) with hL | he
      · exact Or.inl fun b hb => (List.mem_cons.1 hb).elim (fun e => e ▸ ha) (hL b)
      · exact Or.inr he
    · exact Or.inr he

/-- Finitely many decisions, over a finset. -/
lemma finset_forall_or_exists {α : Type*} [DecidableEq α] {P : α → Prop} {E : Prop}
    (s : Finset α) (h : ∀ a ∈ s, P a ∨ E) : (∀ a ∈ s, P a) ∨ E := by
  induction s using Finset.induction_on with
  | empty => exact Or.inl fun _ h => absurd h (Finset.notMem_empty _)
  | insert a s _ ih =>
    rcases h a (Finset.mem_insert_self _ _) with ha | he
    · rcases ih fun b hb => h b (Finset.mem_insert_of_mem hb) with hs | he
      · exact Or.inl fun b hb => (Finset.mem_insert.1 hb).elim (fun e => e ▸ ha) (hs b)
      · exact Or.inr he
    · exact Or.inr he

end BezoutCounterexample.Constructive


namespace BezoutCounterexample.Principalization

open MvPowerSeries IsLocalRing Constructive

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R] {n : ℕ}

namespace Chart

variable {c : Chart R n}

/-- The tail chart on `R ⧸ head e`: the images of the coordinates `ι a` (with `e (ι a) = 0`) and
the descended derivations. -/
def tailQ (c : Chart R n) (e : Fin n → ℚ) {k : ℕ} (ι : Fin k → Fin n)
    (hι : Function.Injective ι) (hz : ∀ a, e (ι a) = 0) : PChart (R ⧸ c.head e) k where
  x a := Ideal.Quotient.mk _ (c.x (ι a))
  d a := quotDer (c.head e) (c.d (ι a)) fun _ hx => c.d_mem_head (hz a) hx
  dual a b := by
    rw [quotDer_mk, c.d_x]
    by_cases h : a = b
    · subst h; simp
    · have h' : ι a ≠ ι b := fun e => h (hι e)
      simp [h, h']

lemma tailQ_Dl (c : Chart R n) (e : Fin n → ℚ) {k : ℕ} (ι : Fin k → Fin n)
    (hι : Function.Injective ι) (hz : ∀ a, e (ι a) = 0) (L : List (Fin k)) (g : R) :
    (c.tailQ e ι hι hz).Dl L (Ideal.Quotient.mk _ g) =
      Ideal.Quotient.mk _ (c.D (lsum ι L) g) := by
  induction L with
  | nil => rw [lsum_nil, c.D_zero]; rfl
  | cons a L ih =>
    rw [lsum_cons, add_comm, c.D_add_single, ← quotDer_mk _ _ fun _ hx => c.d_mem_head (hz a) hx,
      ← ih]
    rfl

/-- **Positive (F2)**: an element lies in the head ideal, or a tail derivative of it is a unit. -/
theorem IsCentred.head_or_escape [h : Fact (PolyIndNoeth R)] (hc : c.IsCentred)
    (hdec : ∀ x : R, x ∈ maximalIdeal R ∨ IsUnit x) (e : Fin n → ℚ) (g : R) :
    g ∈ c.head e ∨ ∃ δ : Fin n →₀ ℕ, (∀ i, e i ≠ 0 → δ i = 0) ∧ IsUnit (c.D δ g) := by
  obtain ⟨k, ι, hι, hrange⟩ := exists_enum (fun i => e i = 0)
  have hz : ∀ a, e (ι a) = 0 := fun a => (hrange _).2 ⟨a, rfl⟩
  set H := c.head e
  set P := c.tailQ e ι hι hz
  have hHm : H ≤ maximalIdeal R := hc.head_le e
  -- the maximal ideal is the head plus the tail
  have hsplit : maximalIdeal R ≤ H ⊔ Ideal.span (Set.range fun a => c.x (ι a)) := by
    rw [hc, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : e i = 0
    · obtain ⟨a, rfl⟩ := (hrange i).1 hi
      exact Ideal.mem_sup_right (Ideal.subset_span ⟨a, rfl⟩)
    · exact Ideal.mem_sup_left (c.x_mem_head hi)
  have hPmap : P.P = (Ideal.span (Set.range fun a => c.x (ι a))).map (Ideal.Quotient.mk H) := by
    rw [PChart.P, Ideal.map_span, ← Set.range_comp]; rfl
  have hPm : ∀ r : R, Ideal.Quotient.mk H r ∈ P.P → r ∈ maximalIdeal R := fun r hr => by
    rw [hPmap, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hr
    obtain ⟨t, ht, hrt⟩ := hr
    have htm : t ∈ maximalIdeal R := by
      rw [hc]; exact Ideal.span_mono (Set.range_comp_subset_range _ _) ht
    have : t - r ∈ H := by rw [← Ideal.Quotient.eq]; exact hrt
    simpa using sub_mem htm (hHm this)
  have hunit : ∀ r : R, IsUnit (Ideal.Quotient.mk H r) → IsUnit r := fun r hr => by
    rcases hdec r with hm | hu
    · obtain ⟨s, hs⟩ := hr.exists_right_inv
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
      rw [← map_mul, ← map_one (Ideal.Quotient.mk H), Ideal.Quotient.eq] at hs
      have h1 : (1 : R) ∈ maximalIdeal R := by
        have := sub_mem (Ideal.mul_mem_right s _ hm) (hHm hs)
        simpa using this
      exact absurd ((Ideal.eq_top_iff_one _).2 h1) (maximalIdeal.isMaximal R).ne_top
    · exact hu
  have hR : IndNoeth (reesSubring P.P) := by
    have hl := PolyIndNoeth.indNoeth_rees_lspan (h.out.quotient H) (List.ofFn P.x)
    have he : lspan (List.ofFn P.x) = P.P := by
      rw [PChart.P, lspan]
      congr 1
      ext y
      simp [List.mem_ofFn]
    rwa [he] at hl
  have hloc : ∀ a ∈ P.P, IsUnit (1 - a) := fun a ha => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hr := hPm r ha
    rcases hdec (1 - r) with h1 | hu
    · have h1' : (1 : R) ∈ maximalIdeal R := by simpa using Ideal.add_mem _ h1 hr
      exact absurd ((Ideal.eq_top_iff_one _).2 h1') (maximalIdeal.isMaximal R).ne_top
    · rw [← map_one (Ideal.Quotient.mk H), ← map_sub]; exact hu.map _
  have hdecS : ∀ s : R ⧸ H, s ∈ P.P ∨ IsUnit s := fun s => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    rcases hdec r with hm | hu
    · left
      obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 (hsplit hm)
      rw [hPmap, map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add]
      exact Ideal.mem_map_of_mem _ ht
    · exact Or.inr (hu.map _)
  rcases pos_F2 P hR hloc (E := IsUnit) hdecS (Ideal.Quotient.mk H g) with h0 | ⟨α, hα⟩
  · exact Or.inl (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  · refine Or.inr ⟨lsum ι (PChart.ofIdx α), fun i hi => lsum_apply_off ι _ fun a ha => ?_, ?_⟩
    · exact hi (ha ▸ hz a)
    · apply hunit
      rw [← tailQ_Dl c e ι hι hz]
      exact hα

end Chart

namespace MC

variable {I : Ideal R} {J : MC R n}

omit [IsLocalRing R] in
/-- A head multi-index with `λ_e(β) < 1` lies in the box `βᵢ ≤ den eᵢ`. -/
lemma le_den_of_lam_lt {e : Fin n → ℚ} (he : ∀ i, 0 ≤ e i) {β : Fin n →₀ ℕ}
    (hβ : ∀ i, e i = 0 → β i = 0) (hlt : lam e β < 1) (i : Fin n) : β i ≤ (e i).den := by
  rcases (he i).eq_or_lt with h0 | hpos
  · rw [hβ i h0.symm]; exact Nat.zero_le _
  · refine le_den_of_mul_lt_one hpos (lt_of_le_of_lt ?_ hlt)
    exact Finset.single_le_sum (f := fun i => (β i : ℚ) * e i)
      (fun i _ => mul_nonneg (Nat.cast_nonneg _) (he i)) (Finset.mem_univ i)

/-- **Admissibility, decided**: `J` is admissible for `(l)`, or a generator has a coefficient of
weight `< 1` (the first candidate of `SA.step_data_pos`). -/
theorem adm_or_witness [Fact (PolyIndNoeth R)] (hdec : ∀ x : R, x ∈ maximalIdeal R ∨ IsUnit x)
    (l : List R) (hl : I = lspan l) (J : MC R n) :
    J.Adm I ∨ ∃ f ∈ l, ∃ β₀ : Fin n →₀ ℕ, coeff β₀ (J.c.tau f) ≠ 0 ∧ lam J.e β₀ < 1 := by
  set E := ∃ f ∈ l, ∃ β₀ : Fin n →₀ ℕ, coeff β₀ (J.c.tau f) ≠ 0 ∧ lam J.e β₀ < 1
  set box : Finset (Fin n →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun i => (J.e i).den)
  have hbox : ∀ β : Fin n →₀ ℕ, (∀ i, J.e i = 0 → β i = 0) → lam J.e β < 1 → β ∈ box :=
    fun β hβ hlt => Finset.mem_Iic.2 fun i => by
      simpa using le_den_of_lam_lt J.nonneg hβ hlt i
  -- one generator, one head multi-index
  have hone : ∀ f ∈ l, ∀ β : Fin n →₀ ℕ,
      ((∀ i, J.e i = 0 → β i = 0) → lam J.e β < 1 → J.c.D β f ∈ J.c.head J.e) ∨ E := by
    intro f hf β
    rcases J.centred.head_or_escape hdec J.e (J.c.D β f) with hh | ⟨δ, hδ, hu⟩
    · exact Or.inl fun _ _ => hh
    · rcases MC.lam_lt_dec J.e β with hlt | hlt
      · by_cases hsupp : ∀ i, J.e i = 0 → β i = 0
        · refine Or.inr ⟨f, hf, δ + β, ?_, ?_⟩
          · intro h0
            rw [← Chart.D_mem_max_iff, Chart.D_add] at h0
            exact (mem_maximalIdeal _).1 h0 hu
          · have hlδ : lam J.e δ = 0 := Finset.sum_eq_zero fun i _ => by
              rcases eq_or_ne (J.e i) 0 with h0 | h0
              · rw [h0, mul_zero]
              · rw [hδ i h0, Nat.cast_zero, zero_mul]
            rw [lam_add, hlδ, zero_add]; exact hlt
        · exact Or.inl fun h => absurd h hsupp
      · exact Or.inl fun _ h => absurd h hlt
  have hgen : ∀ f ∈ l, f ∈ J.c.RF J.e 1 ∨ E := by
    intro f hf
    rcases finset_forall_or_exists box (fun β _ => hone f hf β) with hall | he
    · left
      rw [J.c.mem_RF_iff_P J.nonneg]
      intro β hβ hlt
      exact hall β (hbox β hβ hlt) hβ hlt
    · exact Or.inr he
  rcases list_forall_or_exists l hgen with hall | he
  · left
    rw [Adm, MC.RF, hl, lspan, Ideal.span_le]
    exact fun f hf => hall f hf
  · exact Or.inr he

end MC

end BezoutCounterexample.Principalization
