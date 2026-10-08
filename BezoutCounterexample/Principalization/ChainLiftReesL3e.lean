import Mathlib
import BezoutCounterexample.Principalization.ChainLiftReesL3d
import BezoutCounterexample.Principalization.MaxLocus
import BezoutCounterexample.Principalization.LocDataPt

/-!
# L3-e2: the centred case at a point from the local data of a chart (Task B, S5c)

* `Pt.ζloc`, `Pt.ζloc_spec`: the explicit point of `A_q` (`ζ x = 0 ↔ x ∈ 𝔪`).
* `hcent_of_locDataPt`: at a point `q` of `D(g)` where all heads vanish, the kernel statement for the
  heads `γ x̃ᵢ = γ Dqᵢ aᵢ` of the model, from the chart of a `LocData` transported to `A_q`, its
  numerators `cB.xᵢ gˢ = aᵢ` (`exists_numerators`) and `l3_ker_centred`. All inverses are explicit.
  Only the data of the chart are used, so it takes coll-7c's `LocDataPt` (D3.4);
  `hcent_of_locData` is the instance at `LocData.toPt`.
  The I4 instances on `A_q` are instance binders (filled from `Algebra.Smooth ℚ A` today).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open MvPolynomial BezoutCounterexample.Constructive IsLocalRing

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A]

/-- The explicit point of the local ring at a point. -/
def Pt.ζloc (q : Pt A) : Localization.AtPrime q.ker →ₐ[ℚ] q.L :=
  (IsLocalization.lift (M := q.ker.primeCompl) (S := Localization.AtPrime q.ker)
    (g := (q.z : A →+* q.L)) fun s => isUnit_iff_ne_zero.2 fun h => s.2 (q.mem_ker.2 h)).toRatAlgHom

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma Pt.ζloc_spec (q : Pt A) (x : Localization.AtPrime q.ker) :
    q.ζloc x = 0 ↔ x ∈ maximalIdeal (Localization.AtPrime q.ker) := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.ker.primeCompl x
  rw [IsLocalization.AtPrime.mk'_mem_maximal_iff _ q.ker a s]
  show IsLocalization.lift _ (IsLocalization.mk' _ a s) = 0 ↔ _
  rw [IsLocalization.lift_mk'_spec, mul_zero]
  exact q.mem_ker.symm

variable {m kc l r : ℕ}
  (G : List (MvPolynomial (Fin (m + (kc + l))) ℤ)) (e : SmoothCert.QB G ≃+* A)
  (F : Fin (m + (kc + l)) → MvPolynomial (Fin (m + (kc + l))) ℤ)
  (γ : MvPolynomial (Fin (m + (kc + l))) ℤ) (w : Fin kc → ℕ)

omit [IsDomain A] [Algebra.Smooth ℚ A] in
lemma toAZ_mul (p p' : MvPolynomial (Fin (m + (kc + l))) ℤ) :
    toAZ G e (p * p') = toAZ G e p * toAZ G e p' := by
  simp [toAZ]

/-- **L3-e2b: the centred case at a point**, from a `LocDataPt`. -/
theorem hcent_of_locDataPt {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal]
    (D : LocDataPt I v₀ 𝔪) (hkn : kc ≤ D.n) (hk : D.k = kc) (s : ℕ) (a : Fin D.n → A)
    (ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s = algebraMap A D.B (a i))
    (Dq : Fin kc → ℕ) (hDq : ∀ i, 0 < Dq i)
    (hhead : ∀ i, toAZ G e (F (Fin.natAdd m (Fin.castAdd l i))) = (Dq i : A) * a (ιk hkn i))
    {d : ℕ} (hd : 0 < d) (wf : Fin D.n → ℕ) (hwf : ∀ i, (wf i : ℚ) = d * D.ek i)
    (hwk : ∀ i, w i = wf (ιk hkn i))
    (q : Pt A) (hg : D.g ∉ q.ker) (hγ : toAZ G e γ ∉ q.ker)
    [Fact (PolyIndNoeth (Localization.AtPrime q.ker))]
    [Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker)]
    [Algebra.FormallySmooth ℚ (ResidueField (Localization.AtPrime q.ker))]
    (hall : ∀ i, toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i))) ∈ q.ker)
    (p : MvPolynomial (Option (Fin kc)) (Localization.AtPrime q.ker))
    (hp : aeval (lGen (xq G e F γ q) w) p = 0) :
    p ∈ Ideal.span (Set.range (lRel (xq G e F γ q) w)) := by
  set c := Loc.transport (D.ctrlN q.ker hg) D.cB
  have hcx : ∀ i, c.x i * algebraMap A _ D.g ^ s = algebraMap A _ (a i) := by
    intro i
    have := congrArg (Loc.map (D.ctrlN q.ker hg)) (ha i)
    rw [map_mul, map_pow, Loc.map_algebraMap, Loc.map_algebraMap] at this
    simpa [c, Loc.transport_x] using this
  have hsupp : ∀ i, D.ek i ≠ 0 ↔ (i : ℕ) < kc := by rw [← hk]; exact D.supp
  have hDqA : ∀ i, (Dq i : A) ∉ q.ker := fun i h => by
    rw [q.mem_ker, map_natCast] at h
    have h2 : algebraMap ℚ q.L (Dq i : ℚ) = algebraMap ℚ q.L 0 := by rw [map_natCast, h, map_zero]
    exact (Nat.cast_ne_zero.2 (hDq i).ne') ((algebraMap ℚ q.L).injective h2)
  let hgs : q.ker.primeCompl := ⟨toAZ G e γ * D.g ^ s, fun h =>
    ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hγ fun h' => hg (Ideal.IsPrime.mem_of_pow_mem
      inferInstance _ h'))⟩
  have hmax : ∀ i : Fin kc, c.x (ιk hkn i) ∈ maximalIdeal (Localization.AtPrime q.ker) := by
    intro i
    have ha' : a (ιk hkn i) ∈ q.ker := by
      have h1 := hall i
      rw [toAZ_mul, hhead] at h1
      rcases Ideal.IsPrime.mem_or_mem inferInstance h1 with h | h
      · exact absurd h hγ
      · exact (Ideal.IsPrime.mem_or_mem inferInstance h).resolve_left (hDqA i)
    have h2 : algebraMap A (Localization.AtPrime q.ker) (a (ιk hkn i)) ∈
        maximalIdeal (Localization.AtPrime q.ker) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q.ker _).2 ha'
    rw [← hcx] at h2
    have hu : IsUnit (algebraMap A (Localization.AtPrime q.ker) D.g ^ s) :=
      (IsLocalization.map_units (Localization.AtPrime q.ker) (⟨D.g, hg⟩ : q.ker.primeCompl)).pow s
    exact (Ideal.mul_unit_mem_iff_mem _ hu).1 h2
  -- the unit factors and their explicit inverses
  set v : Fin kc → Localization.AtPrime q.ker := fun i =>
    algebraMap A _ (toAZ G e γ * D.g ^ s) * algebraMap ℚ _ (Dq i : ℚ)
  set vi : Fin kc → Localization.AtPrime q.ker := fun i =>
    IsLocalization.mk' _ (1 : A) hgs * algebraMap ℚ _ ((Dq i : ℚ)⁻¹)
  have hvi : ∀ i, vi i * v i = 1 := by
    intro i
    have hD : ((Dq i : ℚ)⁻¹) * (Dq i : ℚ) = 1 := inv_mul_cancel₀ (Nat.cast_ne_zero.2 (hDq i).ne')
    have hspec : IsLocalization.mk' (Localization.AtPrime q.ker) (1 : A) hgs *
        algebraMap A _ (toAZ G e γ * D.g ^ s) = 1 := by
      rw [show toAZ G e γ * D.g ^ s = (hgs : A) from rfl, IsLocalization.mk'_spec, map_one]
    calc vi i * v i = (IsLocalization.mk' _ (1 : A) hgs * algebraMap A _ (toAZ G e γ * D.g ^ s)) *
          algebraMap ℚ (Localization.AtPrime q.ker) (((Dq i : ℚ)⁻¹) * (Dq i : ℚ)) := by
            simp only [vi, v, map_mul]; ring
      _ = 1 := by rw [hspec, hD, map_one, one_mul]
  have hx : ∀ i, xq G e F γ q i = v i * c.x (ιk hkn i) := by
    intro i
    have hDA : algebraMap A (Localization.AtPrime q.ker) (Dq i : A) =
        algebraMap ℚ (Localization.AtPrime q.ker) (Dq i : ℚ) := by simp
    rw [xq, toAZ_mul, hhead, map_mul, map_mul, hDA, ← hcx]
    simp only [v, map_mul, map_pow]
    ring
  exact l3_ker_centred q.dec q.ζloc q.ζloc_spec c hkn D.inv.nonneg hsupp hd hwf hmax w hwk
    (xq G e F γ q) v vi hvi hx p hp

variable [IsNoetherianRing A] in
/-- **L3-e2b** from a `LocData` (through `LocData.toPt`). -/
theorem hcent_of_locData {I : Ideal A} {v₀ : ℕ → ℚ} {𝔪 : Ideal A} [𝔪.IsMaximal]
    (D : LocData I v₀ 𝔪) (hkn : kc ≤ D.n) (hk : D.k = kc) (s : ℕ) (a : Fin D.n → A)
    (ha : ∀ i, D.cB.x i * algebraMap A D.B D.g ^ s = algebraMap A D.B (a i))
    (Dq : Fin kc → ℕ) (hDq : ∀ i, 0 < Dq i)
    (hhead : ∀ i, toAZ G e (F (Fin.natAdd m (Fin.castAdd l i))) = (Dq i : A) * a (ιk hkn i))
    {d : ℕ} (hd : 0 < d) (wf : Fin D.n → ℕ) (hwf : ∀ i, (wf i : ℚ) = d * D.ek i)
    (hwk : ∀ i, w i = wf (ιk hkn i))
    (q : Pt A) (hg : D.g ∉ q.ker) (hγ : toAZ G e γ ∉ q.ker)
    [Fact (PolyIndNoeth (Localization.AtPrime q.ker))]
    [Algebra.FormallySmooth ℚ (Localization.AtPrime q.ker)]
    [Algebra.FormallySmooth ℚ (ResidueField (Localization.AtPrime q.ker))]
    (hall : ∀ i, toAZ G e (γ * F (Fin.natAdd m (Fin.castAdd l i))) ∈ q.ker)
    (p : MvPolynomial (Option (Fin kc)) (Localization.AtPrime q.ker))
    (hp : aeval (lGen (xq G e F γ q) w) p = 0) :
    p ∈ Ideal.span (Set.range (lRel (xq G e F γ q) w)) :=
  hcent_of_locDataPt G e F γ w D.toPt hkn hk s a ha Dq hDq hhead hd wf hwf hwk q hg hγ hall p hp

end BezoutCounterexample.Principalization
