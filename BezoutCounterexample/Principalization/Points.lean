import BezoutCounterexample.Constructive.Nullstellensatz
import BezoutCounterexample.Constructive.Presented

/-!
# Explicit points (D3.0; Task C plan C0, `docs/d3-design.md`)

The engine quantifies over Mathlib's maximal ideals, which have no decidable membership; its
conclusions "for every maximal ideal" are replaced by "for every explicit point".

* `Pt A`: an explicit point, a `ℚ`-algebra map `z : A → L` to a finite extension `L/ℚ` with a zero
  test (the output of `HasPres.exists_point`, as in `ExplicitNS`).
* `Pt.ker`, with `Pt.ker_isMaximal` (instance): the image of `A` is a finite-dimensional
  `ℚ`-domain. Membership in `p.ker` is decided (`Pt.mem_ker_dec`), and so is the residue field of
  the local ring at `p.ker` (`Pt.dec_local`: `x ∈ 𝔪 ∨ IsUnit x`), the `hdec` of `OrdPos`/`StepPos`.
* `HasPres.exists_pt`: a point of `V(l)` when `1 ∉ (l)`; `HasPres.exists_pt_away`: a point of
  `V(l) ∩ D(d)` when no power of `d` lies in `(l)` (through `A[1/d]`, `HasPres.away`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open BezoutCounterexample.Constructive IsLocalRing

/-- **An explicit point** of a `ℚ`-algebra. -/
structure Pt (A : Type) [CommRing A] [Algebra ℚ A] where
  L : Type
  [fld : Field L]
  [alg : Algebra ℚ L]
  [fd : FiniteDimensional ℚ L]
  z : A →ₐ[ℚ] L
  dec : ∀ x : L, x = 0 ∨ x ≠ 0

attribute [instance] Pt.fld Pt.alg Pt.fd

namespace Pt

variable {A : Type} [CommRing A] [Algebra ℚ A] (p : Pt A)

/-- The maximal ideal of the point. -/
def ker : Ideal A := RingHom.ker p.z

lemma mem_ker {x : A} : x ∈ p.ker ↔ p.z x = 0 := RingHom.mem_ker

lemma mem_ker_dec (x : A) : x ∈ p.ker ∨ x ∉ p.ker :=
  (p.dec (p.z x)).elim (fun h => Or.inl (p.mem_ker.2 h)) fun h => Or.inr fun h' => h (p.mem_ker.1 h')

/-- The kernel of a point is maximal: its image is a finite-dimensional `ℚ`-domain. -/
instance ker_isMaximal : p.ker.IsMaximal := by
  let _ : Algebra A p.L := p.z.toRingHom.toAlgebra
  have : IsScalarTower ℚ A p.L := IsScalarTower.of_algebraMap_eq fun r => (p.z.commutes r).symm
  have : Algebra.IsIntegral ℚ p.L := Algebra.IsIntegral.of_finite ℚ p.L
  have : Algebra.IsIntegral A p.L := Algebra.IsIntegral.tower_top ℚ
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A p.L)
    (Algebra.isIntegral_def.1 inferInstance) (⊥ : Ideal p.L)
  have hk : (⊥ : Ideal p.L).comap (algebraMap A p.L) = p.ker := by
    ext x; simp [ker, RingHom.mem_ker]; rfl
  rwa [hk] at h

/-- **The residue field at a point is decided**: in `A_{p.ker}`, `x ∈ 𝔪 ∨ IsUnit x`. -/
lemma dec_local (x : Localization.AtPrime p.ker) :
    x ∈ maximalIdeal (Localization.AtPrime p.ker) ∨ IsUnit x := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.ker.primeCompl x
  rcases p.mem_ker_dec a with h | h
  · exact Or.inl ((IsLocalization.AtPrime.mk'_mem_maximal_iff _ p.ker a s).2 h)
  · exact Or.inr ((IsLocalRing.notMem_maximalIdeal).1 fun h' =>
      h ((IsLocalization.AtPrime.mk'_mem_maximal_iff _ p.ker a s).1 h'))

end Pt

variable {A : Type} [CommRing A] [Algebra ℚ A]

/-- **A point of `V(l)`** (explicit Nullstellensatz). -/
theorem HasPres.exists_pt (hp : HasPres A) (l : List A) (h1 : (1 : A) ∉ lspan l) :
    ∃ p : Pt A, lspan l ≤ p.ker := by
  obtain ⟨L, iF, iA, iFD, z, hz, hzl, -⟩ := hp.exists_point l h1
  refine ⟨⟨L, z.toRatAlgHom, hz⟩, ?_⟩
  rw [lspan, Ideal.span_le]
  intro x hx
  exact hzl x hx

/-- **A point of `V(l) ∩ D(d)`**, when no power of `d` lies in `(l)`. -/
theorem HasPres.exists_pt_away (hp : HasPres A) (l : List A) (d : A)
    (h : ∀ k : ℕ, d ^ k ∉ lspan l) : ∃ p : Pt A, lspan l ≤ p.ker ∧ d ∉ p.ker := by
  let B := Localization.Away d
  have hB : HasPres B := hp.away d B
  have h1 : (1 : B) ∉ lspan (l.map (algebraMap A B)) := by
    intro h1
    rw [lspan_map, IsLocalization.mem_map_algebraMap_iff (Submonoid.powers d) B] at h1
    obtain ⟨⟨⟨a, ha⟩, ⟨_, k, rfl⟩⟩, he⟩ := h1
    rw [one_mul] at he
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers d) B).1 he
    have hdk : d ^ (j + k) = d ^ j * a := by rw [pow_add]; exact hj
    exact h (j + k) (by rw [hdk]; exact Ideal.mul_mem_left _ _ ha)
  obtain ⟨q, hq⟩ := HasPres.exists_pt hB _ h1
  refine ⟨⟨q.L, q.z.comp (IsScalarTower.toAlgHom ℚ A B), q.dec⟩, fun x hx => ?_, fun hd => ?_⟩
  · rw [lspan] at hx
    refine Submodule.span_induction (p := fun x _ => x ∈ Pt.ker _) ?_ (Ideal.zero_mem _)
      (fun _ _ _ _ => Ideal.add_mem _) (fun r _ _ h => Ideal.mul_mem_left _ r h) hx
    intro y hy
    show q.z (algebraMap A B y) = 0
    exact q.mem_ker.1 (hq (Ideal.subset_span (List.mem_map_of_mem hy)))
  · have hu : IsUnit (q.z (algebraMap A B d)) :=
      (IsLocalization.Away.algebraMap_isUnit d).map q.z
    exact hu.ne_zero hd

end BezoutCounterexample.Principalization
