import BezoutCounterexample.Principalization.TorsorInv
import BezoutCounterexample.Principalization.RunPos

/-!
# Smooth invariance with decided runs (D3.8 E4, leaf)

`IsInv.transfer` (Invariant) takes a run from `IsInv.exists_run` and bounds the target's centres by
`IsRun.transfer_bound`, both classical (`MC.exists_run`, `TI.step`). With the residue fields decided
on both sides (`hdecS`, `hdecS'`, from `Pt.dec_local` at explicit points), `PolyIndNoeth` on the source
and generators of the ideal, the decided versions (`IsInv.exists_run_pos`, `IsRun.transfer_bound_pos`)
give the same statement:

* `IsInv.transfer_pos`, `IsInv.transfer_mvLoc_pos`, `IsInv.transfer_polyLoc_pos`;
* `invAt_torsor_of_rees_pt`, `invAt_rees_of_base_pt`: twins of `invAt_torsor_of_rees` and
  `invAt_rees_of_base` (used by `torsor_invAt_pt`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization Constructive

/-- **The residue field at a point is decided**, at any ideal equal to its kernel. -/
lemma Pt.dec_local_of_eq {A : Type} [CommRing A] [Algebra ℚ A] (p : Pt A) {𝔪 : Ideal A}
    [𝔪.IsPrime] (h : p.ker = 𝔪) :
    ∀ x : Localization.AtPrime 𝔪, x ∈ maximalIdeal (Localization.AtPrime 𝔪) ∨ IsUnit x := by
  subst h; exact p.dec_local

/-- Generators of `I` at `A_𝔪`. -/
lemma Iloc_lspan {A : Type} [CommRing A] (I 𝔪 : Ideal A) [𝔪.IsPrime] (l : List A)
    (hl : I = lspan l) : Iloc I 𝔪 = lspan (l.map (algebraMap A (Localization.AtPrime 𝔪))) := by
  rw [Iloc, hl, lspan, lspan, Ideal.map_span]
  congr 1
  ext y
  simp

section SI

variable {S S' : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [Fact (PolyIndNoeth S)]
  [CommRing S'] [Algebra ℚ S'] [IsLocalRing S']
  [Algebra.FormallySmooth ℚ S'] [Algebra.FormallySmooth ℚ (ResidueField S')]
  [Algebra.IsIntegral ℚ (ResidueField S')] {n n' : ℕ}

/-- **Smooth invariance** with decided runs (`IsInv.transfer` with `exists_run_pos` and
`transfer_bound_pos`): the invariant of `I S'` is the padded invariant of `I`. -/
theorem IsInv.transfer_pos (hdecS : ∀ x : S, x ∈ maximalIdeal S ∨ IsUnit x)
    (hdecS' : ∀ x : S', x ∈ maximalIdeal S' ∨ IsUnit x) {hnn : n ≤ n'} {ψ : S →+* S'}
    (hψ : ∀ a ∈ maximalIdeal S, ψ a ∈ maximalIdeal S')
    {c : Chart S n} (hc : c.IsCentred) {c' : Chart S' n'} (hcc : Compat hnn ψ c c')
    {I : Ideal S} (l : List S) (hl : I = lspan l) (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal S) {e : Fin n → ℚ} (he : IsInv I n e)
    (hfg : (maximalIdeal S').FG) :
    IsInv (I.map ψ) n' (pad n' e) := by
  obtain ⟨k, ck, hrun, hadm, hck, hsupp⟩ := he.exists_run_pos hdecS l hl hI hIm c hc
  obtain ⟨ck', hck', hbound⟩ := hrun.transfer_bound_pos hdecS' hcc
  refine ⟨?_, fun J' hJ' => (hbound J' hJ').1⟩
  obtain ⟨c'', hc'', hx⟩ := Chart.exists_centred hfg ck'
  have hRF : ∀ t, c''.RF (pad n' e) t = ck'.RF (pad n' e) t := by
    intro t
    refine Chart.RF_congr (fun i hi => ?_) t
    have hin : (i : ℕ) < n := by
      by_contra h
      exact hi (by simp only [pad]; rw [dite_eq_right h])
    have hi' : i = Fin.castLE hnn ⟨i, hin⟩ := Fin.ext rfl
    apply hx
    rw [hi', hck'.x]
    exact hψ _ (hck.x_mem _)
  refine ⟨⟨c'', pad n' e, hc'', pad_nonneg_gen he.nonneg, pad_antitone_gen he.nonneg he.anti⟩,
    ?_, rfl⟩
  show I.map ψ ≤ c''.RF (pad n' e) 1
  rw [hRF]
  exact (Ideal.map_mono hadm).trans (hck'.map_RF_le e 1)

end SI

section SILoc

variable {S S' : Type*} [CommRing S] [Algebra ℚ S] [IsLocalRing S] [Fact (PolyIndNoeth S)]
  [CommRing S'] [Algebra ℚ S'] [IsLocalRing S'] [IsNoetherianRing S']
  [Algebra.FormallySmooth ℚ S'] [Algebra.FormallySmooth ℚ (ResidueField S')]
  [Algebra.IsIntegral ℚ (ResidueField S')] {n : ℕ}

/-- **Smooth invariance** (decided runs) for a target which is a localization of `S[X₁, …, X_r]`. -/
theorem IsInv.transfer_mvLoc_pos (hdecS : ∀ x : S, x ∈ maximalIdeal S ∨ IsUnit x)
    (hdecS' : ∀ x : S', x ∈ maximalIdeal S' ∨ IsUnit x) {r : ℕ} (θ : MvPolynomial (Fin r) S →+* S')
    (hinj : Function.Injective θ) (hsurj : ∀ z : S', ∃ a b, IsUnit (θ b) ∧ z * θ b = θ a)
    (hloc : ∀ a ∈ maximalIdeal S, θ (MvPolynomial.C a) ∈ maximalIdeal S')
    {c : Chart S n} (hc : c.IsCentred) {I : Ideal S} (l : List S) (hl : I = lspan l)
    (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal S)
    {e : Fin n → ℚ} (he : IsInv I n e) :
    IsInv (I.map (θ.comp MvPolynomial.C)) (n + r) (pad (n + r) e) := by
  let := θ.toAlgebra
  have : IsScalarTower ℚ (MvPolynomial (Fin r) S) S' :=
    IsScalarTower.of_algebraMap_eq (fun q => (RingHom.map_rat_algebraMap θ q).symm)
  have := isLocalization_unitPre θ hinj hsurj
  have hcc := (c.compat_mvPolynomial r).trans
    ((c.mvPolynomial r).compat_localization (L := S') (unitPre θ))
  exact IsInv.transfer_pos hdecS hdecS' (fun a ha => hloc a ha) hc hcc l hl hI hIm he (IsNoetherian.noetherian _)

/-- **Smooth invariance** (decided runs) for a target which is a localization of `S[X]`. -/
theorem IsInv.transfer_polyLoc_pos (hdecS : ∀ x : S, x ∈ maximalIdeal S ∨ IsUnit x)
    (hdecS' : ∀ x : S', x ∈ maximalIdeal S' ∨ IsUnit x) (θ : Polynomial S →+* S')
    (hinj : Function.Injective θ) (hsurj : ∀ z : S', ∃ a b, IsUnit (θ b) ∧ z * θ b = θ a)
    (hloc : ∀ a ∈ maximalIdeal S, θ (Polynomial.C a) ∈ maximalIdeal S')
    {c : Chart S n} (hc : c.IsCentred) {I : Ideal S} (l : List S) (hl : I = lspan l)
    (hI : I ≠ ⊥) (hIm : I ≤ maximalIdeal S)
    {e : Fin n → ℚ} (he : IsInv I n e) :
    IsInv (I.map (θ.comp Polynomial.C)) (n + 1) (pad (n + 1) e) := by
  let := θ.toAlgebra
  have : IsScalarTower ℚ (Polynomial S) S' :=
    IsScalarTower.of_algebraMap_eq (fun q => (RingHom.map_rat_algebraMap θ q).symm)
  have := isLocalization_unitPre θ hinj hsurj
  have hcc := c.compat_polynomial.trans (c.polynomial.compat_localization (L := S') (unitPre θ))
  exact IsInv.transfer_pos hdecS hdecS' (fun a ha => hloc a ha) hc hcc l hl hI hIm he (IsNoetherian.noetherian _)

end SILoc

section T2

variable {R : Type} [CommRing R] [IsDomain R] [Algebra ℚ R] [Algebra.Smooth ℚ R] [IsNoetherianRing R]
  {r : ℕ}
  (y : Fin (r + 1) → R) [IsDomain (Jou.J y)] [IsNoetherianRing (Jou.J y)]
  [Algebra.FormallySmooth ℚ (Jou.J y)] [Algebra.FiniteType ℚ (Jou.J y)]
  (Q : Ideal (Jou.J y)) [Q.IsMaximal] {l : Fin (r + 1)}
  (hyl : y l ∉ Q.comap (algebraMap R (Jou.J y)))
include hyl

omit [Algebra.Smooth ℚ R] in
/-- **Smooth invariance along the torsor** `R_P → U_Q`, with decided runs (twin of
`invAt_torsor_of_rees`). -/
theorem invAt_torsor_of_rees_pt
    [Fact (PolyIndNoeth (Localization.AtPrime (Q.comap (algebraMap R (Jou.J y)))))]
    (hdecS : ∀ x : Localization.AtPrime (Q.comap (algebraMap R (Jou.J y))),
      x ∈ maximalIdeal (Localization.AtPrime (Q.comap (algebraMap R (Jou.J y)))) ∨ IsUnit x)
    (hdecS' : ∀ x : Localization.AtPrime Q, x ∈ maximalIdeal (Localization.AtPrime Q) ∨ IsUnit x)
    {J : Ideal R} (lJ : List R) (hlJ : J = lspan lJ) (hJ : J ≠ ⊥) (hJP : J ≤ Q.comap (algebraMap R (Jou.J y)))
    {w : ℕ → ℚ} (hw : InvAt J (Q.comap (algebraMap R (Jou.J y))) w) :
    InvAt (J.map (algebraMap R (Jou.J y))) Q w := by
  obtain ⟨n, e, he, rfl⟩ := hw
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime (Q.comap (algebraMap R (Jou.J y)))) :=
    IsLocalization.isNoetherianRing (Q.comap (algebraMap R (Jou.J y))).primeCompl _ inferInstance
  have := residueField_isIntegral Q
  obtain ⟨M, -, -⟩ := he.1
  have : Algebra.FormallySmooth ℚ (ResidueField (Localization.AtPrime Q)) :=
    (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.1 (fe_residueField Q)).2
  have h := IsInv.transfer_mvLoc_pos (S := Localization.AtPrime (Q.comap (algebraMap R (Jou.J y))))
    (S' := Localization.AtPrime Q) hdecS hdecS' (theta2 y Q hyl) (theta2_injective y Q hyl)
    (theta2_surj y Q hyl) (theta2_local y Q hyl) M.centred _ (Iloc_lspan J _ lJ hlJ)
    (Iloc_ne_bot hJ _) (Iloc_le hJP) he
  refine ⟨n + r, pad (n + r) e, ?_, ext0_pad (Nat.le_add_right n r) e⟩
  have hmap : (Iloc J (Q.comap (algebraMap R (Jou.J y)))).map ((theta2 y Q hyl).comp MvPolynomial.C) =
      Iloc (J.map (algebraMap R (Jou.J y))) Q := by
    rw [Iloc, Iloc, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, theta2_comp]
  rw [← hmap]; exact h

end T2

section T1

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ B] [Algebra.Smooth ℚ B] [IsNoetherianRing B]
  (Φ : WFil B)
  (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)
  [IsNoetherianRing (ReesAlg Φ)] [Algebra.FormallySmooth ℚ (ReesAlg Φ)]
  [Algebra.FiniteType ℚ (ReesAlg Φ)]
  (P : Ideal (ReesAlg Φ)) [P.IsMaximal] (hsP : reesS Φ hneg ∉ P)
include hneg hsP

omit [Algebra.Smooth ℚ B] in
/-- **Smooth invariance off the exceptional divisor** `B_𝔪 → R_P`, with decided runs (twin of
`invAt_rees_of_base`). -/
theorem invAt_rees_of_base_pt
    [Fact (PolyIndNoeth (Localization.AtPrime (P.comap (algebraMap B (ReesAlg Φ)))))]
    (hdecS : ∀ x : Localization.AtPrime (P.comap (algebraMap B (ReesAlg Φ))),
      x ∈ maximalIdeal (Localization.AtPrime (P.comap (algebraMap B (ReesAlg Φ)))) ∨ IsUnit x)
    (hdecS' : ∀ x : Localization.AtPrime P, x ∈ maximalIdeal (Localization.AtPrime P) ∨ IsUnit x)
    {J : Ideal B} (lJ : List B) (hlJ : J = lspan lJ) (hJ : J ≠ ⊥)
    (hJP : J ≤ P.comap (algebraMap B (ReesAlg Φ)))
    {u : ℕ → ℚ} (hu : InvAt J (P.comap (algebraMap B (ReesAlg Φ))) u) :
    InvAt (J.map (algebraMap B (ReesAlg Φ))) P u := by
  obtain ⟨n, e, he, rfl⟩ := hu
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have : IsNoetherianRing (Localization.AtPrime (P.comap (algebraMap B (ReesAlg Φ)))) :=
    IsLocalization.isNoetherianRing (P.comap (algebraMap B (ReesAlg Φ))).primeCompl _ inferInstance
  have := residueField_isIntegral P
  obtain ⟨M, -, -⟩ := he.1
  have : Algebra.FormallySmooth ℚ (ResidueField (Localization.AtPrime P)) :=
    (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.1 (fe_residueField P)).2
  set 𝔮 := P.comap (algebraMap B (ReesAlg Φ))
  have h := IsInv.transfer_polyLoc_pos (S := Localization.AtPrime 𝔮) (S' := Localization.AtPrime P)
    (hdecS := hdecS) (hdecS' := hdecS')
    (theta1 Φ hneg P hsP 𝔮 rfl) (theta1_injective Φ hneg P hsP 𝔮 rfl)
    (theta1_surj Φ hneg P hsP 𝔮 rfl) (theta1_local Φ hneg P hsP 𝔮 rfl) M.centred _ (Iloc_lspan J _ lJ hlJ)
    (Iloc_ne_bot hJ _) (Iloc_le hJP) he
  refine ⟨n + 1, pad (n + 1) e, ?_, ext0_pad (Nat.le_succ n) e⟩
  have hcomp : (theta1 Φ hneg P hsP 𝔮 rfl).comp Polynomial.C = Localization.localRingHom 𝔮 P
      (algebraMap B (ReesAlg Φ)) rfl := RingHom.ext fun a => theta1_C Φ hneg P hsP 𝔮 rfl a
  have hmap : (Iloc J 𝔮).map ((theta1 Φ hneg P hsP 𝔮 rfl).comp Polynomial.C) =
      Iloc (J.map (algebraMap B (ReesAlg Φ))) P := by
    have hc2 : (Localization.localRingHom 𝔮 P (algebraMap B (ReesAlg Φ)) rfl).comp
        (algebraMap B (Localization.AtPrime 𝔮)) =
        (algebraMap (ReesAlg Φ) (Localization.AtPrime P)).comp (algebraMap B (ReesAlg Φ)) :=
      RingHom.ext fun x => Localization.localRingHom_to_map _ _ _ rfl x
    rw [Iloc, Iloc, Ideal.map_map, Ideal.map_map, hcomp, hc2]
  rw [← hmap]; exact h

end T1

end BezoutCounterexample.Principalization
