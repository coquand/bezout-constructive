import BezoutCounterexample.Principalization.ReesVertex
import BezoutCounterexample.Principalization.LocalPt
import BezoutCounterexample.Constructive.CompList

/-!
# Explicit points for the drop (leaf; drop_pt steps 1, 3, 7, 8 of `docs/plan-drop-pt.md`)

* `Pt.pullback`: an explicit point pulled back along a ring map (same field, same zero test);
  `Pt.pullback_ker`;
* `Pt.vertexPt`: the vertex over an explicit point `q` of `A`, as an explicit point of the Rees
  algebra: `p ↦ q(p₀)` through `vtx` and the residue field of `A_q` (`Pt.zAt`);
  `Pt.vertexPt_ker : ker = vertexG` (no Zariski: the point is explicit);
* `exists_reesScale_not_mem_pt`: `exists_reesScale_not_mem` at an explicit point `Q` of the Rees
  algebra: `Q(σ_μ G)` is a polynomial in `μ` over the field of `Q`, with constant term
  `Q(G₀) ≠ 0`, so one of `μ = 1, …, N+1` (`N` its degree) is not a root, found by the zero test
  of `Q` (no `Infinite.exists_notMem_finset`).
-/

noncomputable section

namespace BezoutCounterexample.Principalization

open IsLocalRing IsLocalization LaurentPolynomial Constructive

namespace Pt

variable {A R : Type} [CommRing A] [Algebra ℚ A] [CommRing R] [Algebra ℚ R]

/-- The pull-back of an explicit point along a ring map. -/
def pullback (Q : Pt R) (φ : A →+* R) : Pt A :=
  ⟨Q.L, Q.z.comp φ.toRatAlgHom, Q.dec⟩

lemma pullback_ker (Q : Pt R) (φ : A →+* R) : (Q.pullback φ).ker = Q.ker.comap φ := by
  ext x
  simp only [Ideal.mem_comap, Pt.mem_ker]
  rfl

end Pt

section VertexPt

variable {A : Type} [CommRing A] [IsDomain A] [Algebra ℚ A] (Φ : WFil A) (q : Pt A)
  (hpos : ∀ j : ℤ, 0 < j → (Φ.loc (Localization.AtPrime q.ker)).F j ≤
    maximalIdeal (Localization.AtPrime q.ker))

/-- The residue field of `A_q` into the field of the point. -/
def Pt.resL : ResidueField (Localization.AtPrime q.ker) →+* q.L :=
  Ideal.Quotient.lift _ (q.zAt : Localization.AtPrime q.ker →+* q.L) fun a ha =>
    (q.zAt_spec a).2 ha

/-- **The vertex over `q`, as an explicit point of the Rees algebra.** -/
def Pt.vertexPt : Pt (ReesAlg Φ) :=
  ⟨q.L, ((q.resL).comp ((vtx hpos).comp (reesMap Φ (Localization.AtPrime q.ker)))).toRatAlgHom,
    q.dec⟩

lemma Pt.vertexPt_ker : (q.vertexPt Φ hpos).ker = vertexG Φ q.ker hpos := by
  ext x
  rw [Pt.mem_ker, vertexG, Ideal.mem_comap, vertex, RingHom.mem_ker]
  show q.resL (vtx hpos (reesMap Φ _ x)) = 0 ↔ _
  exact map_eq_zero_iff _ (q.resL).injective

end VertexPt

section ScalePt

variable {B : Type} [CommRing B] [Algebra ℚ B] (Φ : WFil B) (hneg : ∀ j : ℤ, j ≤ 0 → Φ.F j = ⊤)

/-- **A rescaling moving `G` off an explicit point** (`exists_reesScale_not_mem` at a point). -/
theorem exists_reesScale_not_mem_pt (Q : Pt (ReesAlg Φ)) (hs : reesS Φ hneg ∈ Q.ker)
    (G : ReesAlg Φ) (hG : hcomp Φ G 0 ∉ Q.ker) :
    ∃ (μ : ℚ) (hμ : μ ≠ 0), reesScale Φ (qUnit μ hμ) G ∉ Q.ker := by
  set π : ReesAlg Φ →+* Q.L := (Q.z : ReesAlg Φ →+* Q.L)
  set S := (G : B[T;T⁻¹]).coeff.support
  set Qp : Polynomial Q.L := ∑ j ∈ S.filter (fun j => 0 ≤ j),
    (Polynomial.C (π (hcomp Φ G j)) * (Polynomial.X : Polynomial Q.L) ^ j.toNat)
  have hQ0 : Qp.coeff 0 = π (hcomp Φ G 0) := by
    simp only [Qp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    by_cases h0 : (0 : ℤ) ∈ S
    · rw [Finset.sum_eq_single (0 : ℤ)]
      · simp
      · intro j hj hj0
        rw [ite_eq_right]; rw [Finset.mem_filter] at hj; omega
      · intro h; exact absurd (Finset.mem_filter.2 ⟨h0, le_rfl⟩) h
    · have hG0 : hcomp Φ G 0 = 0 := by
        apply Subtype.ext
        show LaurentPolynomial.C ((G : B[T;T⁻¹]).coeff 0) * T 0 = 0
        rw [Finsupp.notMem_support_iff.1 h0, map_zero, zero_mul]
      rw [hG0, map_zero]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_filter] at hj
      rw [ite_eq_right]; intro h; apply h0; have : j = 0 := by omega
      rw [← this]; exact hj.1
  have hQne : Qp ≠ 0 := by
    intro h
    apply hG
    rw [Pt.mem_ker]
    show π (hcomp Φ G 0) = 0
    rw [← hQ0, h, Polynomial.coeff_zero]
  have hnegQ : ∀ j : ℤ, j < 0 → π (hcomp Φ G j) = 0 := fun j hj =>
    (Pt.mem_ker Q).1 (hcomp_neg_mem Φ hneg Q.ker hs G hj)
  have heval : ∀ (μ : ℚ) (hμ : μ ≠ 0),
      π (reesScale Φ (qUnit μ hμ) G) = Qp.eval (algebraMap ℚ Q.L μ) := by
    intro μ hμ
    conv_lhs => rw [← sum_hcomp Φ G]
    rw [map_sum, map_sum]
    simp only [Qp, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [← Finset.sum_filter_add_sum_filter_not S (fun j => 0 ≤ j)]
    have hneg0 : ∑ j ∈ S.filter (fun j => ¬ 0 ≤ j), π (reesScale Φ (qUnit μ hμ) (hcomp Φ G j)) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_filter] at hj
      rw [reesScale_hcomp, map_mul, hnegQ j (by omega), mul_zero]
    rw [hneg0, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_filter] at hj
    rw [reesScale_hcomp, map_mul, mul_comm]
    congr 1
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hj.2
    subst hm
    rw [zpow_natCast, Units.val_pow_eq_pow_val, qUnit_val, map_pow, map_pow, Int.toNat_natCast]
    exact congrArg (· ^ m) (Q.z.commutes μ)
  -- the search over `μ = 1, …, N + 1`
  set N := Qp.natDegree
  have hdecμ : ∀ i : Fin (N + 1), Qp.eval (algebraMap ℚ Q.L ((i : ℕ) + 1 : ℚ)) ≠ 0 ∨
      ¬ Qp.eval (algebraMap ℚ Q.L ((i : ℕ) + 1 : ℚ)) ≠ 0 := fun i =>
    (Q.dec _).elim (fun h => Or.inr fun h' => h' h) Or.inl
  rcases list_exists_or_forall hdecμ (List.finRange (N + 1)) with ⟨i, -, hi⟩ | hall
  · have hμ0 : ((i : ℕ) + 1 : ℚ) ≠ 0 := by positivity
    refine ⟨_, hμ0, fun hmem => hi ?_⟩
    rw [← heval _ hμ0]
    exact (Pt.mem_ker Q).1 hmem
  · exfalso
    apply hQne
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Qp
      (f := fun i : Fin (N + 1) => algebraMap ℚ Q.L ((i : ℕ) + 1 : ℚ)) ?_ ?_ (by simp [N])
    · intro a b hab
      have := (algebraMap ℚ Q.L).injective hab
      exact Fin.ext (by exact_mod_cast add_right_cancel this)
    · intro i
      exact (Q.dec _).elim id fun h => absurd h (hall i (List.mem_finRange i))

end ScalePt

end BezoutCounterexample.Principalization
