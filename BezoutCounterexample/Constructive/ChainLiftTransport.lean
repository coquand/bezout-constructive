import Mathlib
import BezoutCounterexample.Constructive.ChainLiftCertGlue
import BezoutCounterexample.Constructive.ChainLiftReesModel

/-!
# Transport of certificates along `m = m'`, `n = n'` (Task B, Rees layer S6, assembly)

The charts of the cover have different head counts `kc`, so the layouts `Fin (m + (kc + l))` and
`Fin ((m + r) + ((1 + kc) + l))` are equal to the common ones only propositionally. Everything
(chart data, conormal injectivity, square pieces, power covers) is transported by renaming the
variables along `finCongr`. The statements take `m' n'` as variables, and the proofs are `subst` plus
`rename (finCongr rfl) = id`.
-/

noncomputable section

namespace BezoutCounterexample.Constructive

open MvPolynomial

/-- The renaming along `m + n = m' + n'`. -/
def trR {m n m' n' : ℕ} (hm : m = m') (hn : n = n') : Fin (m + n) ≃ Fin (m' + n') :=
  finCongr (by rw [hm, hn])

lemma rename_trR_rfl {m n : ℕ} (p : MvPolynomial (Fin (m + n)) ℤ) :
    rename (trR (rfl : m = m) (rfl : n = n)) p = p := by
  have : (trR (rfl : m = m) (rfl : n = n) : Fin (m + n) → Fin (m + n)) = id :=
    funext fun i => Fin.ext rfl
  rw [this, rename_id_apply]

lemma map_rename_trR_rfl {m n : ℕ} (G : List (MvPolynomial (Fin (m + n)) ℤ)) :
    G.map (rename (trR (rfl : m = m) (rfl : n = n))) = G := by
  conv_rhs => rw [← List.map_id G]
  exact List.map_congr_left fun p _ => rename_trR_rfl p

/-- **A power cover transported.** -/
theorem powCover_transport {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (G : List (MvPolynomial (Fin (m + n)) ℤ)) (c : MvPolynomial (Fin (m + n)) ℤ)
    (h : ∃ (a K : ℕ) (P : Fin K → SquarePiece m n G) (u : Fin K → MvPolynomial (Fin (m + n)) ℤ)
      (N : ℕ), 0 < N ∧ (N : MvPolynomial (Fin (m + n)) ℤ) * c ^ a - ∑ k, u k * (P k).h ∈ lspan G) :
    ∃ (a K : ℕ) (P : Fin K → SquarePiece m' n' (G.map (rename (trR hm hn))))
      (u : Fin K → MvPolynomial (Fin (m' + n')) ℤ) (N : ℕ), 0 < N ∧
      (N : MvPolynomial (Fin (m' + n')) ℤ) * rename (trR hm hn) c ^ a - ∑ k, u k * (P k).h ∈
        lspan (G.map (rename (trR hm hn))) := by
  subst hm hn
  rw [map_rename_trR_rfl, rename_trR_rfl]
  exact h

/-- **Chart data and conormal injectivity transported.** -/
theorem chartData_transport {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (G : List (MvPolynomial (Fin (m + n)) ℤ)) (T : ChartData G) (d : MvPolynomial (Fin (m + n)) ℤ)
    (hinj : ConormalInj G d) :
    ∃ T' : ChartData (G.map (rename (trR hm hn))), T'.c = rename (trR hm hn) T.c ∧
      ConormalInj (G.map (rename (trR hm hn))) (rename (trR hm hn) d) := by
  subst hm hn
  rw [map_rename_trR_rfl]
  refine ⟨T, (rename_trR_rfl _).symm, ?_⟩
  rw [rename_trR_rfl]
  exact hinj

/-- **A power cover from chart data, in a transported layout.** -/
theorem powCover_of_chartData {m n m' n' : ℕ} (hm : m = m') (hn : n = n') (hpos : 0 < n)
    (G : List (MvPolynomial (Fin (m + n)) ℤ)) (T : ChartData G) (d : MvPolynomial (Fin (m + n)) ℤ)
    (hinj : ConormalInj G d) :
    ∃ (a K : ℕ) (P : Fin K → SquarePiece m' n' (G.map (rename (trR hm hn))))
      (u : Fin K → MvPolynomial (Fin (m' + n')) ℤ) (N : ℕ), 0 < N ∧
      (N : MvPolynomial (Fin (m' + n')) ℤ) * rename (trR hm hn) (T.c * d) ^ a - ∑ k, u k * (P k).h ∈
        lspan (G.map (rename (trR hm hn))) :=
  powCover_transport hm hn G _ (T.exists_pow_cover hpos d hinj)

/-- **A square piece transported**, with its `h` renamed. -/
theorem squarePiece_transport {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (G : List (MvPolynomial (Fin (m + n)) ℤ)) (S : SquarePiece m n G) :
    ∃ S' : SquarePiece m' n' (G.map (rename (trR hm hn))), S'.h = rename (trR hm hn) S.h ∧
      S'.e = S.e ∧ S'.f = S.f := by
  subst hm hn
  rw [map_rename_trR_rfl, rename_trR_rfl]
  exact ⟨S, rfl, rfl, rfl⟩

/-- **Chart data transported** (alone). -/
theorem chartData_transport' {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (G : List (MvPolynomial (Fin (m + n)) ℤ)) (T : ChartData G) :
    ∃ T' : ChartData (G.map (rename (trR hm hn))), T'.c = rename (trR hm hn) T.c ∧
      T'.x = fun i => rename (trR hm hn) (T.x (Fin.cast hn.symm i)) := by
  subst hm hn
  rw [map_rename_trR_rfl]
  refine ⟨T, (rename_trR_rfl _).symm, funext fun i => ?_⟩
  rw [rename_trR_rfl]
  rfl

/-- **A presentation transported** (the presented algebra is unchanged). -/
def qbTransport {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (G : List (MvPolynomial (Fin (m + n)) ℤ)) :
    SmoothCert.QB G ≃+* SmoothCert.QB (G.map (rename (trR hm hn))) :=
  quotRenameEquiv G (trR hm hn)

end BezoutCounterexample.Constructive
