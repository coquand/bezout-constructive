# Cluster (1) of the cone audit: can the invariant be made constructive? (analysis, 2026-10-04)

Paper analysis only (coll-7c). No Lean was edited or built.

**Scope.** Cluster (1) of `docs/pending/cone-audit-main_theorem_tower.tsv` is the maximal locus and
the invariant. Its modules are:
- `Principalization/{MaxLocus, Stable, Rees, ReesVertex, ReesGlobal, ReesSmooth, Invariant, Globalize}`;
- `BezoutCounterexample/{MarkedCenter, LengthControl, Invariant, Rees}`.

They contribute 2087 (constant, module) rows to the cone.

**Sources.**
- bezout1.pdf §3.3–3.7: Def 3.2, Thm 3.3 (1)–(5), Notation 3.4, Lemma 3.5, Thm 3.6, Lemma 3.7.
- ATW [1], Brais [2], as quoted there.
- Perdry (perdry2.pdf §4).
- Coquand–Quitté, cffr.pdf: Lemma 2.3, and the "elimination of minimal primes" of
  Coquand–Lombardi 2006 [CL].
- `~/COLL/bezout-positive.tex` §1 and §3.
- `docs/maxlocus-plan.md`, `docs/d5-plan.md`.

## 0. Constructive setting and tools already available

$A = \mathbb{Q}[X_1..X_N]/(G)$ is a smooth domain, given by a presentation (`HasPres`), and
$I = (f_1..f_r) \ne 0$ is explicit. These tools are available:

| tool | content | Lean |
|---|---|---|
| (G) | Gröbner decisions in `A`: membership, `1 ∈ J`, colon, contraction from `A_g`, radical membership (Rabinowitsch) | `Groebner`, `HasPres.mem_dec`, `Colon`, `PresContract`, `HasPres.exists_radical` |
| (PB) | `PolyBar`: inductive Noetherianity of `ℚ[Y]` | `polyBar` (audited) |
| (NS) | explicit points: `1 ∉ (l)` gives `z : A → L`, `L/ℚ` finite and factorial, `z` onto | `NullJac`, `HasPres.exists_point` (audited) |
| (MP) | minimal primes (Perdry 4.3/4.4): a finite list of `PrimeFF` primes covering the primes over `I`, with every minimal prime among them | `Lasker.fln`, `MinPrime.HasPres.exists_prime_cover`, `gens_of_minimalPrime` |
| (F2⁺) | positive (F2): `∃ α, z(∂^α h) ≠ 0` or `h ∈ (x_{<j})` | `Constructive/PosF2.pos_F2` |
| cover | bar induction on `A/I` with certificates at explicit points | `Constructive/PosCover.exists_cover`, `Principalization/PosCover`, `PosLocus` |
| lex | decision of `≤_lex` for supports `< n` | `Constructive/LexDec` |

At an explicit point `z`, membership in `𝔪_z = ker z` is decided in `L`.

**Source of the remaining classical steps.** Every classical step in cluster (1) is of one of the
following kinds:
1. the quantifier "for every maximal ideal `𝔪`" over Mathlib's `IsMaximal`, which has no
   decidable membership;
2. an existence obtained from that quantifier by Zorn (`Ideal.exists_le_maximal`) or by
   `IsJacobsonRing`;
3. `IsNoetherianRing` used to choose generators;
4. `minimalPrimes`, `ringKrullDim` and `height` used as invariants;
5. a minimum taken classically, in Method 1.

`bezout-positive.tex` §1 already shows that explicit closed points suffice. A certificate on `D(g)`
determines the invariant on all of `D(g)` (`IsRun.transfer_bound` needs no centredness). So the
uniform repair is: replace "every maximal ideal" by "every explicit point", and replace "every
point" by a finite explicit cover.

---

## 1. The invariant at an explicit point

### 1.0 Which derivations: one chosen chart, intrinsic results
Every `∂^β` in this document is a monomial in the **dual derivations of a chart**. It is never a
monomial in the ambient `∂/∂Y_i` of `ℚ[Y]`. The chart is built in three steps.

1. *Ambient chart on `D(μ)`.* `A = ℚ[Y₁..Y_N]/(G₁..G_c)`, with `c = N − n`. Choose a `c × c`
   minor `μ = det(∂G/∂Y_K)` with `z(μ) ≠ 0` (§1.4). The complementary variables `x = Y_J`,
   `J = K^c`, form a chart (`Chart`) on `A_μ`. Its dual derivations come from implicit
   differentiation:
   `∂_j = ∂/∂Y_j − Σ_{k∈K} ((∂G/∂Y_K)^{-1} ∂G/∂Y_j)_k ∂/∂Y_k`, for `j ∈ J`.
   These are explicit `ℚ`-derivations of `A_μ` with denominators powers of `μ`. They kill the
   `G_i` and satisfy `∂_j x_{j'} = δ_{jj'}`; this is `Chart.d`/`c.dl`, the basis dual to `dx_J`.
2. *Recentring at `z`.* Set `x'_i = P_i(x_i)`, with `P_i` the squarefree part of the
   characteristic polynomial of `z(x_i)` over `ℚ` (`Chart.recFun`, `Chart.change`). The dual
   derivations become `∂'_i = P_i'(x_i)^{-1} ∂_i`, and `P_i'(x_i)` is a unit at `z`. Now
   `x'_i ∈ 𝔪_z`. The chart is centred, `𝔪_z A_z = (x')` (`exists_centred_N`), which needs
   (F1)/(F2) from `polyBar`.
3. *Method 1* changes the chart further by `nextChart` (replace `x_l` by `∂^{β−e_l} f`). The
   derivations again change by a unit Jacobian.

**Independence of the chart.** The intermediate data depend on the chart: the run, the `β`'s, the
coordinates. The **outputs do not**:
- `ord_z(f) = max {b | f ∈ 𝔪_z^b}` is intrinsic. For *any* centred chart, `f ∈ 𝔪_z^b` iff
  `z(∂^β f) = 0` for all `|β| < b` (p-adic duality, `PChart.mem_F_iff` with weights 1). So
  `min {|β| : z(∂^β f) ≠ 0}` is the same in every centred chart. Directly: under a chart change
  with Jacobian `M`, `z(M)` invertible, the order-`k` derivatives at `z` of an `f ∈ 𝔪^k` transform
  by `Sym^k z(M)`, because the lower-order terms vanish at `z`.
- The invariant is intrinsic by definition (`IsInv`: lexicographic minimum over *all* admissible
  marked centres) and unique (`IsInv.unique`).
- The maximal centre `F_t(𝔪)` is intrinsic (`MC.SA`/`transfer_bound` equality case).

So everything is computed in **one chosen chart** per point, or per certificate open `D(g)`. Only
the results are compared between points and charts, never the intermediate data.

### 1.1 Order: `ord_𝔪(I) = max {b | I A_𝔪 ⊆ 𝔪^b}`
**(a)** `MarkedCenter.ord` (line 366) and `Invariant.lean:212` take `sSup` of a set of naturals and
use `Nat.sSup_mem` and `le_csSup`. Thm 3.3(1) gives `e₁ = 1/ord`:
`inv_zero_eq_one_div_ord`, `exists_inv_zero_eq`.

**(b)** True constructively at explicit points.

**(c)** Take the centred chart of §1.0 at `z`. Then
`ord = min_i min {|β| : z(∂^β f_i) ≠ 0}`. That `𝔪^b` is detected by derivatives of order `< b`
is p-adic duality (`PChart.mem_F_iff`, weights 1).

The search is **not** justified by "`f_i ≠ 0`, so some derivative is nonzero". That is classical
existence, and turning it into a search would be Markov's principle. It is bounded in either of
two ways (§1.6):
- (i) by the bar witness of (F2⁺);
- (ii) by the explicit degree bound `ord_z(f) ≤ deg_u N(f)` of §1.6.

- Verdict: **routine.** Define `ord` as this computed value and prove it maximal. Do not use `sSup`.

### 1.2 Method 1: maximal contact, weights, the ATW invariant
**(a)** `MC.SA.step_data_Q` (QuotSeq.lean:122), `SA.step_run`, `exists_isInv` (Principalization
/Invariant.lean). Method 1 minimises
`Ξ_j(β) = tail_j(β)/(1−λ_e(β))` over `S = {β | ∃ g ∈ I, coeff_β(τ g) ≠ 0, λ_e(β) < 1}`. The
minimiser exists classically, as the infimum of a set of rationals of controlled shape. The next
coordinate is `∂^{β−e_l} f` (maximal contact). `IsInv` is "lexicographically minimal among all
admissible marked centres".

**(b)** True constructively at an explicit point. The output is a run (`IsRun`, data) ending in an
admissible centred chart. `IsInv.of_run` turns it into `IsInv`.

**(c)**
- *Reduce to the generators.* Write `g = Σ a_i f_i`. Then `supp τ(g) ⊆ ⋃ (supp τ f_i + ℕ^n)`.
  Moreover `Ξ_j(β+γ) ≥ Ξ_j(β)` whenever `λ(β+γ) < 1`: the numerator grows by `tail(γ) ≥ 0` and
  the denominator shrinks by `λ(γ) ≥ 0`. So the minimum over `S` is attained at a `β` in the
  support of some `τ f_i`.
- *First candidate.* (F2⁺) with `p_e = (x_{<j})` gives a `β₀` with `z(∂^{β₀} f_i) ≠ 0` and
  `λ(β₀) < 1` for some `i`. Otherwise every `f_i ∈ RF_1`, and the centre is admissible.
- *Bounded search.* `Ξ(β) ≤ Ξ(β₀)` forces `tail(β) ≤ Ξ(β₀)`, and `λ(β) < 1` bounds the head
  exponents (head weights `> 0`). This leaves finitely many `β`, each tested by
  `z(∂^β f_i) ≠ 0` in `L`. Units of `A_z` are decided by `z`.
- *Admissibility* `I ⊆ RF_1(c, e)`: by duality (`IsCentred.mem_RF_iff_Q`) it is a statement about
  infinitely many `β`, because tail weights are `0`. It is decided by (F2⁺) on `p_e`.
- *Termination*: `j` increases and is at most `n`.

This is the corollary of `bezout-positive.tex` §1.4.
- Verdict: **needs work (formalisation only).** The algorithm is a bounded search. Write it as a
  function on runs, with the `ℚ`-valued `Ξ` compared exactly. It replaces the classical
  `Set.Nonempty` and minimum in `step_data_Q`.

### 1.3 The lower bound `∀ J' admissible, e ≤_lex J'.e`
**(a)** The second conjunct of `IsInv`, from `IsRun.transfer_bound` (Transfer.lean, outside the
cluster, used by `IsInv.of_run`, `local_inv`, `LocData.inv`).

**(b)** True. It is a universal statement over all admissible marked centres. Proving it needs only:
- comparisons of rationals;
- membership of `f_i` in the weighted ideals of an arbitrary centred chart `J'.c`, decided at `z`
  by (F2⁺), which holds for any centred chart.

**(c)** Recheck `transfer_bound` for case splits on undecided propositions. Expected: only on `ℚ`
comparisons and on `RF`-membership, both decidable at `z`.
- Verdict: **routine (audit pass).**

### 1.4 Charts and recentring at a point
**(a)**
- `Globalize.exists_chart_away` uses Mathlib's `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`,
  `IsStandardSmooth.iff_exists_basis_kaehlerDifferential`, `Module.Finite.finite_basis` and
  `Fintype.ofFinite`.
- `exists_centred_transport` and `Chart.recFun` (recentring by `minpoly ℚ (residue x_i)`) use
  `residueField_isIntegral` via `finite_of_finite_type_of_isJacobsonRing` (Zariski).
- `local_structure` takes `I.FG` and `𝔪.FG` from `IsNoetherian.noetherian` (Globalize.lean:190).

**(b)** True.

**(c)**
- *Chart.* Smoothness of a presentation is the Jacobian criterion: `1 ∈ (G) + (c × c minors)`,
  with `c = N − n`, as an explicit certificate. At `z` some minor `μ` has `z(μ) ≠ 0`; this is a
  finite search in `L`. The complementary variables are a chart on `D(μ)`.
- *Recentring.* Do not use the minimal polynomial. Use the squarefree part `P_i` of the
  characteristic polynomial of `z(x_i)` over `ℚ`, which is `χ / gcd(χ, χ')`. Then `P_i(z(x_i)) = 0`
  and `P_i'(z(x_i)) ≠ 0` (characteristic `0`), which is all `recFun_det_isUnit` needs. No
  factorisation is required. Kronecker gives the minimal polynomial if it is wanted anyway.
- *Finite generation.* `I.FG` is the given list. `𝔪_z.FG` is `fg_ker_of_quotient_basis` (FGKer),
  or `x_i − P_i`-style generators read off the chart. `L` is finite because (NS) builds it, so
  Zariski is not used.
- Verdict: **routine, but a refactor.** "Smooth" must be carried as a Jacobian certificate
  (`HasPres` plus unit minors) next to Mathlib's `Algebra.Smooth`.

### 1.5 Smooth invariance (Thm 3.3(2))
**(a)** `inv_map_eq_of_localization_polynomial`, `IsInv.transfer`, `Chart.mvPolynomial`,
`IsInv.mapEquiv`.

**(b)** True. The proof transports runs along `A_𝔪 → A_𝔪[t]_q`, which is algebraic.

**(c)** At explicit points, a point of `B` over `z` is an explicit point. Runs push forward
(`IsRun.map`).
- Verdict: **routine.**

### 1.6 No Markov: every "first index such that" search has a witness or a bound
"`f ≠ 0`, hence some `∂^β f(z) ≠ 0`, hence search for it" is classical existence plus an unbounded
search, that is, Markov's principle. It must not be used. There are two ways to avoid it.

**(i) Witness from the bar, uniformly.** (F2⁺) (`pos_F2`) is proved by induction on the
**inductive** predicate `NBar` of the Rees ring `B[Jt]`. Its inductive Noetherianity follows from
`polyBar`, which is proved by structural induction (Coquand–Persson). The recursion
"test all `|α| < k`; if they all vanish, go to `τ_{k+1}`" terminates because the bar is an
inductive definition, not because a solution is known to exist. The result is a disjunction
*with data*: an `α` with `z(∂^α h) ≠ 0`, or `h ∈ p_e`.
- *`j = 0`.* `p_e = 0`, and `h = 0` in `A_z` iff `h = 0` in the domain `A`, decided by (G). So
  for `h ≠ 0` the left disjunct is obtained by case analysis on a proved disjunction. This needs
  no Markov.
- The same holds for Method 1's first candidate `β₀` (§1.2), with `p_e = (x_{<j})`. There, `h ∈
  p_e A_z` is decided by computing the colon `((x_{<j}) : h)` by (G) and testing whether a
  generator has `z ≠ 0`.

The bar gives no a-priori number. It gives a terminating procedure, and that is enough
constructively.

**(ii) An explicit numerical bound for `ord_z`, computable from the presentation.** This is
useful for complexity, and as a check independent of the bar.
1. *Noether normalisation, étale at `z`.* Look for `n` linear forms `u = M Y` with
   `M ∈ ℤ^{n×N}` such that:
   - (a) `A` is finite over `ℚ[u]`;
   - (b) `z(det(∂_j u_i)) ≠ 0` in the chart of §1.0, i.e. `u − u(z)` is a regular system of
     parameters at `z`.

   The bad `M` for (a) lie in the zero set of an explicit polynomial `h_a`: the leading form
   that must not vanish in the classical linear Noether normalisation. The bad `M` for (b) lie in
   that of `h_b = det(∂_j (MY)_i)(z)`. This is a polynomial in `M` with coefficients in `L`, and
   it is nonzero, because `M` selecting `x_J` gives `det = 1`. So `h_a h_b ≢ 0`, with
   explicit degree `D`. A grid `{0..D}^{nN}` contains a nonroot (Schwartz–Zippel /
   combinatorial Nullstellensatz). The search is finite, and each candidate is decided: (a) by
   Gröbner (monic integral relations), (b) in `L`.
2. *Norm.* `N(f) := N_{Frac A/ℚ(u)}(f)` is the constant term, up to sign, of the
   characteristic polynomial of `f`. It is computed by elimination, as the generator of
   `(G, T − f) ∩ ℚ[u][T]` or by a resultant. It lies in `ℚ[u]`, because `A` is integral over
   `ℚ[u]` and `ℚ[u]` is normal. For `f ≠ 0` in the domain `A`, `N(f) ≠ 0`, and `N(f) = f·g`
   with `g ∈ A` (Cayley–Hamilton).
3. *Bound.* `ord_z(f) ≤ ord_z(N f)`, since `ord` is superadditive and `ord_z g ≥ 0`. By (b),
   the chart derivations dual to `du` act on `ℚ[u] ⊆ A` as `∂/∂u_i`. So `ord_z(N f)` is the order
   at `u(z)` of the nonzero polynomial `N(f) ∈ L[u]`, which is at most `deg N(f)`: the top-degree
   form survives the Taylor shift. Hence
   **`ord_z(f) ≤ deg_u N(f)`**, computable from `G`, `f`, `M`. A crude a-priori bound is
   `deg N(f) ≤ [Frac A : ℚ(u)] · deg f`, with the degree `[Frac A : ℚ(u)] ≤ ∏ deg G_i` by
   Bézout. The computed value is sharper.

For `ord_z(I)`, take `min_i` over the generators. For Method 1 at stage `j > 0` the analogue
applies to the image of `f_i` in the presented ring `(A/(x_{<j}))_g`, localised at its component
through `z`. That component is a domain, because `V(x_{<j})` is smooth at `z`. Its generators come
from (MP) (`HasPres.exists_minimal_prime`). This is extra work. Use (i) unless explicit bounds are
wanted.

**Inventory of the other searches in the cluster:**

| search | how it terminates |
|---|---|
| `ord`, Method 1 `β₀` | (i) bar witness; or (ii) the norm bound |
| `Ξ`-minimiser after `β₀` | finite: `tail(β) ≤ Ξ(β₀)`, head exponents bounded by `λ < 1` |
| admissibility `I ⊆ RF_1` | (F2⁺) per generator: witness or membership |
| Jacobian minor with `z(μ) ≠ 0` (§1.4) | finite: evaluate the smoothness certificate `1 = Σ c_k μ_k + Σ a_i G_i` at `z`; some term is nonzero in `L` |
| nonroots (`NullJac`, `exists_nat_nonroot`; `exists_reesScale_not_mem`, §5.4) | among `0..deg` (or `deg + 1` nonzero rationals) |
| Noether normalisation `M` | grid `{0..D}^{nN}` |
| cover `exists_cover` | bar induction on `A/I` (witness, no number) |
| lexicographic comparison | supports `< n` (`LexDec`) |
| factorisation (Kronecker), minimal primes (Lasker tree) | finite candidate sets / bar |
| tower recursion | `Acc` induction (§5.6), no search |

No step uses Markov's principle. Where only classical existence was available, the replacement is
a bar witness or an explicit bound, as above.

---

## 2. Deciding equality and comparison of invariants (the ¬¬/lex issue)

**(a)** `Cover.lean` (the old route): `exists_maxInv_NN` used `nn_le_total`, which is only
¬¬-totality of `≤_lex` on `ℕ → ℚ`. The pointwise bound had to be stated as `¬ (v < v₀)`. The
positive route, `Principalization/PosCover.exists_maxInv_pos` with `Constructive/LexDec`, has no
¬¬.

**(b)** Lexicographic order on `ℕ → ℚ` is not decidable in general: it would decide `∀ i, v i = 0`.
For invariants it is decidable, because their supports lie below `n = dim A`. The length bound
`IsInv.card_eq` / `numNonzero ≤ n` gives this, and on `Fin n → ℚ` the order is decided entrywise.

**(c)** The ¬¬ in the old route had two causes:
- invariants given abstractly as `ℕ → ℚ`;
- the cover answering only `¬ ∀ k, g_k ∈ 𝔪`.

With explicit points both disappear. A point `z` decides which `g_k` avoids it, and the
invariant is a computed vector of length `n`. `eq_or_ne_bounded` (PosLocus) and `LexDec` do this.
- Verdict: **done** (leaf `exists_maxInv_pos`, `PosLocus`). Upstream wiring remains.

---

## 3. The maximum is attained; the maximal locus is closed, with explicit equations

### 3.1 Upper semicontinuity: `invAt_semicont`, `local_inv`, `local_structure`, `maxLocus_local`, `LocData`
**(a)** MaxLocus.lean:100–140, 205, 306–335 and Globalize `local_structure`, which follows
Brais Prop 4.1.1. At `𝔪` there is `g ∉ 𝔪` and a chart on `A_g`. Every point of `D(g)` has
invariant `⪰ e_k`, with equality exactly on `V(x_{<k})`. Classical inputs:
- `IsNoetherianRing` for FG;
- `exists_invAt` (the classical Method 1);
- the `∀ 𝔪'` quantifiers in `LocData.iff`/`rf`.

**(b)** True, as a statement about a certificate: chart, run and spread, all data.

**(c)** `spread_run` (finitely many denominators) turns the run at `z` into a run over `A_g` with
`z(g) ≠ 0`. `transfer_bound` gives the bound at every explicit point of `D(g)`. The classical
`LocData.nonempty`, `exists_invAt`, `invAt_semicont` and `g_mul_num_mem` (the four named classical
steps on the `torsorSGD` path, `bezout-positive.tex` §3) all become constructions from §1.2 and §1.4.
- Verdict: **needs work.** No new mathematics: it is the upstream quantifier change "∀ 𝔪" to
  "∀ explicit points", planned in `bezout-positive.tex` §1.

### 3.2 The maximum is attained: `exists_maxInv` (MaxLocus:151), `maxinv` (Invariant:442)
**(a)** `choose` over all maximal ideals, then `by_contra` and `Ideal.exists_le_maximal` (Zorn) to
get a finite subcover. `maxinv` is defined by `if h : ∃ v, … then h.choose` (`Classical.propDecidable`).

**(b)** True.

**(c)** `exists_cover` (bar induction on `A/I`) gives a finite positive cover by certificates
`(g_i, e^{(i)})`, each with a point `z_i`. Then `v₀ = min_⪯ e^{(i)}` is a minimum of finitely many
vectors in `ℚ^n`. It is attained at some `z_i`, and it bounds every point: pick `i` with
`z(g_i) ≠ 0`, decidably. `maxinv` should be the computed `v₀`, not a `dite` on an undecidable `∃`.
- Verdict: **done in leaf form** (`exists_maxInv_pos`). Upstream: redefine `maxinv`.

### 3.3 The locus is closed, with explicit equations: `maxLocus`, `locusIdeal := sInf (maxLocus)` (MaxLocus:260–264)
**(a)** `locusIdeal` is the intersection of all maximal ideals in the locus. Its generators came
from `IsNoetherianRing` (PosWire `exists_locusIdeal_gens`).

**(b)** True.

**(c)** `PosLocus.exists_locusIdeal_gens_attained` gives
`locusIdeal = {x | ∀ j, x/1 ∈ √(a_j) A[1/g_j]}`, explicit by (G). With the gens threading it is
now on the `torsorSGD` path upstream.
- Verdict: **done** (full build 9053, 2026-10-04). One `by_contra` remains in `locGens_of_ne`. It is
  a membership in a maximal ideal and is decidable at an explicit point.

### 3.4 Points of the locus, and the Jacobson property: `locusIdeal_le_p` (MaxLocus:451), `exists_pow_mul_mem` (MaxLocus:711)
**(a)**
- `locusIdeal_le_p`: if `f` vanishes on the locus, then `f ∈ D.p`. It uses
  `isJacobsonRing_of_finiteType`, `p.jacobson = p` and `by_cases g ∈ 𝔪'`.
- `exists_pow_mul_mem` (spreading a membership between charts): `g ∈ √𝔠` via `𝔠.radical.jacobson`.

**(b)** True, in the effective-Nullstellensatz form.

**(c)**
- *`locusIdeal_le_p`.* Decide `g f ∈ D.p` by (G). If not, (NS) applied to the prime `D.p` (it is
  `PrimeFF`) with `a = g f` gives a point `z` with `z(D.p) = 0` and `z(g f) ≠ 0`. Then `z` is in
  the locus (`LocData.iff` on `D(g)`) and `z(f) ≠ 0`, which contradicts `f ∈ locusIdeal`. The
  decision is on `ℚ`-data, so the conclusion is positive.
- *`exists_pow_mul_mem`.* Decide `g ∈ √𝔠` by (G) (Rabinowitsch). In the negative branch, (NS) gives
  a point of `V(𝔠) ∩ D(g)`, which contradicts the pointwise statement.
- `jacS_explicit` (PosCover) is this argument.
- Verdict: **routine** (leaf exists). Upstream wiring remains.

---

## 4. Minimal primes, Jacobson, Krull dimension: what can be eliminated

### 4.1 cffr Lemma 2.3 and the elimination of minimal primes
**cffr Lemma 2.3** (Coquand–Quitté): let `I = (a₁..aₙ)` be regular. If `J = 0` in every
`R[1/aᵢ]`, then `J = 0`. If `J` is regular in every `R[1/aᵢ]`, then `J` is regular.

The "elimination" technique of [CL] reads a classical argument through "some minimal prime `𝔭`"
as a dynamical computation, and retains only the elementary consequences:
- `√J = ⋂ minimal primes`;
- `x` is regular modulo a radical ideal iff `x` lies in no minimal prime;
- localising at a minimal prime is replaced by inverting a regular ideal (Lemma 2.3).

**Observation.** In cluster (1) almost every ring is a domain: `A`, `A_g`, `A_𝔪`, the Rees algebra,
`R/sR` (Lemma 3.5(5)), `U`, and `A/𝔭` for a component. In a domain every nonzero ideal is regular,
so Lemma 2.3 reduces to the trivial principle "`J = 0` in `R[1/a]` with `a ≠ 0` implies `J = 0`".
All covers that occur are also comaximal: chart covers of `V(𝔭)` together with `D(q)`, and covers
of `Spec A` by certificate opens. There Lemma 2.3 is the comaximal local–global principle.

So the technique enters in its elementary form: check on an explicit finite cover instead of at
every (minimal) prime. Its regular-but-not-comaximal generality is not needed here. The one
non-domain ring is `A/P`, with `P = locusIdeal` radical and `r` components. Arguments over `A/P` are
exactly the minimal-prime uses below.

### 4.2 Each use of minimal primes

| # | use (file:line) | statement | replaceable by elimination / regularity + local–global? | or needs explicit primes? |
|---|---|---|---|---|
| m1 | `Invariant.components := (maxLocusIdeal I).minimalPrimes`, `numComponents := ncard` (Invariant:454–457) | the components `V(𝔭₁..𝔭ᵣ)` of Thm 3.3(3) and the count `c(I)` | **No.** `c(I)` is part of the termination measure, and the tower blows up **one irreducible component at a time**. The torsor step needs `𝔭` prime (factoriality/GCD of `U`; for `r ≥ 2`, `Cl U ≅ ℤʳ/ℤ(1..1) ≠ 0`, d5-plan Handoff 2). | **Needs explicit primes**: (MP) gives them, `HasPres.gens_of_minimalPrime`. |
| m2 | `Ideal.finite_minimalPrimes_of_isNoetherianRing` (Invariant:540, PosWire:72) | finitely many components | Superseded by the explicit finite list of (MP), deduplicated by (G) (`𝔭 = 𝔭'` decidable). | explicit list |
| m3 | `Ideal.exists_minimalPrimes_le` (Invariant:550) | a point of maximal invariant lies on some component | **Yes, elementary.** At an explicit point `z` with `z(P) = 0`, test `z(𝔭ᵢ) = 0` for each `i` (finitely many generators, decided in `L`). If every test fails, pick `fᵢ ∈ 𝔭ᵢ` with `z(fᵢ) ≠ 0`. Then `∏ fᵢ ∈ ⋂ 𝔭ᵢ ⊆ √P` (m5), so `z(∏ fᵢ) = 0`, a contradiction in the field `L`. | uses the list, not minimality |
| m4 | `eq_p_of_minimal`, `minimalPrimes_sup_eq_top` (MaxLocus:470, 494), `mem_maxLocus_of_minimal` | the local prime `D.p` is the unique component through `𝔪`; components are pairwise comaximal | **Yes, by points.** Decide `1 ∈ 𝔭 + 𝔭'` by (G). Otherwise (NS) gives `z ∈ V(𝔭 + 𝔭')`, and `LocData` at `z` gives `D.p` with `𝔭 = D.p = 𝔭'` (the `eq_p` argument: `D.p ⊆ 𝔮` from `P_le_map`, and `𝔮 ⊆ D.p` from §3.4). Minimality of `𝔮` is used only to get `𝔮 ⊆ D.p` from `P ⊆ D.p`. With the (MP) list it holds by `PrimeFF` and the cover property. | list, decided |
| m5 | `Ideal.sInf_minimalPrimes` (radical = intersection of minimal primes) in `one_mem_sup_colon` (PosWire:87) | `x ∈ ⋂ 𝔭ᵢ ⇒ x ∈ √P` | **Yes, exactly the elimination of [CL].** Along the Lasker/Perdry split tree, `√J = √(J+a) ∩ √(J+b)` when `ab ∈ J`: if `xᵐ ∈ J+a` and `xⁿ ∈ J+b`, then `x^{m+n} ∈ (J+a)(J+b) ⊆ J`. So the leaves of the tree satisfy `⋂ Pᵢ ⊆ √J` elementwise (Perdry Lemma 4.3), with no prime ideals. `one_mem_sup_colon` then follows by CRT from m4. | elementwise identity from the tree |
| m6 | `Ideal.radical_eq_sInf` in `Ctrl.dvd_pow` (MaxLocus:563) | `Ctrl M g` (every prime avoiding `g` avoids `M`) gives `m ∣ g^b` | **Yes, by definition change.** `Ctrl` is the classical form of `m ∣ g^b`. All `M` that occur are generated by finitely many explicit denominators (`spread_run`), so carry the divisibilities `mₖ ∣ g^{bₖ}` as data. This is [CL]'s replacement of "for all primes" by the radical. | none |
| m7 | `h𝔭 : 𝔭 ∈ (locusIdeal I v₀).minimalPrimes` as a hypothesis throughout ReesVertex, ReesGlobal, Rees.lean:157 | the chosen component | Replace by a record: `𝔭` explicit with `PrimeFF`, its `ChartCover` (the separating `q`), and `P ≤ 𝔭`. Every downstream use of minimality goes through m4/m5. | explicit prime (data) |

**Conclusion on minimal primes.**
- Minimality is genuinely needed only for **m1**, where the components are the centres and their
  number is the measure. There the primes must be explicit, and (MP) already supplies them.
- The other uses (m2–m7) reduce to:
  - the explicit list;
  - the elementwise radical identity m5, which is pure [CL];
  - decisions at explicit points.
- cffr Lemma 2.3 is not needed beyond its comaximal case in this cluster.

### 4.3 Uses of the Jacobson property
`locusIdeal_le_p` and `exists_pow_mul_mem` (§3.4) are replaced by (NS) plus (G). Zariski's lemma
appears as `finite_of_finite_type_of_isJacobsonRing` in:
- `MarkedCenter:161`, `Globalize:67` (residue field finite);
- `ReesVertex:722` `comap_isMaximal_of_finiteType` (contraction of a maximal ideal is maximal),
  `IsArtinianRing.isField_of_isDomain`.

All of these disappear at explicit points:
- `L` is finite by construction.
- The composite `A → R → L` of an explicit point of the Rees algebra is an explicit point of `A`,
  onto the subfield generated by the image. Its kernel is maximal in the positive sense, because
  inverses are images (`NullJac`, "z onto").
- Verdict: **routine.**

### 4.4 Krull dimension and height, and whether grade or depth helps

**Uses.**
- `MarkedCenter`: `IsRegularSystemOfParameters` requires `ringKrullDim S = n`.
  `Chart.IsCentred.ringKrullDim_eq` uses `ringKrullDim_le_spanFinrank_maximalIdeal`, `Ideal.height`,
  `ringKrullDim_le_iff_isMaximal_height_le`, `Order.LTSeries.length_le_krullDim` and
  `Ideal.exists_maximal`. `chart_size_eq_ringKrullDim`, `exists_ringKrullDim_eq_natCast` and
  `ringKrullDim_localization` also live here.
- `LengthControl`:
  - `Star.dim_le : ringKrullDim B ≤ N + m`;
  - `ringKrullDim_U = dim A + 1 + ℓ`;
  - `star_initial`.
- `Rees.lean:696` `numNonzero_inv_add_le` (`numNonzero(inv) + m ≤ dim A`, Lemma 3.7(2)).
- `exists_maxInv_pos` / `PosLocus`: invariant supports bounded by `dim A`.

**What is actually used.** Every use needs only the **chart size** `n(A)`. This is the common
length of all charts, equal to the rank of `Ω_{A/ℚ}`, and computable from the presentation as `N`
minus the rank of the Jacobian. Specifically:
- *Constancy*: `Chart.card_eq`. It holds constructively, since free modules of ranks `n` and `n'`
  over a nontrivial ring with `ℚ ⊆ R` satisfy `n = n'` by determinants.
- *Additivity*: it is read off the explicit charts. The Rees chart `reesChart` has `n+1`
  coordinates, and the torsor chart has `n + 1 + ℓ`.
- *The bound* "support of the invariant `≤ n`": a run has at most `n` steps.

Krull dimension and height appear only because Mathlib's `IsRegularLocalRing` formulates
"regular system of parameters" through them. The identification `n = dim` is the only place where
chains of primes enter.

**Replacement.** Define `dim A := n(A)` (the rank of `Ω`) and drop `ringKrullDim`. Then:
- `Star.dim_le` becomes a bound on chart size;
- `ringKrullDim_U` becomes a chart count;
- `IsRegularSystemOfParameters` becomes "centred chart".

The equivalences `n(A) = dim A` and `Chart.IsCentred ⇔ regular system of parameters` stay as
classical **comparison theorems** for the statement map (`docs/STATEMENTS.md`), outside the
constructive path.

**Grade or depth.** These are not needed. If one wants an intrinsic, prime-free characterisation of
`n` at a point, two are available:
- the embedding dimension `dim_{κ(z)} 𝔪_z/𝔪_z²`, computed by linear algebra in `L` from the
  Jacobian;
- the homological (Koszul) grade of `𝔪_z` in `A_z`, in the sense of cffr §6 / true grade, which
  equals `n` because the coordinates of a centred chart form a regular sequence.

The second is constructive, by the Taylor embedding (F1) into `L[[X]]`, where `X₁..Xₙ` is
regular. It is more work than the first and buys nothing for the tower. The grade/regularity
technique would matter if a height bound were used to control a *non-domain* (e.g. `Star` for
`A/P`). In cluster (1) no such use exists.
- Verdict: **routine, but a definitional refactor** of `MarkedCenter`/`LengthControl`.

---

## 5. Remaining steps of the cluster

### 5.1 The global centre `F_t` (Thm 3.3(4)): `compF` (MaxLocus:759), `compF_map`, `compFil_mem_iff`, `ReesGlobal.gensF` (IsNoetherian `choose`, ReesGlobal:353)
**(a)** `F_t = {f | f ∈ cRF(𝔪, t) for every maximal 𝔪 ⊇ 𝔭}`. Membership is a `∀ 𝔪` statement.
Generators come from Noetherianity.

**(b)** True.

**(c)** `F_t = ⋂ᵢ (RF_t^{(i)} ∩ A)` over the separated chart cover of `V(𝔭)`, with `(1)` on
`D(q)`. It is computable by (G) (PosWire O3, `HasPres.exists_gens_of_charts`).
`compF_map` (`F_t A_𝔪 = cRF(𝔪, t)`) holds by the partition of unity of `mem_cRF_of_cover`
(Cover.lean, positive given the cover).
- Verdict: **needs work** (wiring; leaves exist).

### 5.2 Local–global identities on `A` and on the Rees algebra
**(a)** These lemmas check something at every maximal ideal:
- `ReesGlobal:150–165`: `J ≤ J'` if `J A_𝔪 ≤ J' A_𝔪` for every maximal `𝔪`, by `by_contra` and
  `exists_le_maximal` on the colon ideal;
- `compFil_F_nonpos`;
- `not_mem_loc` (ReesVertex:159, torsion-freeness of `F_a/F_{a+1}`);
- `compFil_mul_not_mem` (ReesVertex:200, `gr` is a domain, checked at one `𝔪 ⊇ 𝔭` obtained by
  Zorn).

**(b)** True.

**(c)**
- *`J ≤ J'`.* Decide `J ≤ J'` by (G). Better, prove `J ⊆ J'` on each `D(gᵢ)` of a comaximal
  explicit cover and glue, since `1 = Σ cᵢ gᵢ^N`. This is cffr Lemma 2.3 in its comaximal case.
- *`not_mem_loc`.* On each chart piece `D(gᵢ)`,
  `gr_F(A_{gᵢ}) ≅ (A/𝔭)_{gᵢ}[u_1..u_k]` (weighted, Lemma 3.5(4)). This is a domain, because
  `(A/𝔭)_{gᵢ}` is a domain and polynomial rings over domains are domains (constructive). So
  `h ∉ 𝔭` is **regular** on `gr`, and `h x ∈ F_{a+1}`, `x ∈ F_a` give `x ∈ F_{a+1}` on each
  piece, hence globally. This is the regularity-plus-local–global pattern, and it replaces both
  the `by_contra` and the `∀ 𝔪`.
- *`compFil_mul_not_mem`.* The single point `𝔪 ⊇ 𝔭` is an explicit point of `V(𝔭)`, given by
  (NS) since `1 ∉ 𝔭` is decided.
- Verdict: **routine.**

### 5.3 Smoothness and finite presentation of the Rees algebra: `ReesSmooth.reesPsi_ker`, `rees_formallySmooth`, `ReesGlobal.rees_smooth`, `reesAlg_finiteType`
**(a)**
- `Algebra.FormallySmooth` (a lifting property over all square-zero extensions), `.comp`,
  `.of_isLocalization`, `.polynomial`, `.of_equiv`, `Algebra.Smooth.mk`, `smoothLocus_eq_univ_iff`.
- `rees_smooth` picks, for each prime of `R`, a maximal ideal of `A` below it (`exists_le_maximal`).

**(b)** True, in Jacobian form.

**(c)** Locally,
`R_𝔪 = S[s, u_1..u_k]/(xᵢ − s^{wᵢ} uᵢ)` (`reesPsi_ker`, algebraic). The relations have
Jacobian `I_k` with respect to the chart derivatives `∂_{xᵢ}`, so the presentation is standard
smooth on each chart piece. With `T⁻¹ = s` and `R[1/s] = A[T^±]`, these pieces form a finite
cover of `Spec R`. "`1 ∈ Jacobian ideal`" holds on each piece, hence globally (comaximal
local–global). Finite presentation comes from the explicit generators `g T^j` (`reesGenSet`,
using `gensF` from §5.1) and from relations computed by (G) as an elimination ideal.
- Verdict: **needs work.** The same "smooth = Jacobian certificate" refactor as §1.4, plus an
  elimination computation. No open mathematics.

### 5.4 The drop of the invariant (Thm 3.6): `Drop.drop`, `Rees.drop`, `ReesVertex.exists_reesScale_not_mem`, `vertex_isInv`, `VertexData`
**(a)** At every maximal `P` of `R` with `I_w ≤ P`, `s ∈ P` and `P` off `V(R₊)`, the invariant of
`I_w` is `≻ v₀`. The proof uses the vertex, spreading, and the `𝔾_m`-action. The polynomial
argument `exists_reesScale_not_mem` picks `μ ∈ ℚ^×` with `Q(μ) ∉ P` by `classical`.

**(b)** True at explicit points `z : R → L`.

**(c)**
- *Polynomial argument.* `Q ∈ (R/P)[X]` has nonzero constant term in the field `L`, so among any
  `deg Q + 1` nonzero rationals one is a nonroot, found by a finite search
  (`exists_nat_nonroot`).
- *Vertex data.* `VertexData.nonempty` and the vertex invariant are Method 1 at the explicit
  vertex point, plus `transfer_bound`.
- *From pointwise to global.* The pointwise drop must give the global `maxinv(I_w) ≺ v₀`, or
  equality with fewer components. Apply `exists_cover` to `V(I_w)` on the presented `R`, with a
  certificate at each explicit point. Then decide, for each point, which case holds:
  - `z(s) = 0` and some `z(f T^j) ≠ 0` (`f ∈ F_j`): drop;
  - `z(s) ≠ 0`, i.e. a point of `A[T^±]` with invariant `inv_{z'}(I) ⪯ v₀`: equality only over
    the other components.

  All these are decisions in `L`.
- Verdict: **needs work** (wiring through `exists_cover` on `R`). Constructive.

### 5.5 Derivation stability and the length bound (Lemma 3.7): `Stable.deriv_mem_RF`, `length_le_of_derivations`, `LengthControl.Star`, `Rees.deriv_mem_𝓕`, `numNonzero_inv_add_le`
**(a)**
- The flow `f ↦ Σ tᵐ δᵐ f/m!` modulo `t^N` (`flowHom`, characteristic 0), plus uniqueness of
  the maximal centre on `S[t]_{(𝔪,t)}`, give `δ(xᵢ) ∈ F_{eᵢ}`.
- `Classical.byContradiction` is used on `RF`-membership.
- `Star` says: "for every maximal `𝔪 ⊇ 𝔟` there are `δ_j`, `z_q` with `det ∉ 𝔪`".

**(b)** True.

**(c)**
- The flow is a ring homomorphism by binomial identities, which is constructive.
- Uniqueness of the maximal centre is `transfer_bound`'s equality case at an explicit point.
- The `by_contra` is on `RF`-membership, which is decidable by (F2⁺).
- `Star` should be restated positively: explicit `δ_j`, `z_q` with `1 ∈ 𝔟 + (det)`, or a finite
  cover by such data. In the tower the derivations are explicit (the Euler derivation
  `T(Σ wᵢ xᵢ ∂ᵢ − T∂_T)`, the torsor derivations), and the determinant certificate is an
  identity.
- Verdict: **routine** (restatement).

### 5.6 Termination of the tower: `Γ`, `Γ_wellFoundedOn` (Invariant:638–689), `complexityLT_wf` (PrincipalizationStar:43), measure `(maxinv 𝔟, numComponents 𝔟)`
**(a)** The measure is lex on `ΓN N × ℕ`. `Γ` (Thm 3.3(5)) consists of entries `D!/a`, with zeros
only at the end. Well-foundedness is proved via the encoding
`encW : Γ → Lex (Fin N → WithTop ℕ)`, `a ↦ a`, and zero `↦ ⊤`, using `wellFounded_lt`,
`Function.Lex.wellFoundedLT`, `WithTop.instWellFoundedLT` and `Set.WellFoundedOn`. The paper's
argument ("first entries eventually stabilise") is classical.

**(b)** True constructively as **inductive** well-foundedness (`Acc`). Lex on `(ℕ ∪ {∞})^N`
is accessible by nested induction over the `N` positions, and the `ℕ` factor for `c(I)` likewise.

**(c)**
- Mathlib's `WellFounded` is `Acc`-based, so the statement is the right one. Its proofs for
  `Pi.Lex`/`WithTop` may be classical, so reprove them by nested `Acc` induction (about 100 lines),
  or whitelist them after review.
- The tower's recursion needs `maxinv` and `numComponents` as **computed** values: from the cover
  (§3.2) and from the (MP) list (m1).
- `encW_lt`, `next_weight_form` and `inv_mem_Γ` are arithmetic on `ℚ`.
- The length bound `N` comes from `Star`/Lemma 4.4, which is chart counting (§4.4).
- Verdict: **routine.**

---

## 6. Verdicts

| step | content | verdict |
|---|---|---|
| 1.0 | derivations = chart duals; results chart-independent | routine (one chosen chart per point) |
| 1.1 | `ord` at a point | routine |
| 1.6 | no Markov: witnesses (bar) or explicit bounds (norm after Noether normalisation) | routine for (i); needs work for (ii), which is optional |
| 1.2 | Method 1 / maximal contact / weighted invariant as a terminating search | needs work (formalisation; maths in bezout-positive §1.4) |
| 1.3 | lex lower bound (`transfer_bound`) | routine (audit pass) |
| 1.4 | charts (Jacobian minor), recentring (squarefree charpoly), FG | routine; refactor "smooth = Jacobian certificate" |
| 1.5 | smooth invariance | routine |
| 2 | equality/comparison of invariants, ¬¬/lex | done (leaves) |
| 3.1 | upper semicontinuity, `LocData` at explicit points | needs work (quantifier change ∀𝔪 → ∀ explicit points) |
| 3.2 | maximum attained, `maxinv` computed | done (leaf); redefine `maxinv` upstream |
| 3.3 | locus ideal with explicit equations | done (upstream, 2026-10-04) |
| 3.4 | Jacobson uses | routine (NS + G; leaf `jacS_explicit`) |
| 4.2 m1 | components as centres, `c(I)` | needs explicit primes: available via (MP); wiring needed |
| 4.2 m2–m7 | other minimal-prime uses | routine: elimination [CL] (m5), decisions at points (m3, m4), definition change (m6) |
| 4.3 | Zariski / Artinian residue fields | routine (finite `L` by construction) |
| 4.4 | Krull dimension, height | routine; refactor `dim := rank Ω`; grade/depth not needed |
| 5.1 | global centre `F_t`, generators | needs work (wiring; leaves exist) |
| 5.2 | local–global identities, torsion-freeness of `gr` | routine (regularity + comaximal local–global) |
| 5.3 | smoothness/finite presentation of the Rees algebra | needs work (Jacobian refactor, elimination) |
| 5.4 | drop of the invariant | needs work (cover on `R`, decisions in `L`) |
| 5.5 | derivation stability, `Star` | routine (positive restatement) |
| 5.6 | termination measure | routine (`Acc` proofs; computed `maxinv`, `c(I)`) |

**No step of cluster (1) is an open problem.**

## 7. Overall assessment

Cluster (1) is constructive in substance. Two inputs are genuinely non-elementary, and both are
already constructive leaves:
- the minimal primes needed as centres: Perdry/MinPrime, resting on factorisation over `ℚ`, whose
  one trusted primitive is `exists_primitive_shift`, justified by ¬¬;
- explicit points: `NullJac`.

Everything else is one of three things:
- **Quantifier changes**: "every maximal ideal" becomes "every explicit point" (`L` finite, with
  decidable `ker z`), or "every point" becomes "a finite explicit cover from `exists_cover`, glued
  by the comaximal local–global principle". This removes Zorn, Jacobson, Zariski and every
  `by_contra`/`by_cases` on membership.
- **Elimination of minimal primes** [CL] for the uses that are not centres: the radical as an
  elementwise intersection along the Lasker tree; `Ctrl` as divisibility data.
- **Definitional refactors**:
  - `dim := rank Ω` instead of `ringKrullDim`/`height`;
  - "smooth" as a Jacobian certificate, next to Mathlib's `Algebra.Smooth`;
  - `maxinv`, `numComponents`, `ord` as computed values, not `choose`/`sSup`.

cffr Lemma 2.3 is useful as a **pattern**: check on `R[1/aᵢ]` and glue. In this cluster every ring
is a domain or every cover is comaximal, so only its elementary case is needed. Grade and depth are
not needed, because chart size replaces dimension.

**Cost estimate.** The largest items are:
1. the upstream quantifier change in `MaxLocus`/`Globalize`/`LocData` (3.1, 5.1);
2. Method 1 as a constructive search (1.2);
3. the Jacobian-certificate refactor of smoothness (1.4, 5.3);
4. the drop theorem through a cover on the Rees algebra (5.4).

None needs new mathematics beyond `bezout-positive.tex` §1 and §3. The natural order is
1.2 → 3.1 → 5.1 → 5.4. The definitional refactors 4.4 and 1.4/5.3 can come in one batched
upstream edit.
