# Remaining classical uses in the `main_theorem_tower` cone

## Final status (2026-10-07, after d45–d52)

Count: **0**. Measured with `ana/cone-int.lean`, the same criterion as below: a project declaration in
the cone counts if its type or value directly uses a forbidden constant (`Classical.*`, `sorryAx`, `em`,
`not_not`, …) or a hidden-choice wrapper (`Exists.choose`, `Finset.toList`, …). The cone has 4812
declarations. Build 9188 jobs; ConstructiveAudit PASS (1921 declarations, 8 trusted primitives).

What remains, all outside the project's own reasoning:
- `#print axioms main_theorem_tower` is still `[propext, Classical.choice, Quot.sound]`, through
  whitelisted Prop-level Mathlib lemmas (Hilbert basis, localisation, `Set.Finite` bookkeeping). These are
  known constructive facts.
- The 8 `@[cprim]` primitives: sign splitting and cotransitivity on ℝ, positive inverses and roots,
  Banach fixed point with rate ½, polynomial gcd over a discrete field, the primitive-element shift.
- Unique choice: `towerResult := towerResult''` by `WellFounded.fix` plus `uniqueChoice`.

Count history: 95 → … → 57 (d37) → 49 (d41) → 46 (d42) → 38 (group B) → 28 (d44) → 19 (d45) → 15 (d46)
→ 14 (d47) → 13 (d48) → 12 (d49, d50) → 1 (d51) → 0 (d52). Details per step are in `docs/rewrite-tasks.md`.

The last statement changes:
- `LocusComp` carries `gensI` and `chartn`, with charts from the certificate (d48).
- `IsMaxInv` → `IsMaxInvPt` in `IsComplexity`, `ReesData` and every `hmax` (d50).
- The ChainLift chain uses `ChartCoverPtL` (d51).

## Historical classification (2026-10-05, count 66)


Measured in the rehearsal `~/COLL/bezout-int` after the D3.5 integration build, with
`ana/cone-int.lean`: a declaration counts when its own type or value directly uses a forbidden constant
(`Classical.*`, `sorryAx`, …) or a hidden-choice wrapper (`Exists.choose`, `Finset.toList`, …). The cone
walk stops at `@[cprim]`. Count: **66** after integration round 2 (before D3.5: 80; after the D3.4 rehearsal fixes: 73; batch D removed 7).
Path evidence: `ana/cone-path.lean` (shortest path from the root to each engine hit).

Kind of fact:
- **(a)** a known constructive fact, Prop-level Mathlib (Zariski, Hilbert basis, `Set.ncard`/`Finset` bookkeeping);
- **(b)** a constructive twin is already built (leaf), and only the wiring of the consumer is missing;
- **(c)** genuinely open: needs new constructive work.

The D3.4/D3.5 leaves were added to the root in this integration as modules, but no statement was
switched beyond what the rehearsal already had. Each "(b)" row names the twin and the consumer that still
has to move. A leaf is clean only if its *transitive* cone is clean; see "Leaf check" at the end.

## Route 1: `goodV` of an invariant (`InvAt.goodV` → `IsInv.goodV` → `IsInv.exists_run` → Method 1)

Path: `TI.step ← IsRun.transfer_bound ← IsInv.of_run ← IsInv.exists_run ← IsInv.goodV ← InvAt.goodV ←
inv_mem_Γ ← maxinv_mem_Γ ← ReesData.e_ne_zero_iff`.

| hit | why classical | twin | kind |
|---|---|---|---|
| `MC.exists_run` | `by_cases J.Adm I`, classical `SA.step_run` | `MC.exists_run_pos` (RunPos), at points (`Pt.dec_local`) | b |
| `MC.SA.step_run`, `step_run_of`, `step_Q`, `step_data_Q` | `by_contra`/decidability of the step data on a local ring without decided residue field | `SA.step_run_pos`, `step_data_pos` (StepRunPos/StepPos) | b |
| `MC.exists_adm_Q` (+`_proof_1_1`), `MC.exists_sa_adm_Q` | `Nat.find` on a classical predicate, `by_contra` | `MC.exists_adm_pos`, `sa_zero_pos` (StepRunPos) | b |
| `exists_min_Xi` | minimum over an arbitrary set of multi-indices (`classical`) | `XiMinPos` (positive minimum, box search) | b |
| `TI.step` | `by_contra` search over `Fin n'`, weight comparisons | `TI.step_pos`, `IsRun.transfer_bound_pos` (TransferPos) | b |
| `IsInv.goodV`/`InvAt.goodV` (enter through `inv_mem_Γ`, `isMaxInv_mem_ΓN'`, `InvAt.mem_Γ`) | via `IsInv.exists_run` | `IsInv.exists_run_pos` (RunPos); `InvAt.goodV_pt` = to write (3 lines) | b |

Consumer to move: the users of `InvAt.goodV` at the witnessing point (`InvariantPt.InvAt.mem_Γ`,
`ChainLiftComplexity.isMaxInv_mem_ΓN'`, `ReesData.e_ne_zero_iff`), with the point witness
`IsMaxInv.exists_pt` (MaxInvPt).

## Route 2: max centres and `cRF` inside `LocData` (`LocData.cRF_eq_transport` → `MC.exists_max_FT/PB/Q`)

Path: `exists_min_Xi ← SA.step_data_Q ← exists_sa_adm_Q ← MC.exists_max_Q ← exists_max_PB ← exists_max_FT ←
cRF_eq ← LocData.cRF_eq_transport ← div_le_span_pow ← divisorial_le`.

| hit | why classical | twin | kind |
|---|---|---|---|
| `LocData.RFB_map_eq`, `RFB_map_of_not_mem`, `exists_pow_mul_mem`, `g_mul_num_mem`, `locusIdeal_le_p` | `LocData` at an arbitrary maximal ideal; `by_contra`/`classical` membership | LocDataPt API: `RFB_map_eq_pt`, `RFB_map_of_mem`, `exists_pow_mul_mem_pt`, `g_mul_num_mem_pt`, `locusPt_le_p` (LocDataPtLemmas, ChartCoverPtLGlue) | b |
| `mem_maxLocus_of_le` | `exists_invAt`/`invAt_semicont` at a maximal ideal, `by_contra` | `mem_locusPt_of_le_ptL` (LocDataPtProd) | b |
| `exists_maxInv` | `sSup`-style maximum over maximal ideals | `exists_isMaxInv_pt` (MaxInvPt), `exists_isMaxInv_of_hasPres` (MaxInvPos) | b |

| `cRF_eq` and `MC.exists_max_FT/PB/Q` on the I3 path `LocusComp.exists_pow_mem_compFPt → cRF_eq` | the maximal centre at a local ring without a decided residue field | `LocusComp.exists_pow_mem_compFPt_ptL` via `cRF_eq_of_rf` + `LocDataPt.rf` (coll-8a, ComponentFilPtL; its cone has only the 9 Prop-level Centre/Chart (a) hits); consumers to switch: ChainLiftChartDimRees:61, ReesGlobal:285–286 | b |

Consumer to move: `div_le_span_pow`/`div_eq_span` (P.Divisorial), the `compFil` chain (`compF_map`), from
`LocData` to `LocDataPt`/`ChartCoverPtL` (coll-8a's hloc/hglob are the same move).

## Route 3: charts at a maximal ideal (`exists_centred_chart` → `IsRegularSystemOfParameters.exists_chart`)

Path: `exists_chart_away ← exists_chart_atPrime ← exists_centred_chart ← IsRegularSystemOfParameters.exists_chart ←
MarkedCenter.exists_mc ← isInvariant_iff_invAt ← invAt_inv ← ReesData.h𝔭c`.

| hit | why classical | twin | kind |
|---|---|---|---|
| `IsRegularSystemOfParameters.exists_chart` | `choose` of coefficients, `by_contra` on units | charts from the certificate: `ChartDim.exists_chart_away` (coll-8a, ChartDimPt) | b |
| `exists_chart_away` | `Classical.choose` of a chart at a maximal ideal (regular local ring) | `ChartDim.exists_chart_away` | b |
| `Chart.IsCentred.mem_sup_pow_succ`, `Chart.IsCentred.pow_eq_span` | `choose`/`not_not` in the associated graded of a regular local ring | none; only reached through route 3 | a |
| `Pt.ofIsMaximal._proof_2` | `Classical.em` zero test (comparison point of a maximal ideal) | off path once route 3 and the bridge `LocusComp.of_minimalPrimes` go | a |

## Route 4: `s ∉ 𝔪` on the Rees algebra (`RF_mul_not_mem` → `compFil_mul_not_mem_pt`)

Path: `RF_mul_not_mem ← compFil_mul_not_mem_pt ← rees_s_prime ← torsor_s_prime ← torsor_spec`.

| hit | why classical | twin | kind |
|---|---|---|---|
| `RF_mul_not_mem` | `by_contra` on membership in `RF`, residue field not decided | at points the residue field is decided (`Pt.dec_local`); a `RF_mul_not_mem_pt` is a short variant | b (twin to write, short) |
| `isLocalization_away_s`, `vertex_eq_span`, `vtx._simp_2` | `classical` on supports / `not_not` simp lemmas over `Fin` | mechanical (decidable support, `Fin`) | a |
| `span_s_isPrime` (+`_proof_1_2..4`) | `classical`, Rees primality at maximal ideals | none built: `rees_s_prime_of_dyn` passes `hdec := em`, and the DynGr/DynRees/DynTorsor bridges are stale and unbuilt. coll-8a is writing `compF_dec_of_cover` + `compFil_mul_not_mem_pt` + `span_s` via `span_s_dyn` with `Q := False`; consumers Rees.lean:647/655, SDiv:72, GCDStep:278/361 | c (in progress) |
| `VertexData.nonempty` | `choose` of vertex data at a maximal ideal | `VertexData.nonempty_ptL` (coll-8a, in progress) | b |
| `vertexG_data`, `vertex_invariant` (if in the cone) | the SA steps run classically at the vertex | point twin with the `_pos` steps at `q₀` planned (coll-8a) | c |
| `rees_smooth` (via `reesLoc_formallySmooth`) | smoothness of the Rees algebra at maximal ideals | coll-8a's rees-cert (`ChainLiftRees*`, `ChainLiftChartDimRees`); consumers still use `Algebra.Smooth`/`ringKrullDim` | b |
| `ReesData.drop` | `by_contra` at a maximal ideal of the Rees algebra | point argument via `Q : Pt (ReesAlg)`; needs the D3.4 twins to take the I4 instances instead of `[Algebra.Smooth ℚ A]` (D3.6, coll-7c) | b |
| `ReesData.𝓡plus_eq_span`, `exists_reesScale_not_mem`, `reesMap_isLocalization`, `reesLoc_formallySmooth`, `rees_finiteType`, `compF_map` | `by_contra`/`choose`/Noetherian generators of the Rees layer | coll-8a's rees-cert leaves (ChainLiftRees*) cover `rees_smooth`; the rest open | c |

## Route 5: the torsor invariant at maximal ideals (`torsor_invAt`)

| hit | why classical | twin | kind |
|---|---|---|---|
| `torsor_invAt` | `classical`; `exists_invAt` at a maximal ideal of `U` | at points: TorsorPt's `torsor_locus_down/up` use it at `q.ker`; a point proof needs `invAt` at points of `U` (ptL API on `U`, with `chartDim_U`) | b/c |
| `PrincipalizationData.torsor_invariant`, `PrincipalizationData.divisorial_decrease`, `components_eq_of`, `eq_of_forall_isMaximal` | `by_cases` on `maxinv` equality, Jacobson + `Set.ncard` | `torsor_decrease_pt`, `divisorial_decrease_pt` (TorsorPt, DivisorialPt) | b |
| `exists_torsorY_not_mem`, `exists_torsorY_not_mem_map` | `by_contra` search for a generator off a prime | `exists_torsorY_not_mem_map_pt` (TorsorPt, decided search) | b |

## gensF (generators of the filtration steps)

| hit | why classical | twin | kind |
|---|---|---|---|
| `gensF`, `span_gensF`, `genPairs`, `genPairs_mem` (+simp), `mem_genPairs` (+simp), `exists_gen_not_dvd`, `hasPres_adjoin_over` | `(IsNoetherian.noetherian _).choose`, `Finset.toList` (hidden choice) | `canonGensF`/`canonGenPairs` (ReesGlobal) with an enumeration; `Constructive.Enum` (leaf, added to the root, not wired) | b (statement change: `[Enum A] [Fact (HasPres A)]` on the torsor modules; decided by coll-01, postponed to D3.6) |

## The rest: the top level on `maxinv`

| hit | why classical | twin | kind |
|---|---|---|---|
| `inv`, `inv.eq_1`, `invAt_inv`, `maxinv`, `maxinv.eq_1`, `maxinv_spec`, `ord_spec` | `Classical.choose`/`dite` with classical decidability, `sSup` | `IsMaxInv` (MaxInvPos), `exists_isMaxInv_pt` (MaxInvPt), `kOf` (InvariantPt) | b (needs `ReesData` with `e`, `he : IsMaxInv I e`: the top-level statement switch) |
| `ne_zero_iff_lt_numNonzero` | `Set.ncard` | `ne_zero_iff_lt_kOf` (InvariantPt) | b |
| `ReesData.h𝔭c` | `IsNoetherian.noetherian` generators of `locusPt` (TEMPORARY bridge `LocusComp.of_minimalPrimes`) | `ReesData.CompData.locusComp` (ReesComp), `exists_comp_data` (ReesPt) | b |
| `Loc.spread_ideal_le`, `spread_run` | `by_contra`, classical spreading | `spread_ideal_le_list`, `spread_run_pos` (SpreadPos) | b |
| `towerResult` | `Classical.choice` of the theorem (Task A C2: data by `WellFounded.fix`) | coll-8a's C2 plan (`complexityLT'_wf`, `canonComp`, `commonDen`) | c |

## D3.6 list (decided, not in this integration)

- CRFGen proof-only edit (coll-8a): compFil's `mul_le`/`zero_eq` fields and `I_le_compFil` via `cRF_mul_le_gen`, `cRF_of_nonpos_gen`, `Iloc_le_cRF_one`. Removes `LocusComp.mem` and `cRF_eq` from everything typed over compFil.
- Weakening of the D3.4/D3.5 twins' `[Algebra.Smooth ℚ A]` to the I4 instances, so they apply at the Rees algebra (needed by the point proof of `drop`).
- `hmax` binders of the engine switched to points (IsMaxInvPt), by script, in a clone.
- Group B: `gensF`/`genPairs` → `canonGensF`/`canonGenPairs` with `[Enum A] [Fact (HasPres A)]` (Constructive/Enum, built, not wired).
- Callers of routes 1–3 switched to the `_pos`/ptL twins: `InvAt.goodV_pt`, LocDataPt cRF, charts from `ChartDim.exists_chart_away`, `RF_mul_not_mem` at points.

## Leaf check (transitive)

Transitive cone of each leaf's main theorems (`ana/cone-leaf.lean`, bezout-int after round 2). Hits are
cone members that directly use a forbidden constant.

**Clean (0):** `ne_zero_iff_lt_kOf`, `weight_le_dec` (InvariantPt); `MC.exists_run_pos`, `IsInv.exists_run_pos`
(RunPos); `local_structure_pt` (LocalPt); `spread_run_pos` (SpreadPos); `IsRun.transfer_bound_pos` (TransferPos);
`MC.exists_adm_pos` (StepRunPos); `exists_invAt_semicont_ptL`, `mem_locusPt_of_le_ptL`, `LocDataPt.exists_dim`
(LocDataPtProd).

**Not clean:**

| leaf root | hits | through |
|---|---|---|
| `InvAt.mem_Γ`, `IsMaxInv.exists_zero_eq` (InvariantPt) | 9 | route 1 (`InvAt.goodV` → `IsInv.exists_run` → `MC.exists_run`, `TI.step`, step_*_Q, `exists_min_Xi`) + the 2 Centre (a) hits; fix: `InvAt.goodV_pt` |
| `exists_isMaxInv_pt`, `IsMaxInv.exists_pt` (MaxInvPt), `exists_comp_data` (ReesPt), `divisorial_decrease_pt` (DivisorialPt) | 11 | `exists_invAt`/`invAt_semicont` at maximal ideals (`spread_run`, `exists_chart_away`, route 1); fix: the ptL lemmas with `hchart` |
| `torsor_decrease_pt`, `torsor_count_pt` (TorsorPt) | 41 | the above + `torsor_invAt`, the Rees layer (route 4), `gensF` |
| `StarC.eq_zero_pt` (StarPt) | 1 | `TI.step` (via the classical transfer behind `IsInv`) |
| `length_control_torsor_pt` (StarPt) | 39 | `PrincipalizationData`/`ReesData` (`maxinv`, `h𝔭c`), routes 1–4, `gensF` |
| `LocusComp.exists_chartCoverPtL` (ChartCoverPtL) | 2 | Centre (a) hits `mem_sup_pow_succ`, `pow_eq_span` |
| `ChartCoverPtL.global_of_RFB_pt`, `.mem_RFB_of_mem` (ChartCoverPtLGlue) | 8 | Centre (a) + `MC.exists_max_Q` chain (`step_Q`, `exists_sa_adm_Q`, `exists_min_Xi`); fix: coll-8a's CRFGen/ComponentFilPtL |

