import BezoutCounterexample
import BezoutCounterexample.Constructive.AuditCore

/-! Run: `lake env lean docs/pending/cone-count.lean` (repo root; needs the lake lock or a quiet tree).
Count the declarations in the dependency cone of a root (project modules only, stopping at
`@[cprim]`) whose own type or value directly uses a non-project constant with `forbidden` (AuditCore: the
`Classical` prefix, `sorryAx`, `em`, `not_not`, …). Same criterion as coll-8a's 91.

`hiddenChoice` (2026-10-05, coll-7c/coll-01): non-project wrappers whose *value* is a classical choice
(`Exists.choose = Classical.choose`, `Nonempty.some`, `Quot.out`, `Multiset.toList`, …) are counted
too. The cone walk does not enter non-project constants, so without this list such uses (e.g.
`gensF := (IsNoetherian.noetherian _).choose`) were invisible. -/

open Lean Elab Command BezoutCounterexample.Constructive.Audit

/-- Non-project constants that hide a classical choice behind a non-`Classical` name. -/
def hiddenChoice (n : Name) : Bool :=
  [`Exists.choose, `Exists.choose_spec, `Nonempty.some, `Classical.arbitrary,
    `Quot.out, `Quotient.out, `Multiset.toList, `Finset.toList, `Function.invFun,
    `Function.surjInv, `Set.Finite.toFinset, `Fintype.ofFinite, `Set.Finite.fintype,
    `Set.Nonempty.some, `Function.Injective.invFun,
    `Function.extend, `Set.Infinite.natEmbedding].contains n

elab "#cone_classical_count " root:ident : command => do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let modOf : Name → Option Name := fun n =>
    (env.getModuleIdxFor? n).map fun idx => moduleNames[idx.toNat]!
  let isProject : Name → Bool := fun n =>
    match modOf n with
    | some m => (`BezoutCounterexample).isPrefixOf m
    | none => false
  let isPrim : Name → Bool := fun n => cprimAttr.hasTag env n
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root.getId]
  let mut hits : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    let some ci := env.find? n | continue
    let mut used : NameSet := ci.type.getUsedConstantsAsSet
    if let some v := ci.value? (allowOpaque := true) then
      used := v.getUsedConstants.foldl (·.insert ·) used
    if let .inductInfo ii := ci then
      for c in ii.ctors do used := used.insert c
    if used.toList.any (fun c => !isProject c && (forbidden c || hiddenChoice c)) then hits := hits.push n
    for c in used.toList do
      if isProject c && !isPrim c then stack := stack.push c
  logInfo m!"cone size {visited.size}; direct forbidden-constant users: {hits.size}"
  IO.FS.writeFile "docs/pending/cone-classical.txt"
    (String.intercalate "\n" (hits.toList.map toString |>.mergeSort (· ≤ ·)))

#cone_classical_count BezoutCounterexample.main_theorem_tower
