import Lean
import BezoutCounterexample.Constructive.Attr

/-!
# The constructivity audit

`#constructive_audit "whitelist" "report"` inspects every declaration of the modules
`BezoutCounterexample.Constructive.*` (except the audit itself). It traverses types and proof
terms, recursing into project declarations and stopping at

* `@[cprim]` declarations (trusted constructive primitives, listed with their statements);
* external constants (Lean core, Batteries, Mathlib), which must appear in the whitelist file:
  each whitelisted constant has been checked by hand to have a constructively valid statement
  (its Lean proof may be classical) at the types where it is used.

It fails on any external constant in the namespace `Classical`, on `sorryAx`, on the classical
decidability instances of `ℝ`, and on any external constant missing from the whitelist.
-/

open Lean Elab Command

namespace BezoutCounterexample.Constructive.Audit

/-- Constants that are never acceptable. -/
def forbidden (n : Name) : Bool :=
  (`Classical).isPrefixOf n || n == ``sorryAx ||
  n == `Real.decidableLT || n == `Real.decidableLE || n == `Real.decidableEq ||
  n == `em || n == `not_not || n == `by_contradiction || n == `of_not_not

def isProjectModule (mod : Name) : Bool :=
  (`BezoutCounterexample.Constructive).isPrefixOf mod &&
  !(mod == `BezoutCounterexample.Constructive.AuditCore) &&
  !(mod == `BezoutCounterexample.Constructive.Attr)

def parseWhitelist (s : String) : NameSet := Id.run do
  let mut out : NameSet := {}
  for line in s.splitOn "\n" do
    let line := (line.splitOn "#").head!.trim
    if line.isEmpty then continue
    out := out.insert line.toName
  return out

elab "#constructive_audit " wl:str rep:str : command => do
  let env ← getEnv
  let wlText ← IO.FS.readFile wl.getString
  let whitelist := parseWhitelist wlText
  let moduleNames := env.header.moduleNames
  let modOf : Name → Option Name := fun n =>
    (env.getModuleIdxFor? n).map fun idx => moduleNames[idx.toNat]!
  let isProject : Name → Bool := fun n =>
    match modOf n with
    | some m => isProjectModule m
    | none => false   -- declared in the current file: not a project module
  let isPrim : Name → Bool := fun n => cprimAttr.hasTag env n
  -- roots
  let roots := env.constants.toList.filterMap fun (n, _) =>
    if isProject n && !isPrim n then some n else none
  let mut visited : NameSet := {}
  let mut stack : Array Name := roots.toArray
  let mut externals : NameSet := {}
  let mut firstUse : NameMap Name := {}
  let mut prims : NameSet := {}
  let mut bad : Array (Name × Name) := #[]   -- (offending constant, reached from)
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
    for c in used.toList do
      if isProject c then
        if isPrim c then prims := prims.insert c
        else stack := stack.push c
      else
        if forbidden c then bad := bad.push (c, n)
        externals := externals.insert c
        if !firstUse.contains c then firstUse := firstUse.insert c n
  let missing := externals.toList.filter (fun c => !whitelist.contains c)
  -- report
  let mut out := "# Constructivity audit\n\n"
  out := out ++ s!"Project declarations audited: {visited.size}\n\n"
  out := out ++ "## Trusted primitives (`@[cprim]`)\n\n"
  for p in prims.toList.toArray.qsort (·.toString < ·.toString) do
    let some ci := env.find? p | continue
    let ty ← liftTermElabM <| Meta.ppExpr ci.type
    out := out ++ s!"* `{p}` : `{ty}`\n"
  out := out ++ s!"\n## External constants ({externals.size})\n\n"
  for c in externals.toList.toArray.qsort (·.toString < ·.toString) do
    let tag := if whitelist.contains c then "" else "  **NOT WHITELISTED**"
    let src := (firstUse.find? c).map toString |>.getD "?"
    out := out ++ s!"* `{c}` (e.g. in `{src}`){tag}\n"
  out := out ++ "\n## Forbidden constants\n\n"
  for (c, n) in bad do
    out := out ++ s!"* `{c}` reached from `{n}`\n"
  IO.FS.writeFile rep.getString out
  if !bad.isEmpty then
    throwError "FAIL: forbidden constants: {bad.toList}"
  if !missing.isEmpty then
    throwError "FAIL: {missing.length} external constants not whitelisted: {missing}"
  logInfo m!"PASS: {visited.size} declarations, {externals.size} whitelisted externals, \
    {prims.size} primitives"

end BezoutCounterexample.Constructive.Audit
