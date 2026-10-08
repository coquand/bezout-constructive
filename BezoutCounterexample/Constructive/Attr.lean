import Lean

/-!
# The `cprim` attribute

A declaration tagged `@[cprim]` is a *trusted constructive primitive*: its statement is
constructively valid, but its Lean proof may be classical. The constructivity audit
(`Constructive/Audit.lean`) does not look inside such declarations; it lists them separately,
so that each one can be checked by hand.
-/

open Lean

initialize cprimAttr : TagAttribute ←
  registerTagAttribute `cprim
    "trusted constructive primitive: constructively valid statement, possibly classical proof"
