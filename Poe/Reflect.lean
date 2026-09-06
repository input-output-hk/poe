import Poe.Translate
import Poe.Uplc

/-!
# `gen_uplc`: splice a translator result into a referenceable `def`

`Poe.Translate.translate` is a `CoreM` action, so a `theorem` can't mention its
output directly — which is why `Poe.Bridge`'s certificates hand-transcribe the
compiled term (`doubleUplcTerm`) and only *check* it matches. `gen_uplc` closes
that gap: it runs the translator at elaboration time and binds the resulting
`Uplc.Term` to a real `def`, so certificates can be stated against the actual
translator output rather than a hand copy.

```
gen_uplc myTerm := Some.validator      -- def myTerm : Poe.Uplc.Term := <compiled>
```

Relies on the `ToExpr` instances on `Poe.Uplc.Term`/`Const`/`DataValue`/`Builtin`
(see `Poe.Uplc`). The bound name is placed in the current namespace.
-/

open Lean Elab Command

/-- Run the translator on `src` at elaboration time and bind its compiled
    `Poe.Uplc.Term` to `nm` (in the current namespace) as a real `def`. -/
elab "gen_uplc " nm:ident " := " src:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo src
  let term ← liftCoreM <| Poe.Translate.translate declName
  let name := (← getCurrNamespace) ++ nm.getId
  liftCoreM <| addAndCompile <| Declaration.defnDecl {
    name, levelParams := [], type := mkConst ``Poe.Uplc.Term,
    value := ToExpr.toExpr term, hints := .regular 0, safety := .safe }
