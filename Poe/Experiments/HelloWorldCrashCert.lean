import Poe.Reflect
import Poe.Bridge
import Poe.Examples.HelloWorld

/-!
# Whole-validator certificates at the PLC / CEK level

This is the **PLC-level** counterpart to `HelloWorldFusedCorrect` (which is the
Lean level). The Lean/PLC division of labour:
  - **Lean level** (`*Correct`, kernel-checked): shape precision, faithful
    extraction, and the `Bool` business decision. Cannot speak about `()`-vs-
    error — `Unit` is a subsingleton in Lean.
  - **PLC level** (here): that the compiled term actually *halts* (accepts) or
    *errors* (rejects) — the `Halt`/`Error` distinction that only exists once we
    run the term. This is where accept-vs-reject becomes real.

`gen_uplc` transcribes the real compiled term; the now-total `toBlasterData`
(`Poe.Bridge.toBlasterByteString`) lets `native_decide` evaluate it on a concrete
input through Blaster's CEK machine.

**Trust caveats (why these are weaker than the Lean-level proofs):**
* `native_decide` trusts the Lean compiler + native runtime (`ofReduceBool`,
  `trustCompiler`), not just the kernel.
* Blaster reports fuel exhaustion *before* halting as `Error` too, so
  `isErr = true` alone conflates "faulted" with "ran out of fuel". The two
  theorems are only meaningful *together, at the same fuel*: `accepts_wellformed`
  witnesses that 5000 fuel is enough to halt, so `rejects_illformed`'s `Error` at
  5000 is a genuine fault, not exhaustion. `native_decide` on concrete inputs
  only — no `∀`-quantified guarantee.

`validatorETerm` is `HelloWorld.validatorE` as the translator compiles it: a
`Data → Unit` fast-path term (0 `chooseData`) that faults on a wrong shape.
-/

namespace Poe.Experiments.HelloWorldCrashCert

open PlutusCore.UPLC Poe.Bridge

gen_uplc validatorETerm := Poe.Examples.HelloWorld.validatorE

def prog : Term.Program := toBlasterProgram (.program (1, 1, 0) validatorETerm)

/-- Did the CEK machine end in `Error` (a rejected transaction)? -/
def isErr : CekMachine.State → Bool
  | .Error => true
  | _      => false

private def bs (s : String) : PlutusCore.Data.Data := .B (toBlasterByteString s.toUTF8)

/-- A well-formed `ScriptContext`: `Constr 0 [txInfo, redeemer, spendingScript]`,
    message "Hello, World!", owner "alice" among the signatories. -/
private def goodCtx : PlutusCore.Data.Data :=
  .Constr 0
    [ .Constr 0 [ bs "f0", bs "f1", bs "f2", bs "f3", bs "f4", bs "f5", bs "f6", bs "f7",
                  .List [bs "alice", bs "bob"] ],
      .Constr 0 [bs "Hello, World!"],
      .Constr 1 [bs "ignored", .Constr 0 [.Constr 0 [bs "alice"]]] ]

/-- **Unhappy path**: an ill-formed input (a `Constr` with no fields) faults the
    fast-path accessors — the CEK machine reaches `Error`. Rejection certified
    at the UPLC level, on the real compiled validator. -/
theorem rejects_illformed :
    isErr (CekMachine.cekExecuteProgram prog
      [Term.Term.Const (.Data (.Constr 0 []))] 5000) = true := by
  native_decide

/-- **Happy path**: the well-formed context is accepted — the machine halts, not
    errors. -/
theorem accepts_wellformed :
    isErr (CekMachine.cekExecuteProgram prog
      [Term.Term.Const (.Data goodCtx)] 5000) = false := by
  native_decide

end Poe.Experiments.HelloWorldCrashCert
