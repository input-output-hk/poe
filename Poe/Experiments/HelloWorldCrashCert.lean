import Poe.Reflect
import Poe.Bridge
import Poe.Examples.HelloWorld

/-!
# Whole-validator CEK certificates

`gen_uplc` (transcribe the real compiled term) + the now-total `toBlasterData`
(`Poe.Bridge.toBlasterByteString`) let `native_decide` evaluate a whole
validator on a concrete input through Blaster's CEK machine. So we can certify
its actual on-chain behaviour — accept and reject — on real `ScriptContext`
inputs, not just hand-written toy terms.

`validatorETerm` is `HelloWorld.validatorE` as the translator compiles it: a
`Data → Unit` fast-path term (0 `chooseData`) that faults on a wrong shape. The
theorems below are the reject and accept guarantees at the UPLC level.
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
