import Poe.Experiments.HelloWorldFused
import Poe.Oracle

/-!
Oracle for the fused single-pass style (`HelloWorldFused.validatorE`). Same
cases as `HelloWorldParsedOracle`: accept a well-formed ctx, abort on wrong
message / wrong owner / ill-formed input / wrong constructor tags.
-/

namespace Poe.Experiments.HelloWorldFused

open Poe.Uplc

def mkCtx (msg owner : String) (signatories : List String)
    (redeemerTag : Nat := 0) (txInfoTag : Nat := 0) : Term :=
  let txInfo := DataValue.constr txInfoTag
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer  := DataValue.constr redeemerTag [.b msg.toUTF8]
  let scriptInfo := DataValue.constr 1
    [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .const (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

def illFormedCtx : Term := .const (.data (.constr 0 []))

#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``validatorE
    [([mkCtx "Hello, World!" "alice" ["alice", "bob"]], .unit)]
  Poe.Oracle.runSuiteAborts ``validatorE
    [ [mkCtx "wrong message" "alice" ["alice", "bob"]]
    , [mkCtx "Hello, World!" "mallory" ["alice", "bob"]]
    , [illFormedCtx]
    , [mkCtx "Hello, World!" "alice" ["alice", "bob"] (redeemerTag := 1)]
    , [mkCtx "Hello, World!" "alice" ["alice", "bob"] (txInfoTag := 1)]
    ]

end Poe.Experiments.HelloWorldFused
