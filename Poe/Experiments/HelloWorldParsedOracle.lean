import Poe.Experiments.HelloWorldParsed
import Poe.Oracle

/-!
Oracle suite for `HelloWorldParsed.validatorE` — the parsed-boundary
style where `WellFormed` is decided explicitly at the entry point.

Three well-formed cases (accept / wrong message / wrong owner) match every
other oracle suite in the project. A fourth case — ill-formed input — is
specific to this style: `validatorE_bad` proves the else branch is real
Lean code, and this oracle confirms the compiled UPLC actually errors on
inputs that don't match `WellFormed`, not just theoretically.

Two further abort cases pin the tightened constructor tags: a redeemer or
`TxInfo` under a non-zero tag is otherwise perfectly valid, but the real
`FromData` decoder rejects any tag ≠ 0 for these single-constructor types,
so `WellFormed` must too — these confirm the tag check has teeth.
-/

namespace Poe.Experiments.HelloWorldParsed

open Poe.Uplc

/-- `redeemerTag`/`txInfoTag` default to the real (tag 0) encoding; override
    them to build otherwise-valid contexts that differ only in a tag the
    tightened `WellFormed` checks. -/
def mkCtx (msg owner : String) (signatories : List String)
    (redeemerTag : Nat := 0) (txInfoTag : Nat := 0) : Term :=
  let txInfo := DataValue.constr txInfoTag
    [ .b "f0".toUTF8, .b "f1".toUTF8, .b "f2".toUTF8, .b "f3".toUTF8
    , .b "f4".toUTF8, .b "f5".toUTF8, .b "f6".toUTF8, .b "f7".toUTF8
    , .list (signatories.map (fun s => .b s.toUTF8)) ]
  let redeemer  := DataValue.constr redeemerTag [.b msg.toUTF8]
  -- tag 1 = SpendingScript; inner 0/0 = Just/Datum (see `ScriptInfoOk`).
  let scriptInfo := DataValue.constr 1
    [.b "ignored".toUTF8, .constr 0 [.constr 0 [.b owner.toUTF8]]]
  .const (.data (.constr 0 [txInfo, redeemer, scriptInfo]))

-- An input that fails WellFormed: ctx is a Constr with zero fields.
def illFormedCtx : Term := .const (.data (.constr 0 []))

#eval show Lean.CoreM Unit from do
  Poe.Oracle.runSuite ``validatorE
    [([mkCtx "Hello, World!" "alice" ["alice", "bob"]], .unit)]
  Poe.Oracle.runSuiteAborts ``validatorE
    [ [mkCtx "wrong message" "alice" ["alice", "bob"]]
    , [mkCtx "Hello, World!" "mallory" ["alice", "bob"]]
    -- ill-formed: WellFormed fails, else branch fires, UPLC errors
    , [illFormedCtx]
    -- valid but for one tag the tightened WellFormed now rejects
    , [mkCtx "Hello, World!" "alice" ["alice", "bob"] (redeemerTag := 1)]
    , [mkCtx "Hello, World!" "alice" ["alice", "bob"] (txInfoTag := 1)]
    ]

end Poe.Experiments.HelloWorldParsed
