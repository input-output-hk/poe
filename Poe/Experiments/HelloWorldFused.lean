import Poe.Examples.HelloWorld
import Poe.Prelude
import Poe.Lib.DataDecoding

/-!
# Style 6: fused single-pass parse (`Data → Option Evidence`)

Same on-chain decision as `HelloWorldParsed` (style 2E) — reject ill-formed
input, accept well-formed — but validation and extraction happen in *one*
traversal instead of `wellFormedB`-then-`parse`. `parse` returns `none` on any
shape mismatch and `some evidence` otherwise; `validatorE` matches on that.

Measured smaller than 2E (882 vs 1233 bytes) because it drops the double
traversal. It still emits the full set of `chooseData` nodes, though: returning
`Option` means "must not fault," which is the same totality demand that forces
the defensive 5-way dispatch. Fusion removes the redundant *second* extraction,
not the shape checks — see `Poe.Experiments.CrashCertificate` for the style that
drops the checks entirely.
-/

namespace Poe.Experiments.HelloWorldFused

open Poe.PlutusData (Data)
open Poe.Lib.DataDecoding (elemBytes)

/-- Values extracted from a well-formed `ScriptContext`. -/
structure Evidence where
  msg   : ByteArray
  owner : ByteArray
  sigs  : List ByteArray

/-- Walk the signatories list once: validate (every element is a `.b`) and
    extract in the same pass. `none` on the first non-bytestring element. -/
def parseSigs : List Data → Option (List ByteArray)
  | []        => some []
  | .b b :: t => match parseSigs t with
                 | some r => some (b :: r)
                 | none   => none
  | _         => none

/-- Fused validate + extract. Tags match the audited ledger shape (see
    `Poe.Examples.HelloWorld`): ScriptContext 0, TxInfo 0, redeemer 0,
    ScriptInfo 1 (SpendingScript), Just 0, Datum 0. -/
def parse : Data → Option Evidence
  | .constr 0 [txInfo, redeemer, scriptInfo] =>
    match txInfo, redeemer, scriptInfo with
    | .constr 0 (_::_::_::_::_::_::_::_:: .list sigs ::_),
      .constr 0 [.b msg],
      .constr 1 [_, .constr 0 [.constr 0 [.b owner]]] =>
        match parseSigs sigs with
        | some s => some ⟨msg, owner, s⟩
        | none   => none
    | _, _, _ => none
  | _ => none

/-- Business logic on structured types — no `Data` in scope. -/
def validatorCore (e : Evidence) : Bool :=
  e.msg == "Hello, World!".toUTF8 && elemBytes e.owner e.sigs

/-- Deployable entry point: parse once, then check-or-abort. -/
def validatorE (ctx : Data) : Unit :=
  match parse ctx with
  | some e => Poe.Prelude.check (validatorCore e)
  | none   => Poe.Prelude.abort ()

theorem validatorE_none (ctx : Data) (h : parse ctx = none) :
    validatorE ctx = Poe.Prelude.abort () := by
  simp only [validatorE, h]

theorem validatorE_some (ctx : Data) (e : Evidence) (h : parse ctx = some e) :
    validatorE ctx = Poe.Prelude.check (validatorCore e) := by
  simp only [validatorE, h]

end Poe.Experiments.HelloWorldFused
