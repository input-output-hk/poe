import PlutusCore.UPLC.Term
import PlutusCore.UPLC.CekMachine
import Poe.Uplc
import Poe.Examples.First

/-!
# D5 (stretch): the increment-2 bridge to PlutusCoreBlaster

`Poe.Uplc.Term`/`Builtin`/`Program` are isomorphic, constructor for
constructor, to Blaster's own `PlutusCore.UPLC.Term.Term`/`BuiltinFun`/
`Program`, so `toBlasterTerm`/`toBlasterBuiltin`/`toBlasterProgram` below
are the "mechanical injection" `Poe.Uplc`'s doc comment promises: a total,
structural embedding. `Const`/`DataValue` are *not* full isomorphisms —
they embed only the sub-fragment Poe needs into Blaster's larger
`Const`/`Data` types (see `Poe.Uplc`'s doc comment for specifics).

Two gaps:

* Blaster's `ByteString` is backed by a Lean `String`
  (`structure ByteString where data : String`), not a `ByteArray` like
  `Poe.Uplc`'s `Const.bytestring`. An arbitrary byte sequence is not valid
  UTF-8, so there is no honest total `ByteArray → Blaster.ByteString`
  embedding via reinterpretation. `toBlasterConst`/`toBlasterData` are left
  `sorry` for `bytestring`/`data`; resolving it (Blaster gaining a real
  byte-sequence representation, or Poe restricting this certificate
  direction to the `ByteArray`-free fragment) is follow-up work.
* `Poe.Uplc.DataValue` is missing two of real `Data`'s five cases (`Map`
  and `I`, integer-as-`Data` — see `Poe.Uplc`'s doc comment), so
  `toBlasterData` can't represent an integer-literal `Data` value yet. -/

namespace Poe.Bridge

open PlutusCore.UPLC

/-- Total: every `Poe.Uplc.Builtin` case names a real `BuiltinFun`
    constructor. Blaster's enum is a strict superset (BLS crypto, more
    batches); Poe's fragment never produces the extra ones. -/
def toBlasterBuiltin : Poe.Uplc.Builtin → Term.BuiltinFun
  | .addInteger => .AddInteger
  | .subtractInteger => .SubtractInteger
  | .multiplyInteger => .MultiplyInteger
  | .divideInteger => .DivideInteger
  | .modInteger => .ModInteger
  | .equalsInteger => .EqualsInteger
  | .lessThanInteger => .LessThanInteger
  | .lessThanEqualsInteger => .LessThanEqualsInteger
  | .equalsByteString => .EqualsByteString
  | .appendByteString => .AppendByteString
  | .lengthOfByteString => .LengthOfByteString
  | .equalsString => .EqualsString
  | .appendString => .AppendString
  | .ifThenElse => .IfThenElse
  | .trace => .Trace
  | .unBData => .UnBData
  | .unListData => .UnListData
  | .headList => .HeadList
  | .tailList => .TailList
  | .nullList => .NullList
  | .encodeUtf8 => .EncodeUtf8
  | .unConstrData => .UnConstrData
  | .unIData => .UnIData
  | .fstPair => .FstPair
  | .sndPair => .SndPair
  | .chooseData => .ChooseData

/-- See the file doc comment: `bytestring`/`data` are the one real gap,
    `ByteArray` has no honest total embedding into Blaster's
    `String`-backed `ByteString` yet. -/
def toBlasterData : Poe.Uplc.DataValue → PlutusCore.Data.Data
  | .constr tag fields => .Constr (Int.ofNat tag) (fields.map toBlasterData)
  | .list xs => .List (xs.map toBlasterData)
  | .b _ => sorry -- ByteArray -> Blaster's String-backed ByteString: no honest total embedding yet

def toBlasterConst : Poe.Uplc.Const → Term.Const
  | .integer i => .Integer i
  | .bytestring _ => sorry -- see toBlasterData
  | .string s => .String s
  | .bool b => .Bool b
  | .unit => .Unit
  | .data d => .Data (toBlasterData d)

/-- Total, structural, one case per constructor — the "mechanical
    injection" by construction. -/
def toBlasterTerm : Poe.Uplc.Term → Term.Term
  | .var i => .Var i
  | .const c => .Const (toBlasterConst c)
  | .builtin b => .Builtin (toBlasterBuiltin b)
  | .lam n t => .Lam n (toBlasterTerm t)
  | .app f a => .Apply (toBlasterTerm f) (toBlasterTerm a)
  | .delay t => .Delay (toBlasterTerm t)
  | .force t => .Force (toBlasterTerm t)
  | .constr i ts => .Constr i (ts.map toBlasterTerm)
  | .case scrut branches => .Case (toBlasterTerm scrut) (branches.map toBlasterTerm)
  | .error => .Error

def toBlasterProgram : Poe.Uplc.Program → Term.Program
  | .program (a, b, c) t => .Program (.Version a b c) (toBlasterTerm t)

/-!
## D5 (stretch): certificate theorem, proved for `double`

`PlutusCore.UPLC.CekMachine.cekExecuteProgram : Program → List Term → Nat
→ State` is fuel-limited (`Nat` steps) via `runSteps`, which treats fuel
exhaustion *before* halting as `State.Error` too — `Eval`/`Return` states
never escape `runSteps` — so `Halt`/`Error` are the only two results, and
the certificate is existential over fuel: for every input, *some* amount
of stepping reaches the halted state matching the source function's Lean
value.

`doubleUplcTerm` is `double`'s compiled shape (see `Poe.Examples.First`),
transcribed by hand rather than threaded through `Poe.Translate.translate`
(a `CoreM` action, not plain data a `theorem` can reference directly). Note
it includes the `let`-desugared identity-continuation wrapper (`(lam x1 x1)
[...]`) that `translateCode`'s `.let` case always emits — the real output is
`(lam x0 [(lam x1 x1) [[(builtin addInteger) x0] x0]])`, which needs 20 CEK
steps to `Halt`.

`AddInteger`'s evaluation never branches on its operands' values, so the
fixed step count `n = 20` works for every `x`. Plain `rfl` discharges the
theorem: the kernel unfolds `toBlasterTerm`/`toBlasterBuiltin`/`step`/
`runSteps`/... symbolically for the free `x`. -/

def doubleUplcTerm : Poe.Uplc.Term :=
  .lam "x0"
    (.app
      (.lam "x1" (.var 0))
      (.app (.app (.builtin .addInteger) (.var 0)) (.var 0)))

def doubleProgram : Poe.Uplc.Program :=
  .program (1, 1, 0) doubleUplcTerm

theorem double_certificate :
    ∀ (x : Int), ∃ (n : Nat),
      PlutusCore.UPLC.CekMachine.cekExecuteProgram
        (toBlasterProgram doubleProgram)
        [Term.Term.Const (.Integer x)]
        n
      = PlutusCore.UPLC.CekMachine.State.Halt
          (PlutusCore.UPLC.CekValue.CekValue.VCon (.Integer (Poe.Examples.double x))) := by
  intro x
  refine ⟨20, ?_⟩
  -- `toBlasterTerm`/`toBlasterProgram` don't reduce via bare `rfl`, but
  -- their auto-generated equation lemmas unfold them; the CEK internals
  -- (`step`/`runSteps`/...) then reduce via plain `rfl`.
  simp only [toBlasterProgram, toBlasterTerm, toBlasterBuiltin, doubleProgram, doubleUplcTerm,
    Poe.Examples.double]
  rfl

/- `#print axioms` reports `sorryAx` here, but the certificate is fully
   proved for `double`: `doubleUplcTerm` has no `.const` node, so
   `toBlasterTerm`'s reduction never touches the `toBlasterConst` branch.
   The taint comes from Lean's per-declaration axiom tracking —
   `toBlasterTerm` is one general function over all of `Poe.Uplc.Term`, one
   branch calls `toBlasterConst` (which has `sorry`s for `bytestring`/
   `data`), and that taints the whole definition regardless of which inputs
   actually reach that branch. Resolving the `ByteArray`/`ByteString` gap
   (see file doc comment) would clear it. -/
#print axioms double_certificate

/-!
## Certificate 2: `absInt` (branching, still no partiality/recursion)

The step up from `double`: real branching (`Decidable`/`ifThenElse`/
`Force`/`Delay`). `absIntUplcTerm` is `absInt`'s compiled shape (see
`Poe.Examples.First`), hand-transcribed like `doubleUplcTerm`.

The two branches take a *different* number of CEK steps to `Halt` (the
negation branch does one extra `SubtractInteger`): 47 for the identity
branch (`x ≥ 0`), 60 for the negation branch (`x < 0`). Since `runSteps`
stays `Halt`ed regardless of extra fuel, a single shared `n = 60` (the
larger) works for *every* `x`.

The proof splits with `rcases x with n | n`, not `by_cases h : x < 0`:
`rfl` (kernel definitional equality) never consults local hypotheses, so
`h` would sit inert while the kernel tries to reduce `x < 0`'s `Decidable`
instance for opaque `x` and gets stuck. Splitting on `Int`'s two
constructors (`ofNat`/`negSucc`) instead makes `x` a constructor
application, and `Int.negSucc_lt_zero` supplies the one fact rfl can't
derive (that any `negSucc n` is negative). The `ofNat n` branch closes by
bare `rfl`; the `negSucc n` branch needs each builtin's implementation
(`ifThenElse`, `subtractInteger`, `expectedArgs`, ...) named in the `simp`
set — same "reduces via equation lemmas, not bare kernel whnf" property as
`double`, chained through `evaluateBuiltinFunction`'s dispatch. -/

def absIntUplcTerm : Poe.Uplc.Term :=
  .lam "x0"
    (.app
      (.lam "x1"
        (.app
          (.lam "x2"
            (.app
              (.lam "x3"
                (.force
                  (.app
                    (.app
                      (.app (.force (.builtin .ifThenElse)) (.var 0))
                      (.delay
                        (.app (.lam "x4" (.var 0))
                          (.app (.app (.builtin .subtractInteger) (.const (.integer 0))) (.var 3)))))
                    (.delay (.var 3)))))
              (.app (.app (.builtin .lessThanInteger) (.var 2)) (.var 0))))
          (.var 0)))
      (.const (.integer 0)))

def absIntProgram : Poe.Uplc.Program :=
  .program (1, 1, 0) absIntUplcTerm

theorem absInt_certificate :
    ∀ (x : Int), ∃ (n : Nat),
      PlutusCore.UPLC.CekMachine.cekExecuteProgram
        (toBlasterProgram absIntProgram)
        [Term.Term.Const (.Integer x)]
        n
      = PlutusCore.UPLC.CekMachine.State.Halt
          (PlutusCore.UPLC.CekValue.CekValue.VCon (.Integer (Poe.Examples.absInt x))) := by
  intro x
  refine ⟨60, ?_⟩
  simp only [toBlasterProgram, toBlasterTerm, toBlasterBuiltin, toBlasterConst, absIntProgram,
    absIntUplcTerm, Poe.Examples.absInt, PlutusCore.UPLC.CekMachine.cekExecuteProgram,
    PlutusCore.UPLC.CekMachine.cekExecuteProgramWithSemanticVariant,
    PlutusCore.UPLC.CekMachine.applyParams, PlutusCore.UPLC.CekMachine.initialState]
  rcases x with n | n
  · rfl
  · simp [Int.negSucc_lt_zero, PlutusCore.UPLC.CekMachine.runSteps, PlutusCore.UPLC.CekMachine.step,
      PlutusCore.UPLC.CekMachine.evalBuiltin,
      PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction,
      PlutusCore.UPLC.BuiltinFunctions.Integer.lessThanInteger, PlutusCore.Integer.lessThanInteger,
      PlutusCore.UPLC.Builtins.expectedArgs, PlutusCore.UPLC.BuiltinFunctions.Bool.ifThenElse,
      PlutusCore.Bool.ifThenElse, PlutusCore.UPLC.BuiltinFunctions.Integer.subtractInteger,
      PlutusCore.Integer.subtractInteger, Int.sub]

-- Same `sorryAx` taint as `double_certificate`, same reason (through
-- `toBlasterConst`/`toBlasterTerm`, not a gap in *this* proof) — see
-- that theorem's own note.
#print axioms absInt_certificate

end Poe.Bridge
