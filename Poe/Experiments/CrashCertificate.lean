import PlutusCore.UPLC.Term
import PlutusCore.UPLC.CekMachine
import Poe.Uplc
import Poe.Bridge

/-!
# Let-it-crash: reasoning about the unhappy path at the CEK level

The assume-style validators (1E/3E/4E) and the decide-style ones (2E/6) sit at
two extremes: assume-style is cheap (0 `chooseData`, ~460 bytes) but cannot even
*state* what happens on ill-formed input (the `WellFormed` proof is in the
signature, so the validator can't be applied without one); decide-style pays
~40 bytes per `chooseData` node (~400 bytes total for HelloWorld) to make
rejection a total Lean function.

Let-it-crash is the third point: deploy the fast-path term (0 `chooseData`) and
let a wrong `Data` shape *fault* a builtin — a fault is a valid rejection (the
transaction fails). A `Data → Unit` Lean function can't distinguish "accepts"
from "faults" (`Unit` has one value), so the unhappy path can't be a theorem
about the *function*. It is instead a theorem about the compiled term's CEK
execution — the same `cekExecuteProgram` methodology as `Poe.Bridge`'s happy-path
certificates, but landing in `State.Error` rather than `State.Halt`.

`crash_cert` below is the minimal proof of concept: `unBData` applied to a
`Constr` faults, and the CEK machine reaches `State.Error`. Discharged by
`rfl`, like the `Poe.Bridge` certificates.

Two current limits:
* **Bytestring-free inputs only.** `toBlasterData` is `sorry` on `.b` (the
  `ByteArray`/`String`-`ByteString` gap — see `Poe.Bridge`), so an input
  carrying real `B` bytes can't be encoded through the bridge. Certifiable
  ill-formed inputs are the shape-only ones (wrong constructor/arity at a node
  reached before any `B`), e.g. the empty `Constr 0 []` here.
* **Whole validators need transcription tooling.** These certificates reference
  a hand-written `Uplc.Term` (`crashTerm`); transcribing a ~460-byte validator
  by hand is impractical. Scaling this to a real validator wants an elaborator
  that splices `Poe.Translate.translate`'s output into a `def` (`Uplc.Term`
  derives `ToExpr`, so this is feasible — it just isn't built yet).
-/

namespace Poe.Experiments.CrashCertificate

open PlutusCore.UPLC Poe.Bridge

/-- Minimal fast-path term: apply `unBData` straight to the argument, no
    defensive `chooseData`. Faults at runtime on any non-`B` argument. -/
def crashTerm : Poe.Uplc.Term := .lam "x0" (.app (.builtin .unBData) (.var 0))

def crashProgram : Poe.Uplc.Program := .program (1, 1, 0) crashTerm

/-- The unhappy path, certified: on an ill-formed (non-`B`) input the compiled
    term drives the CEK machine to `State.Error`. `Constr 0 []` is bytestring-
    free, so it encodes through the bridge without hitting the `.b` `sorry`. -/
theorem crash_cert :
    ∃ n, CekMachine.cekExecuteProgram (toBlasterProgram crashProgram)
      [Term.Term.Const (.Data (.Constr 0 []))] n = CekMachine.State.Error := by
  refine ⟨10, ?_⟩
  simp only [toBlasterProgram, toBlasterTerm, toBlasterBuiltin, crashProgram, crashTerm]
  rfl

/- Same benign `sorryAx` taint as `Poe.Bridge.double_certificate`: it flows
   through `toBlasterTerm` mentioning `toBlasterConst` (per-declaration axiom
   tracking), not through this proof — `crashTerm` has no `.const` node and the
   input `Data` is built directly, so no `sorry` is reached at reduction. -/
#print axioms crash_cert

end Poe.Experiments.CrashCertificate
