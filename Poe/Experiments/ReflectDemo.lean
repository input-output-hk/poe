import Poe.Reflect
import Poe.Bridge
import Poe.Examples.First

/-!
# `gen_uplc` demonstration

`doubleTerm` is generated from the translator at elaboration time.

`double_certificate'` restates `Bridge.double_certificate` against the *actual
translator output* — no hand copy in the statement. This is the payoff: a CEK
certificate about the term the compiler really produces.

(The generated term is not `rfl`-equal to `Bridge.doubleUplcTerm`: they differ
only in the cosmetic `.lam` binder-name strings — the generator keeps the real
LCNF names, the hand copy wrote `"x0"/"x1"` — which the emitter ignores and the
CEK machine never inspects. The `#eval` below confirms identical emitted text.)
-/

namespace Poe.Experiments.ReflectDemo

open PlutusCore.UPLC Poe.Bridge

gen_uplc doubleTerm := Poe.Examples.double

/-- The `double` certificate, stated against the translator's real output. -/
theorem double_certificate' :
    ∀ (x : Int), ∃ (n : Nat),
      CekMachine.cekExecuteProgram
        (toBlasterProgram (.program (1, 1, 0) doubleTerm))
        [Term.Term.Const (.Integer x)] n
      = CekMachine.State.Halt (CekValue.CekValue.VCon (.Integer (Poe.Examples.double x))) := by
  intro x
  refine ⟨20, ?_⟩
  simp only [doubleTerm, toBlasterProgram, toBlasterTerm, toBlasterBuiltin, Poe.Examples.double]
  rfl

#eval show Lean.CoreM Unit from do
  IO.println s!"emit matches hand-transcription: \
    {Poe.Emit.emit doubleTerm == Poe.Emit.emit Poe.Bridge.doubleUplcTerm}"

end Poe.Experiments.ReflectDemo
