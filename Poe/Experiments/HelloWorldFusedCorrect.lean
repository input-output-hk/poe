import Poe.Experiments.HelloWorldFused

/-!
# Fused validator: what's proved at the LEAN level

Everything here is about the `Data`/`Bool` model and is **kernel-checked**
(`propext`/`Quot.sound` only — no evaluator, solver, or compiler in the trusted
base). These hold independent of any compilation style.

* `parse_isSome_iff_wellFormed`: the cheap fused decider accepts *exactly* the
  audited `WellFormed` — no false accepts, no false rejects.
* `parse_some_faithful`: when it accepts, `owner`/`msg`/`sigs` really are the
  bytes at their ledger positions ("owner is definitely owner").
* `validatorCore_iff`: the business decision (a `Bool`) is `true` exactly when
  the message and owner-membership conditions hold.

**What is NOT provable here — the Lean/PLC boundary.** The deployed `validatorE`
returns `Unit`, and `Unit` is a subsingleton, so `() = abort ()` in Lean: success
and failure are *indistinguishable* at the Lean level. Any `validatorE ctx =
abort ()` / `= ()` statement is subsingleton-trivial. The genuine "accepts with
`()` vs errors" distinction exists only at the **PLC/CEK level** (`Halt` vs
`Error`) — see `Poe.Experiments.HelloWorldCrashCert`, which pays a compiler-trust
cost (`native_decide`). So the division of labour is:
  - **Lean level**: shape precision, faithful extraction, and the `Bool`
    decision — meaningful, cheap, kernel-checked (this file).
  - **PLC level**: that the `Bool` decision compiles to accept/reject
    (`Halt`/`Error`) — `HelloWorldCrashCert`.
-/

namespace Poe.Experiments.HelloWorldFused

open Poe.PlutusData (Data IsByteStringList)
open Poe.Examples.HelloWorld (WellFormed TxInfoOk RedeemerOk ScriptInfoOk)
open Poe.Lib.DataDecoding (elemBytes_iff ByteArray.beq_iff_eq)

/-- `parseSigs` inverts `List.map .b`: it succeeds on an all-bytestring list,
    returning the underlying bytes. -/
theorem parseSigs_map : ∀ bss : List ByteArray, parseSigs (bss.map Data.b) = some bss
  | []       => rfl
  | b :: bss => by simp only [List.map_cons, parseSigs, parseSigs_map bss]

/-- …and only on an all-bytestring list: success pins the input exactly. -/
theorem parseSigs_eq_some {xs : List Data} {r : List ByteArray}
    (h : parseSigs xs = some r) : xs = r.map Data.b := by
  induction xs generalizing r with
  | nil => simp only [parseSigs, Option.some.injEq] at h; subst h; rfl
  | cons x t ih =>
    cases x with
    | b b =>
      simp only [parseSigs] at h
      cases hpt : parseSigs t with
      | none => rw [hpt] at h; simp at h
      | some rt =>
        rw [hpt] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.map_cons, ih hpt]
    | constr _ _ => simp only [parseSigs] at h; simp at h
    | list _ => simp only [parseSigs] at h; simp at h
    | i _ => simp only [parseSigs] at h; simp at h

/-- `parseSigs` succeeds iff the list is all bytestrings — i.e. iff the `Data`
    list wrapping it satisfies `IsByteStringList`. -/
theorem parseSigs_isSome_iff {xs : List Data} :
    (parseSigs xs).isSome ↔ ∃ bss : List ByteArray, xs = bss.map Data.b := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp h
    exact ⟨r, parseSigs_eq_some hr⟩
  · rintro ⟨bss, rfl⟩
    rw [parseSigs_map]; rfl

/-- **Faithfulness / "owner is definitely owner"**: when `parse` accepts, the
    context genuinely carries `e`'s values at their ledger positions —
    `e.owner` is the `SpendingScript` (tag 1) → `Just` (tag 0) → `Datum`
    (tag 0) → `.b` field, `e.msg` the redeemer's byte field, `e.sigs` the
    signatories. -/
theorem parse_some_faithful (ctx : Data) (e : Evidence) (h : parse ctx = some e) :
    ∃ (f0 f1 f2 f3 f4 f5 f6 f7 : Data) (rest : List Data) (tor : Data),
      ctx = .constr 0
        [ .constr 0 (f0 :: f1 :: f2 :: f3 :: f4 :: f5 :: f6 :: f7 :: .list (e.sigs.map Data.b) :: rest),
          .constr 0 [.b e.msg],
          .constr 1 [tor, .constr 0 [.constr 0 [.b e.owner]]] ] := by
  unfold parse at h
  split at h
  · split at h
    · rename_i f0 f1 f2 f3 f4 f5 f6 f7 sigs rest msg tor owner
      cases hs : parseSigs sigs with
      | none => rw [hs] at h; simp at h
      | some r =>
        rw [hs] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨f0, f1, f2, f3, f4, f5, f6, f7, rest, tor, by rw [parseSigs_eq_some hs]⟩
    · simp at h
  · simp at h

/-- **Precision**: the fused decider accepts exactly the audited `WellFormed` —
    no false accepts, no false rejects. -/
theorem parse_isSome_iff_wellFormed (ctx : Data) :
    (parse ctx).isSome ↔ WellFormed ctx := by
  constructor
  · -- accept ⇒ well-formed: the faithful shape satisfies every sub-predicate
    intro hIS
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hIS
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hctx⟩ := parse_some_faithful ctx e he
    subst hctx
    exact ⟨⟨e.sigs, rfl⟩, trivial, trivial⟩
  · -- well-formed ⇒ accept: each sub-predicate pins its shape, then parse computes
    intro hWF
    unfold WellFormed at hWF
    split at hWF
    · obtain ⟨hT, hR, hS⟩ := hWF
      unfold TxInfoOk at hT; split at hT
      · unfold RedeemerOk at hR; split at hR
        · unfold ScriptInfoOk at hS; split at hS
          · obtain ⟨bss, hbss⟩ := hT
            subst hbss
            simp [parse, parseSigs_map]
          · exact hS.elim
        · exact hR.elim
      · exact hT.elim
    · exact hWF.elim

/-- **Business logic (Lean level)**: the fused validator's `Bool` decision is
    `true` exactly when the message is "Hello, World!" and the owner is a
    signatory. Kernel-checked. This is the meaningful form of "returns true /
    returns false" — stated on the `Bool`, where `true ≠ false`, *not* on the
    `Unit` deployable (where success and abort collapse; see the header). Combine
    with `parse_some_faithful` to read `e.owner` as the genuine datum owner. -/
theorem validatorCore_iff (e : Evidence) :
    validatorCore e = true ↔ e.msg = "Hello, World!".toUTF8 ∧ e.owner ∈ e.sigs := by
  simp only [validatorCore, Bool.and_eq_true, ByteArray.beq_iff_eq, elemBytes_iff]

end Poe.Experiments.HelloWorldFused
