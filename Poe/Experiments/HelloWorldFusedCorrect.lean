import Poe.Experiments.HelloWorldFused

/-!
# Precision of the fused decider (Lean-source level)

Two guarantees about `HelloWorldFused.parse`, both about the `Data` model —
independent of any compilation style:

* `parse_isSome_iff_wellFormed`: the cheap fused decider accepts *exactly* the
  audited `WellFormed` predicate — no false accepts, no false rejects.
* `parse_some_faithful`: when it accepts, the extracted `owner`/`msg`/`sigs`
  really are the bytes at their ledger-defined positions ("owner is definitely
  owner" — the `SpendingScript`→`Just`→`Datum`→`.b` field, etc.).
-/

namespace Poe.Experiments.HelloWorldFused

open Poe.PlutusData (Data IsByteStringList)
open Poe.Examples.HelloWorld (WellFormed TxInfoOk RedeemerOk ScriptInfoOk)

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

/-- **The validator always crashes (aborts) on ill-formed input** — the property
    we were chasing, here kernel-checked for *every* `ctx`, with nothing in the
    trusted base but the Lean kernel (no evaluator, no solver, no compiler).

    In the decide style the rejection is an explicit `abort ()` in the Lean
    source, so it is a plain equation rather than an implicit builtin fault; the
    translator maps `abort` to UPLC `error`, so the deployed term faults on
    exactly the inputs `WellFormed` rejects. Corollary of
    `parse_isSome_iff_wellFormed` + `validatorE_none`. -/
theorem validatorE_rejects_illformed (ctx : Data) (h : ¬ WellFormed ctx) :
    validatorE ctx = Poe.Prelude.abort () := by
  refine validatorE_none ctx ?_
  cases hp : parse ctx with
  | none => rfl
  | some e => exact absurd ((parse_isSome_iff_wellFormed ctx).mp (by simp [hp])) h

end Poe.Experiments.HelloWorldFused
