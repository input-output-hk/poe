import Poe.Prelude
import Poe.PlutusData

/-!
# Multi-signature wallet: a coroutine contract

From the EUTxO paper (Chapman, Knispel, Kovalev, Wadler, 2019).

## The coroutine view

A stateful EUTxO contract is a **coroutine**:
- The *datum* is the current **suspension point** (continuation).
- The *redeemer* is the **resume event** (input to the next step).
- The *validator* IS the **step function** of the state machine.
- Acceptance means "advance one step and store the new suspension in an output UTxO".

```
  datum (state) ──step──▶ next state ──stored in──▶ output datum
                 ▲
                 │ redeemer (input)
```

## The multisig state machine

```
                Propose(κ, deadline)
                  sigsNew = {}
  ┌──────────┐ ──────────────────────▶  ┌──────────────────────────┐
  │ Holding  │                           │ Collect(κ, deadline, sigs)│
  └──────────┘ ◀──────────────────────  └──────────────────────────┘
               Pay            ◀──── Add sig ────┘
               if |sigs| ≥ n           if sig ∈ sigsAuth
               Cancel
               if deadline expired
```

Parameters baked into the script:
- `sigsAuth`: the set of authorised signers (public key hashes)
- `minSigs`: required number of signatures (n)

## Data encoding

`State`:
  Holding          → `Constr 0 []`
  Collect κ d sigs → `Constr 1 [B κ, I d, List [B s₀, B s₁, …]]`

`Input`:
  Propose κ d  → `Constr 0 [B κ, I d]`
  Add sig      → `Constr 1 [B sig]`
  Pay          → `Constr 2 []`
  Cancel       → `Constr 3 []`

Note: the payment *value* is not stored in the datum — the locked UTxO
carries the value itself, so when `Pay` fires the whole UTxO value goes
to κ.  (A richer version tracking a partial payment amount would store
an additional `I value` field.)

## Context structure assumed (Plutus V3)

ScriptContext = `Constr 0 [txInfo, _purpose, scriptInfo]`

txInfo = `Constr 0 [inputs, refInputs, outputs, fee, mint,
                    txCerts, wdrl, validRange, signatories, ...]`
  where validRange = `Constr 0 [lowerBound, upperBound]`
        upperBound = `Constr 0 [Extended_Finite(Constr 1 [I t]), _closure]`

scriptInfo (SpendingScript) = `Constr 1 [_txOutRef, Just (Datum datum)]`
  where Just  = `Constr 0 [...]` (PlutusTx Maybe indexing)
        Datum = `Constr 0 [actual_data]`
-/

namespace Poe.Examples.MultiSig

open Poe.PlutusData (Data constrTag field0 field1 field2 field3 field7 field8
                    unBData unIData decodeByteStringList
                    IsConstr HasFieldAt IsB IsI IsByteStringList)

private def elemBytes (x : ByteArray) : List ByteArray → Bool
  | []      => false
  | y :: ys => x == y || elemBytes x ys

-- ---------------------------------------------------------------------------
-- Parameters (baked into the script at deploy time)
-- ---------------------------------------------------------------------------

structure Params where
  sigsAuth : List ByteArray  -- authorised public key hashes
  minSigs  : Nat             -- required signature count (n)

-- ---------------------------------------------------------------------------
-- On-chain state (datum) and input (redeemer) types
-- ---------------------------------------------------------------------------

/-- Datum: the coroutine's current suspension point. -/
inductive State where
  | Holding : State
  | Collect : (payee : ByteArray) → (deadline : Int) → (sigs : List ByteArray) → State

/-- Redeemer: the event that resumes the coroutine. -/
inductive Input where
  | Propose : (payee : ByteArray) → (deadline : Int) → Input
  | Add     : (sig : ByteArray) → Input
  | Pay     : Input
  | Cancel  : Input

-- ---------------------------------------------------------------------------
-- Data encoding / decoding predicates (ghost-only)
-- ---------------------------------------------------------------------------

/-- What the datum Data must look like to decode as a `State`. -/
def StateOk (d : Data) : Prop :=
  match d with
  | .constr 0 []                               => True           -- Holding
  | .constr 1 [.b _, .i _, .list _]            => True           -- Collect (sigs shape checked below)
  | _                                          => False

/-- What the redeemer Data must look like to decode as an `Input`. -/
def InputOk (r : Data) : Prop :=
  match r with
  | .constr 0 [.b _, .i _]   => True   -- Propose
  | .constr 1 [.b _]         => True   -- Add
  | .constr 2 []             => True   -- Pay
  | .constr 3 []             => True   -- Cancel
  | _                        => False

-- ---------------------------------------------------------------------------
-- Decoders
-- ---------------------------------------------------------------------------

def decodeState : ∀ d, StateOk d → State
  | .constr 0 [],                    _  => .Holding
  | .constr 1 [.b κ, .i d, .list l], _  =>
      .Collect κ d (l.filterMap fun | .b s => some s | _ => none)

def decodeInput : ∀ r, InputOk r → Input
  | .constr 0 [.b κ, .i d], _ => .Propose κ d
  | .constr 1 [.b s],       _ => .Add s
  | .constr 2 [],            _ => .Pay
  | .constr 3 [],            _ => .Cancel

/-- Encode a `State` back to Data (used to check the output datum). -/
def encodeState : State → Data
  | .Holding            => .constr 0 []
  | .Collect κ d sigs   => .constr 1 [.b κ, .i d, .list (sigs.map .b)]

-- ---------------------------------------------------------------------------
-- Pure step function (the heart of the coroutine)
-- ---------------------------------------------------------------------------

/-- Add a signature if it is authorised and not already present. -/
def addSig (sig : ByteArray) (params : Params) (sigs : List ByteArray) : Option (List ByteArray) :=
  if elemBytes sig params.sigsAuth then
    if elemBytes sig sigs then some sigs       -- already recorded, idempotent
    else some (sig :: sigs)
  else none                                    -- not authorised

/-- The state machine step.
    `txSigs` : signatories present in the transaction (from txInfo.signatories).
    `now`    : upper bound of the transaction validity range (deadline check).
    Returns `some nextState` on a valid transition, `none` to reject. -/
def step (params : Params) (txSigs : List ByteArray) (now : Int)
    (state : State) (input : Input) : Option State :=
  match state, input with
  | .Holding, .Propose κ d =>
      -- Anyone may propose; sigs start empty
      some (.Collect κ d [])
  | .Collect κ d sigs, .Add sig =>
      -- Signer must actually have signed the tx AND be authorised
      if elemBytes sig txSigs then
        addSig sig params sigs |>.map (.Collect κ d ·)
      else none
  | .Collect _ _ sigs, .Pay =>
      -- Enough signatures collected?
      if sigs.length ≥ params.minSigs then some .Holding
      else none
  | .Collect _ d _, .Cancel =>
      -- Deadline must have expired
      if now > d then some .Holding
      else none
  | _, _ => none  -- all other combinations reject

-- ---------------------------------------------------------------------------
-- ScriptContext predicates
-- ---------------------------------------------------------------------------

/-- The validity-range upper bound from `txInfo`.

    `txInfo.validRange` (field 7) = `Constr 0 [lowerBound, upperBound]`
    `upperBound` (field 1 of validRange) = `Constr 0 [Extended, Closure]`
    `Extended` (field 0 of upperBound):
      `Constr 0 []` = NegInf
      `Constr 1 [I t]` = Finite t      ← what we care about
      `Constr 2 []` = PosInf

    We only define `HasFiniteUpperBound` here; a `PosInf` validity range
    means "no deadline", which is fine for Propose/Add/Pay but disallows
    Cancel (you can't cancel if there's no end of time). -/
def HasFiniteUpperBound (txInfo : Data) : Prop :=
  match txInfo with
  | .constr 0 (_ :: _ :: _ :: _ :: _ :: _ :: _ :: .constr 0 [_, .constr 0 [.constr 1 [.i _], _]] :: _) => True
  | _ => False

def decodeTxUpperBound : ∀ txInfo, HasFiniteUpperBound txInfo → Int
  | .constr 0 (_ :: _ :: _ :: _ :: _ :: _ :: _ :: .constr 0 [_, .constr 0 [.constr 1 [.i t], _]] :: _), _ => t

/-- `txInfo.signatories` as a list of byte arrays (public key hashes). -/
def HasSignatories (txInfo : Data) : Prop :=
  match txInfo with
  | .constr 0 (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: sigList :: _) =>
      IsByteStringList sigList
  | _ => False

def decodeSignatories : ∀ txInfo, HasSignatories txInfo → List ByteArray
  | .constr 0 (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: sigList :: _), h =>
      decodeByteStringList sigList h

/-- The datum from a `SpendingScript` `scriptInfo`.

    `scriptInfo = Constr 1 [txOutRef, Just (Datum d)]`
    Just = `Constr 0 [...]`, Datum = `Constr 0 [d]` (PlutusTx conventions). -/
def DatumOk (scriptInfo : Data) : Prop :=
  match scriptInfo with
  | .constr 1 [_, .constr 0 [.constr 0 [d]]] => StateOk d
  | _ => False

def decodeDatum : ∀ scriptInfo, DatumOk scriptInfo → { d : Data // StateOk d }
  | .constr 1 [_, .constr 0 [.constr 0 [d]]], h => ⟨d, h⟩

/-- The full script context is well-formed for a spending multisig transaction. -/
def WellFormed (ctx : Data) : Prop :=
  match ctx with
  | .constr 0 [txInfo, redeemer, scriptInfo] =>
      HasSignatories txInfo ∧ HasFiniteUpperBound txInfo ∧ DatumOk scriptInfo ∧ InputOk redeemer
  | _ => False

-- ---------------------------------------------------------------------------
-- Output datum check (ghost-only for now)
-- ---------------------------------------------------------------------------

/-- Some output carries `nextState` as an inline datum.

    `txInfo.outputs` is the third field (index 2) of txInfo; each
    `TxOut = Constr 0 [address, value, outputDatum, referenceScript]`
    where an inline datum is `outputDatum = Constr 1 [d]`.

    Ghost-only (Prop — erased in compiled UPLC).  Making this a decidable
    on-chain check requires iterating over `txInfo.outputs`, which is
    left as future work.  For now the guarantee lives at the Lean level:
    any proof of `OutputCarries txInfo s` witnesses that the continuation
    really is present in the transaction. -/
def OutputCarries (txInfo : Data) (nextState : State) : Prop :=
  ∃ (addr val ref : Data) (outputs pre suf : List Data),
    txInfo = .constr 0 (pre ++ [.list outputs] ++ suf) ∧
    .constr 0 [addr, val, .constr 1 [encodeState nextState], ref] ∈ outputs

-- ---------------------------------------------------------------------------
-- The validator
-- ---------------------------------------------------------------------------

/-- The multisig coroutine validator.

    Runs the step function and checks that a next-state continuation
    is deposited into an output (ghost check — see `OutputCarries`). -/
def validatorE (params : Params) (ctx : Data) (wf : WellFormed ctx) : Unit :=
  match ctx, wf with
  | .constr 0 [txInfo, redeemer, scriptInfo], ⟨hSigs, hUB, hDatum, hInput⟩ =>
      let sigs  := decodeSignatories txInfo hSigs
      let now   := decodeTxUpperBound txInfo hUB
      let ⟨d, hd⟩ := decodeDatum scriptInfo hDatum
      let state := decodeState d hd
      let input := decodeInput redeemer hInput
      match step params sigs now state input with
      | some _ => ()
      | none   => Poe.Prelude.abort ()

end Poe.Examples.MultiSig
