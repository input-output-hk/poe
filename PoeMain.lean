/-!
# poe — command-line compiler

Compiles a `.poem` file (a Lean source file using the Poe library) to UPLC or TPLC.

Usage:
  poe <file.poem> -o <output> [-d <declName>] [--tplc]

The `.poem` file is a Lean source file.  It may import Poe modules.  The CLI
prepends `import Poe.Reflect` and appends a `poe`/`poe_tplc` command, then
elaborates the resulting file using the `lean` binary so that the elaborator
command runs as a side effect and writes the output.

Example (validator.poem):
  import Poe.Prelude

  def validatorE (datum redeemer ctx : Poe.Prelude.Data) : Unit :=
    if datum == redeemer then () else Poe.Prelude.abort ()
-/

structure CliArgs where
  inputFile  : String := ""
  outputFile : String := ""
  declName   : String := "validatorE"
  tplc       : Bool   := false

def usage : String :=
  "Usage: poe <file.poem> -o <output> [-d <declName>] [--tplc]\n" ++
  "  -o <file>     output file (required)\n" ++
  "  -d <name>     declaration to compile (default: validatorE)\n" ++
  "  --tplc        emit Typed PLC instead of UPLC"

def parseArgs (args : List String) : Except String CliArgs :=
  let rec go : List String → CliArgs → Except String CliArgs
    | [], acc => pure acc
    | "-o" :: out :: rest, acc => go rest { acc with outputFile := out }
    | "-d" :: d :: rest,   acc => go rest { acc with declName := d }
    | "--tplc" :: rest,    acc => go rest { acc with tplc := true }
    | ("-h" :: _),         _   => .error usage
    | ("--help" :: _),     _   => .error usage
    | f :: rest, acc =>
      if acc.inputFile.isEmpty then go rest { acc with inputFile := f }
      else .error s!"unexpected argument: {f}"
  go args {}

def main (args : List String) : IO Unit := do
  let cli ← match parseArgs args with
    | .error msg => IO.eprintln msg; return
    | .ok cli    => pure cli
  if cli.inputFile.isEmpty || cli.outputFile.isEmpty then
    IO.eprintln usage; return
  -- Resolve the output path to an absolute path so the elaborator can write it
  -- regardless of where lean changes cwd.
  let cwd ← IO.currentDir
  let outputAbs :=
    if cli.outputFile.startsWith "/" then cli.outputFile
    else (cwd / cli.outputFile).toString
  -- Read the .poem source
  let poemSrc ← IO.FS.readFile cli.inputFile
  -- Build a wrapper that:
  --   1. Imports Poe.Reflect (registers the `poe`/`poe_tplc` elaborator commands)
  --   2. Re-emits the .poem content (its own imports + declarations)
  --   3. Runs the appropriate elaborator command to write the output
  let cmd := if cli.tplc then "poe_tplc" else "poe"
  let wrapper :=
    "import Poe.Reflect\n" ++
    poemSrc ++ "\n" ++
    s!"{cmd} \"{outputAbs}\" := {cli.declName}\n"
  -- Write the wrapper alongside the output so relative imports resolve correctly
  let tmpFile := outputAbs ++ ".__poe_tmp.lean"
  IO.FS.writeFile tmpFile wrapper
  -- Find the lean binary from LEAN_SYSROOT env (set by lake) or fall back to PATH
  let leanBin ←
    if let some sysroot ← IO.getEnv "LEAN_SYSROOT" then
      pure s!"{sysroot}/bin/lean"
    else
      pure "lean"
  -- Elaborate the wrapper (not --run: we want elaborator side-effects, not main)
  let leanPath ← IO.getEnv "LEAN_PATH"
  let result ← IO.Process.output {
    cmd  := leanBin
    args := #[tmpFile]
    env  := leanPath.map (fun p => #[("LEAN_PATH", some p)]) |>.getD #[]
  }
  try IO.FS.removeFile tmpFile catch _ => pure ()
  try IO.FS.removeFile (tmpFile ++ ".olean") catch _ => pure ()
  try IO.FS.removeFile (tmpFile ++ ".ilean") catch _ => pure ()
  if result.exitCode != 0 then
    IO.eprint result.stderr
    IO.Process.exit 1
  IO.println s!"Wrote {cli.outputFile}"
