-- Import only the executable slice (parser, checkers, driver): the
-- soundness proofs are irrelevant at runtime and would drag the whole
-- of mathlib into native compilation.
import M2Lean.Verify

open M2Lean

/-- `m2lean-check FILE [-o REPORT]`: verify every claim in an M2Lean
protocol document.  Exit codes: 0 all claims accepted, 1 some claim
rejected, 2 parse/structural failure (the document itself is
rejected), 3 usage. -/
def main (args : List String) : IO UInt32 := do
  let (input?, out?) :=
    match args with
    | [f] => (some f, none)
    | [f, "-o", o] => (some f, some o)
    | _ => (none, none)
  let some input := input? |
    IO.eprintln "usage: m2lean-check FILE [-o REPORT]"
    return 3
  let raw ← IO.FS.readFile input
  match parseDocument raw with
  | .error e =>
    let cls := if e.startsWith "parse:" then "parse" else "structural"
    IO.eprintln s!"rejected ({cls}): {e}"
    return 2
  | .ok doc =>
    match validateDocument doc with
    | .error e =>
      IO.eprintln s!"rejected (structural): {e}"
      return 2
    | .ok () =>
      let results := runDocument doc
      let rep := (report doc results).pretty
      match out? with
      | some o => IO.FS.writeFile o (rep ++ "\n")
      | none => IO.println rep
      for r in results do
        let status := if r.accepted then "accepted" else "REJECTED"
        let level := if r.accepted then r.assurance else "none"
        IO.eprintln s!"{r.claim}: {status} [{level}] {r.message}"
      return (if results.all (·.accepted) then 0 else 1)
