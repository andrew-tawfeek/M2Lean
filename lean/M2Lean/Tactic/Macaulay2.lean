/-
M2Lean: the `macaulay2` tactic (prototype).

Discharges goals of the form

  `toMv n f ∈ spanOf n gs`

(over ℚ, with `f`, `gs` ground sparse data) by:

1. evaluating the goal's sparse data,
2. writing a Macaulay2 session that asks `membershipClaim` for
   cofactors and exports a protocol document,
3. running `M2 --script` as a subprocess,
4. parsing the returned document with the M2Lean parser,
5. embedding the cofactors as literals and closing the goal with
   `checkMembership_sound` applied to a *kernel-checked* run of the
   certificate checker (`Lean.Meta.mkDecideProof`).

Trust: exactly as everywhere else in M2Lean, the M2 output is
untrusted; a wrong or corrupted answer makes the final `decide` proof
fail, never a false theorem.  Requires `M2` on `PATH` and the
`M2LEAN_HOME` environment variable pointing at the repository root, or a
Lake dependency checkout containing `m2/M2Lean.m2`.
-/
import Mathlib
import M2Lean.Certificates.Soundness
import M2Lean.Protocol.Ast

open Lean Meta Elab Tactic

namespace M2Lean.Tactic

/-! ### Expression construction for sparse data -/

private def ratToExpr (q : ℚ) : Expr :=
  mkApp2 (mkConst ``mkRat) (toExpr q.num) (toExpr q.den)

private instance : ToExpr ℚ where
  toExpr := ratToExpr
  toTypeExpr := mkConst ``Rat

private instance : ToExpr (STerm ℚ) where
  toExpr t := mkApp3 (mkConst ``STerm.mk [.zero]) (mkConst ``Rat)
    (ratToExpr t.coeff) (toExpr t.exps)
  toTypeExpr := mkApp (mkConst ``STerm [.zero]) (mkConst ``Rat)

private def polysToExpr (ps : List (SPoly ℚ)) : Expr := toExpr ps

/-! ### Evaluation of the goal's data -/

private unsafe def evalSPolyUnsafe (e : Expr) : MetaM (SPoly ℚ) :=
  evalExprCore (SPoly ℚ) e (fun _ => pure ())

@[implemented_by evalSPolyUnsafe]
private opaque evalSPoly (e : Expr) : MetaM (SPoly ℚ)

private unsafe def evalSPolysUnsafe (e : Expr) : MetaM (List (SPoly ℚ)) :=
  evalExprCore (List (SPoly ℚ)) e (fun _ => pure ())

@[implemented_by evalSPolysUnsafe]
private opaque evalSPolys (e : Expr) : MetaM (List (SPoly ℚ))

private unsafe def evalNatUnsafe (e : Expr) : MetaM ℕ :=
  evalExprCore ℕ e (fun _ => pure ())

@[implemented_by evalNatUnsafe]
private opaque evalNat (e : Expr) : MetaM ℕ

/-! ### Macaulay2 session generation -/

private def m2Poly (n : ℕ) (p : SPoly ℚ) : String :=
  if p.isEmpty then "0_R" else
  String.intercalate " + " <| p.map fun t =>
    let mono := String.intercalate "*" <|
      (List.range n).filterMap fun i =>
        let e := t.exps.getD i 0
        if e = 0 then none else some s!"x_{i}^{e}"
    let c := s!"({t.coeff.num}/{t.coeff.den})"
    if mono.isEmpty then c else s!"{c}*{mono}"

private def m2Script (pkg : String) (n : ℕ) (f : SPoly ℚ)
    (gs : List (SPoly ℚ)) (out : String) : String :=
  String.intercalate "\n" [
    s!"loadPackage(\"M2Lean\", FileName => \"{pkg}\");",
    s!"R = QQ[x_0..x_{n-1}];",
    s!"I = ideal \{{String.intercalate ", " (gs.map (m2Poly n))}};",
    "D = newM2LeanDocument \"tactic-request\";",
    s!"membershipClaim(D, \"m\", {m2Poly n f}, I);",
    s!"writeM2LeanDocument(D, \"{out}\");",
    ""]

private def parentN : Nat → System.FilePath → Option System.FilePath
  | 0, path => some path
  | n + 1, path => path.parent.bind (parentN n)

/-- Locate the Macaulay2 package in either the source checkout selected by
`M2LEAN_HOME` or this package's own Lake dependency checkout.  A compiled Lean
module lives below `<package>/.lake/build/lib/lean`, so entries in `LEAN_PATH`
provide a stable, package-manager-independent route back to the package root. -/
private def findM2Package : TacticM String := do
  let explicitRoots :=
    match ← IO.getEnv "M2LEAN_HOME" with
    | some home => [System.FilePath.mk home]
    | none => []
  let dependencyRoots :=
    match ← IO.getEnv "LEAN_PATH" with
    | some path => (System.SearchPath.parse path).filterMap (parentN 4)
    | none => []
  for root in explicitRoots ++ dependencyRoots do
    let packageFile := root / "m2" / "M2Lean.m2"
    if ← packageFile.pathExists then
      return packageFile.toString
  throwError "macaulay2: cannot locate m2/M2Lean.m2; set M2LEAN_HOME to the M2Lean package root"

/-- Ask Macaulay2 for membership cofactors; returns them as parsed
sparse polynomials. -/
private def askMacaulay2 (n : ℕ) (f : SPoly ℚ) (gs : List (SPoly ℚ)) :
    TacticM (List (SPoly ℚ)) := do
  let pkg ← findM2Package
  let dir ← IO.Process.run { cmd := "mktemp", args := #["-d"] }
  let dir := dir.trimAscii.copy
  let scriptPath := s!"{dir}/request.m2"
  let outPath := s!"{dir}/answer.json"
  IO.FS.writeFile scriptPath (m2Script pkg n f gs outPath)
  let r ← IO.Process.output { cmd := "M2", args := #["--script", scriptPath] }
  if r.exitCode ≠ 0 then
    throwError "macaulay2: M2 failed (exit {r.exitCode}):\n{r.stderr}"
  let raw ← IO.FS.readFile outPath
  match parseDocument raw with
  | .error e => throwError "macaulay2: cannot parse M2 answer: {e}"
  | .ok doc =>
    match doc.claims.find? (·.id == "m") with
    | some ⟨_, .membership _ _ cofs⟩ => return cofs
    | _ => throwError "macaulay2: M2 answer contains no membership claim"

/-! ### The tactic -/

/-- Close a goal `toMv n f ∈ spanOf n gs` (over ℚ, ground data) by
delegating the cofactor search to Macaulay2 and kernel-checking the
returned certificate. -/
elab "macaulay2" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let fn := tgt.getAppFn
  let args := tgt.getAppArgs
  unless fn.isConstOf ``Membership.mem && args.size == 5 do
    throwError "macaulay2: goal is not a membership `toMv n f ∈ spanOf n gs`"
  let spanSet := args[3]!
  let elem := args[4]!
  unless spanSet.getAppFn.isConstOf ``M2Lean.spanOf &&
      elem.getAppFn.isConstOf ``M2Lean.toMv do
    throwError "macaulay2: goal is not of the form `toMv n f ∈ spanOf n gs`"
  let spanArgs := spanSet.getAppArgs
  let elemArgs := elem.getAppArgs
  -- spanOf (α) [Field α] (n) (gs); toMv (α) [CommRing α] (n) (p)
  let nE := spanArgs[2]!
  let gsE := spanArgs[3]!
  let fE := elemArgs[3]!
  let n ← evalNat nE
  let f ← evalSPoly fE
  let gs ← evalSPolys gsE
  let cofs ← askMacaulay2 n f gs
  let csE := polysToExpr cofs
  -- build `checkMembership f gs cs = true` and its kernel decide proof
  let checkE ← mkAppM ``M2Lean.checkMembership #[fE, gsE, csE]
  let propE ← mkEq checkE (toExpr true)
  let decideProof ← mkDecideProof propE
  let proof ← mkAppM ``M2Lean.checkMembership_sound #[nE, decideProof]
  goal.assign proof

end M2Lean.Tactic
