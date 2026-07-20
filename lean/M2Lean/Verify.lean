/-
M2Lean: the verification driver.

Maps validated protocol claims onto the executable checkers and
produces a verification report (SPEC §5).  The assurance level
attached to each accepted claim records whether the checker has a
kernel-checked soundness theorem (`proved`) or is executable-complete
with its mathematical soundness cited but not yet formalized
(`checked`) — see SPEC §6 and docs/trust-model.md.
-/
import Lean.Data.Json
import M2Lean.Protocol.Ast

namespace M2Lean

open Lean (Json)

structure ClaimResult where
  claim : String
  accepted : Bool
  assurance : String
  message : String
  deriving Repr

def ClaimResult.toJson (r : ClaimResult) : Json :=
  Json.mkObj [
    ("claim", Json.str r.claim),
    ("status", Json.str (if r.accepted then "accepted" else "rejected")),
    ("assurance", Json.str (if r.accepted then r.assurance else "none")),
    ("message", Json.str r.message)]

private def reject (c : PClaim) (msg : String) : ClaimResult :=
  ⟨c.id, false, "none", msg⟩

private def verdict (c : PClaim) (level : String) (ok : Bool) (failMsg : String)
    (okMsg : String := "") : ClaimResult :=
  if ok then ⟨c.id, true, level, okMsg⟩ else reject c s!"verification: {failMsg}"

/-- Rings over prime fields parse and validate, but their claims are
not yet checkable in the Lean semantics (ADR 0002). -/
private def ratRingOnly (d : Document) (rid : String) : Option String :=
  match d.ringInfo? rid with
  | none => some s!"structural: '{rid}' is not a PolynomialRing"
  | some (_, _, coeff) =>
    match d.find? coeff with
    | some .ratField => none
    | some (.primeField p) =>
      some s!"unsupported: checking over GF({p}) is not yet implemented (ADR 0002)"
    | _ => some s!"structural: dangling coefficient reference '{coeff}'"

def runClaim (d : Document) (c : PClaim) : ClaimResult :=
  match c.data with
  | .polyIdentity rid lhs rhs =>
    match ratRingOnly d rid with
    | some m => reject c m
    | none => verdict c "proved" (checkIdentity lhs rhs)
        "lhs and rhs normalize to different canonical forms"
        "polynomial identity holds"
  | .membership iid f cofs =>
    match d.find? iid with
    | some (.ideal rid gens) =>
      match ratRingOnly d rid with
      | some m => reject c m
      | none => verdict c "proved" (checkMembership f gens cofs)
          "cofactor combination does not equal the element"
          "element lies in the ideal"
    | _ => reject c s!"structural: '{iid}' is not an Ideal"
  | .spanInclusion src tgt rows =>
    match d.find? src, d.find? tgt with
    | some (.ideal rid sgens), some (.ideal _ tgens) =>
      match ratRingOnly d rid with
      | some m => reject c m
      | none => verdict c "proved" (checkSpanInclusion sgens tgens rows)
          "some source generator is not certified inside the target span"
          "source ideal is contained in target ideal"
    | _, _ => reject c "structural: source/target must be Ideals"
  | .groebner iid basis bc gc sps =>
    match d.find? iid with
    | some (.ideal rid gens) =>
      match ratRingOnly d rid, d.ringInfo? rid with
      | some m, _ => reject c m
      | none, some (_, ord, _) =>
        verdict c "checked" (checkGroebner ord gens basis bc gc sps)
          "Buchberger evidence failed (span, S-pair reduction, or lm bound)"
          "Buchberger criterion verified from certificate (soundness theorem pending)"
      | none, none => reject c "structural: ring not found"
    | _ => reject c s!"structural: '{iid}' is not an Ideal"
  | .chainComplex rid dids =>
    match ratRingOnly d rid with
    | some m => reject c m
    | none => Id.run do
      let mut mats : List (Nat × Nat × SMatrix) := []
      for did in dids do
        match d.find? did with
        | some (.matrix _ r cl e) => mats := mats ++ [(r, cl, e)]
        | _ => return reject c s!"structural: '{did}' is not a Matrix"
      let mut ok := true
      let mut msg := ""
      for k in [0 : mats.length - 1] do
        let (r, m₁, A) := mats[k]!
        let (m₂, cc, B) := mats[k+1]!
        if m₁ ≠ m₂ then
          ok := false
          msg := s!"dimension mismatch between differentials {k} and {k+1}"
        else if !checkComplexPair r m₁ cc A B then
          ok := false
          msg := s!"differentials {k} and {k+1} do not compose to zero"
      return verdict c "proved" ok msg "consecutive differentials compose to zero"
  | .gradedComplex rid mids dids =>
    match ratRingOnly d rid with
    | some m => reject c m
    | none => Id.run do
      let mut degs : List (List Int) := []
      for mid in mids do
        match d.find? mid with
        | some (.freeModule _ ds) => degs := degs ++ [ds]
        | _ => return reject c s!"structural: '{mid}' is not a GradedFreeModule"
      let mut mats : List SMatrix := []
      for did in dids do
        match d.find? did with
        | some (.matrix _ _ _ e) => mats := mats ++ [e]
        | _ => return reject c s!"structural: '{did}' is not a Matrix"
      return verdict c "checked" (checkGradedComplex degs mats)
        "grading or composition check failed"
        "graded complex verified from certificate (graded soundness theorem pending)"

def runDocument (d : Document) : List ClaimResult :=
  d.claims.map (runClaim d)

def report (d : Document) (results : List ClaimResult) : Json :=
  Json.mkObj [
    ("m2leanVersion", Json.str "0.1.0"),
    ("documentId", Json.str (d.documentId ++ "-report")),
    ("reportFor", Json.str d.documentId),
    ("results", Json.arr (results.map (·.toJson)).toArray),
    ("provenance", Json.mkObj [
      ("producer", Json.str "m2lean-check (Lean 4)"),
      ("packageVersion", Json.str "0.1.0")])]

end M2Lean
