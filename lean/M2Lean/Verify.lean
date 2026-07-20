/-
M2Lean: the verification driver.

Maps validated protocol claims onto the executable checkers and
produces a verification report (SPEC §5).  Claims are checked in the
coefficient field their ring declares: `ℚ` for `RationalField`
documents and `ZMod p` for `PrimeField p` documents (the parser
stores prime-field residues as integer rationals; `convPoly`
re-interprets them, rejecting non-residues).  The assurance level
attached to each accepted claim records whether the checker has a
kernel-checked soundness theorem (`proved`) or is executable-complete
with its soundness cited but not yet formalized (`checked`) — see
SPEC §6 and docs/trust-model.md.
-/
import Lean.Data.Json
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod
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

/-! ## Coefficient conversion

The parser stores every coefficient as `ℚ`.  A `Conv α` interprets
those rationals in the declared coefficient field; for `ZMod p` it
requires canonical residues (denominator 1, value in `[0, p)`). -/

structure Conv (α : Type) where
  coeff : Rat → Except String α

def Conv.rat : Conv Rat := ⟨.ok⟩

def Conv.zmod (p : Nat) : Conv (ZMod p) :=
  ⟨fun q =>
    if q.den ≠ 1 then .error s!"coefficient {q} is not an integer residue"
    else if q.num < 0 || q.num ≥ (p : Int) then
      .error s!"residue {q.num} out of range [0, {p})"
    else .ok ((q.num : Int) : ZMod p)⟩

variable {α : Type} [Field α] [DecidableEq α]

def Conv.poly (cv : Conv α) (p : SPoly Rat) : Except String (SPoly α) :=
  p.mapM fun t => do return ⟨← cv.coeff t.coeff, t.exps⟩

def Conv.polys (cv : Conv α) (ps : List (SPoly Rat)) : Except String (List (SPoly α)) :=
  ps.mapM cv.poly

def Conv.rows (cv : Conv α) (rs : List (List (SPoly Rat))) :
    Except String (List (List (SPoly α))) :=
  rs.mapM cv.polys

def Conv.mat (cv : Conv α) (M : SMatrix Rat) : Except String (SMatrix α) :=
  cv.rows M

def Conv.spair (cv : Conv α) (sp : SPairCert Rat) : Except String (SPairCert α) := do
  return ⟨sp.i, sp.j, ← cv.polys sp.quotients⟩

/-! ## Generic claim runner -/

/-- Run one claim's checker in the coefficient field `α`.
`gbLevel` is the assurance level currently carried by Gröbner-backed
claims (see `Certificates.Soundness` / `GroebnerSound`). -/
def runClaimIn (cv : Conv α) (d : Document) (c : PClaim) : ClaimResult :=
  let convErr := fun (e : String) => reject c s!"structural: {e}"
  match c.data with
  | .polyIdentity _ lhs rhs =>
    match cv.poly lhs, cv.poly rhs with
    | .ok l, .ok r => verdict c "proved" (checkIdentity l r)
        "lhs and rhs normalize to different canonical forms"
        "polynomial identity holds"
    | .error e, _ | _, .error e => convErr e
  | .membership iid f cofs =>
    match d.find? iid with
    | some (.ideal _ gens) =>
      match cv.poly f, cv.polys gens, cv.polys cofs with
      | .ok f', .ok gens', .ok cofs' =>
        verdict c "proved" (checkMembership f' gens' cofs')
          "cofactor combination does not equal the element"
          "element lies in the ideal"
      | .error e, _, _ | _, .error e, _ | _, _, .error e => convErr e
    | _ => reject c s!"structural: '{iid}' is not an Ideal"
  | .spanInclusion src tgt rows =>
    match d.find? src, d.find? tgt with
    | some (.ideal _ sgens), some (.ideal _ tgens) =>
      match cv.polys sgens, cv.polys tgens, cv.rows rows with
      | .ok s', .ok t', .ok rows' =>
        verdict c "proved" (checkSpanInclusion s' t' rows')
          "some source generator is not certified inside the target span"
          "source ideal is contained in target ideal"
      | .error e, _, _ | _, .error e, _ | _, _, .error e => convErr e
    | _, _ => reject c "structural: source/target must be Ideals"
  | .groebner iid basis bc gc sps =>
    match d.find? iid, d.ringInfo? (match d.find? iid with
        | some (.ideal r _) => r | _ => "") with
    | some (.ideal _ gens), some (arity, ord, _) =>
      match cv.polys gens, cv.polys basis, cv.rows bc, cv.rows gc,
            sps.mapM cv.spair with
      | .ok gens', .ok basis', .ok bc', .ok gc', .ok sps' =>
        verdict c GroebnerSound.level
          (checkGroebner arity ord gens' basis' bc' gc' sps')
          "Buchberger evidence failed (span, S-pair reduction, or lm bound)"
          GroebnerSound.acceptMessage
      | .error e, _, _, _, _ | _, .error e, _, _, _ | _, _, .error e, _, _
      | _, _, _, .error e, _ | _, _, _, _, .error e => convErr e
    | _, _ => reject c s!"structural: '{iid}' is not an Ideal with a ring"
  | .nonMembership iid gbId f quots rem =>
    -- sound only relative to an accepted Gröbner claim for the same
    -- ideal: locate it, re-run its checker, then check the division data
    match d.claims.find? (fun c' => c'.id == gbId) with
    | some ⟨_, .groebner iid' basis bc gc sps⟩ =>
      if iid' ≠ iid then reject c "structural: Gröbner claim is for a different ideal"
      else
        match d.find? iid, d.ringInfo? (match d.find? iid with
            | some (.ideal r _) => r | _ => "") with
        | some (.ideal _ gens), some (arity, ord, _) =>
          match cv.polys gens, cv.polys basis, cv.rows bc, cv.rows gc,
                sps.mapM cv.spair, cv.poly f, cv.polys quots, cv.poly rem with
          | .ok gens', .ok basis', .ok bc', .ok gc', .ok sps', .ok f',
            .ok quots', .ok rem' =>
            verdict c GroebnerSound.level
              (checkGroebner arity ord gens' basis' bc' gc' sps' &&
               checkNonMembership arity ord basis' f' quots' rem')
              "division data failed (identity, zero remainder, or reducibility)"
              s!"element is NOT in the ideal ({GroebnerSound.level} via Gröbner claim '{gbId}')"
          | _, _, _, _, _, _, _, _ => convErr "coefficient conversion failed"
        | _, _ => reject c s!"structural: '{iid}' is not an Ideal with a ring"
    | some _ => reject c s!"structural: '{gbId}' is not a GroebnerBasis claim"
    | none => reject c s!"structural: no claim '{gbId}' in this document"
  | .chainComplex _ dids => Id.run do
    let mut mats : List (Nat × Nat × SMatrix α) := []
    for did in dids do
      match d.find? did with
      | some (.matrix _ r cl e) =>
        match cv.mat e with
        | .ok e' => mats := mats ++ [(r, cl, e')]
        | .error e => return convErr e
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
  | .gradedComplex _ mids dids => Id.run do
    let mut degs : List (List Int) := []
    for mid in mids do
      match d.find? mid with
      | some (.freeModule _ ds) => degs := degs ++ [ds]
      | _ => return reject c s!"structural: '{mid}' is not a GradedFreeModule"
    let mut mats : List (SMatrix α) := []
    for did in dids do
      match d.find? did with
      | some (.matrix _ _ _ e) =>
        match cv.mat e with
        | .ok e' => mats := mats ++ [e']
        | .error e => return convErr e
      | _ => return reject c s!"structural: '{did}' is not a Matrix"
    return verdict c "checked" (checkGradedComplex degs mats)
      "grading or composition check failed"
      "graded complex verified from certificate (graded soundness theorem pending)"

/-! ## Domain dispatch -/

/-- The coefficient domain of the ring a claim lives in. -/
def claimRing (d : Document) (c : PClaim) : Option String :=
  match c.data with
  | .polyIdentity rid .. | .chainComplex rid .. | .gradedComplex rid .. => some rid
  | .membership iid .. | .groebner iid .. | .nonMembership iid .. =>
    match d.find? iid with
    | some (.ideal rid _) => some rid
    | _ => none
  | .spanInclusion src .. =>
    match d.find? src with
    | some (.ideal rid _) => some rid
    | _ => none

def runClaim (d : Document) (c : PClaim) : ClaimResult :=
  match claimRing d c with
  | none => reject c "structural: claim does not resolve to a ring"
  | some rid =>
    match d.ringInfo? rid with
    | none => reject c s!"structural: '{rid}' is not a PolynomialRing"
    | some (_, _, coeff) =>
      match d.find? coeff with
      | some .ratField => runClaimIn Conv.rat d c
      | some (.primeField p) =>
        if hp : p.Prime then
          haveI : Fact p.Prime := ⟨hp⟩
          runClaimIn (Conv.zmod p) d c
        else
          reject c s!"structural: characteristic {p} is not prime"
      | _ => reject c s!"structural: dangling coefficient reference '{coeff}'"

def runDocument (d : Document) : List ClaimResult :=
  d.claims.map (runClaim d)

def report (d : Document) (results : List ClaimResult) : Json :=
  Json.mkObj [
    ("m2leanVersion", Json.str "0.2.0"),
    ("documentId", Json.str (d.documentId ++ "-report")),
    ("reportFor", Json.str d.documentId),
    ("results", Json.arr (results.map (·.toJson)).toArray),
    ("provenance", Json.mkObj [
      ("producer", Json.str "m2lean-check (Lean 4)"),
      ("packageVersion", Json.str "0.2.0")])]

end M2Lean
