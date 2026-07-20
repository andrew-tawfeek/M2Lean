/-
M2Lean: protocol document AST, JSON decoding, and structural validation.

Parsing a document is not a proof (SPEC §5, architecture layer 2).
This file rejects malformed or non-canonical documents with error
messages that carry paths into the source, and produces typed data
that the checkers of `Certificates.Checkers` consume.  Nothing here
is trusted for soundness: a bug can only cause wrongful rejection or
hand different (still checker-verified) data to the checkers.
-/
import Lean.Data.Json
import M2Lean.Protocol.Sparse
import M2Lean.Certificates.Checkers

namespace M2Lean

open Lean (Json)

/-! ## Typed protocol data -/

inductive Entry where
  | ratField
  | primeField (p : Nat)
  | polyRing (coeff : String) (vars : List String) (ord : MonOrder)
  | ideal (ring : String) (gens : List SPoly)
  | matrix (ring : String) (rows cols : Nat) (entries : SMatrix)
  | freeModule (ring : String) (degs : List Int)
  deriving Repr, Inhabited

inductive ClaimData where
  | polyIdentity (ring : String) (lhs rhs : SPoly)
  | membership (ideal : String) (element : SPoly) (cofactors : List SPoly)
  | spanInclusion (src tgt : String) (rows : List (List SPoly))
  | groebner (ideal : String) (basis : List SPoly)
      (basisCof genCof : List (List SPoly)) (sps : List SPairCert)
  | chainComplex (ring : String) (diffs : List String)
  | gradedComplex (ring : String) (modules : List String) (diffs : List String)
  deriving Repr, Inhabited

structure PClaim where
  id : String
  data : ClaimData
  deriving Repr, Inhabited

structure Document where
  documentId : String
  objects : List (String × Entry)
  claims : List PClaim
  provenance : Json
  deriving Inhabited

def Document.find? (d : Document) (id : String) : Option Entry :=
  (d.objects.find? (·.1 == id)).map (·.2)

/-! ## Decoding helpers (with source paths in error messages) -/

abbrev P := Except String

def ctx (path : String) : P α → P α
  | .ok a => .ok a
  | .error e => .error s!"{path}: {e}"

def getObj (j : Json) (k : String) (path : String) : P Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"{path}: missing field '{k}'"

def getStr (j : Json) (k : String) (path : String) : P String :=
  do (← getObj j k path).getStr?.mapError (s!"{path}.{k}: {·}")

def getArr (j : Json) (k : String) (path : String) : P (Array Json) :=
  do (← getObj j k path).getArr?.mapError (s!"{path}.{k}: {·}")

def getNatField (j : Json) (k : String) (path : String) : P Nat :=
  do (← getObj j k path).getNat?.mapError (s!"{path}.{k}: {·}")

/-- Canonical decimal integer strings (SPEC §2). -/
def parseCanonicalInt (s : String) (path : String) : P Int := do
  let body := if s.startsWith "-" then s.drop 1 else s
  if body.isEmpty || !body.all Char.isDigit then
    throw s!"{path}: '{s}' is not a decimal integer"
  if body.length > 1 && body.front == '0' then
    throw s!"{path}: leading zeros in '{s}'"
  if s == "-0" then throw s!"{path}: '-0' is not canonical"
  let n := body.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0
  return if s.startsWith "-" then -(n : Int) else (n : Int)

/-- Canonical rationals: positive denominator, reduced. -/
def parseRat (j : Json) (path : String) : P Rat := do
  let num ← parseCanonicalInt (← getStr j "num" path) s!"{path}.num"
  let den ← parseCanonicalInt (← getStr j "den" path) s!"{path}.den"
  if den ≤ 0 then throw s!"{path}: denominator must be positive"
  let q := mkRat num den.toNat
  -- canonicality: the reduced form must equal the transmitted form
  if q.num ≠ num || (q.den : Int) ≠ den then
    throw s!"{path}: {num}/{den} is not reduced"
  return q

def parseTerm (j : Json) (path : String) : P STerm := do
  let c ← parseRat (← getObj j "coefficient" path) s!"{path}.coefficient"
  let exps ← (← getArr j "exponents" path).toList.mapIdxM fun i e =>
    e.getNat?.mapError (s!"{path}.exponents[{i}]: {·}")
  return ⟨c, exps⟩

def parsePoly (j : Json) (path : String) : P SPoly := do
  (← getArr j "terms" path).toList.mapIdxM fun i t =>
    parseTerm t s!"{path}.terms[{i}]"

def parsePolyArr (j : Json) (k : String) (path : String) : P (List SPoly) := do
  (← getArr j k path).toList.mapIdxM fun i p => parsePoly p s!"{path}.{k}[{i}]"

def parseOrder (j : Json) (path : String) : P MonOrder := do
  match ← getStr j "kind" path with
  | "GRevLex" => return .grevlex
  | "Lex" => return .lex
  | o => throw s!"{path}: unsupported monomial order '{o}'"

def isPrime (p : Nat) : Bool :=
  p ≥ 2 && ((List.range p).drop 2).all (fun d => p % d ≠ 0)

/-! ## Object parsing -/

def parseEntry (j : Json) (path : String) (lookup : String → Option Entry) :
    P (String × Entry) := do
  let id ← getStr j "id" path
  let requireRing : String → P String := fun k => do
    let rid ← getStr j k path
    match lookup rid with
    | some (.polyRing ..) => return rid
    | some _ => throw s!"{path}.{k}: '{rid}' is not a PolynomialRing"
    | none => throw s!"{path}.{k}: unknown id '{rid}' (objects must be in dependency order)"
  match ← getStr j "kind" path with
  | "RationalField" => return (id, .ratField)
  | "PrimeField" => do
    let p ← parseCanonicalInt (← getStr j "characteristic" path) s!"{path}.characteristic"
    if p ≤ 0 || !isPrime p.toNat then
      throw s!"{path}.characteristic: {p} is not prime"
    return (id, .primeField p.toNat)
  | "PolynomialRing" => do
    let cid ← getStr j "coefficients" path
    match lookup cid with
    | some .ratField | some (.primeField _) => pure ()
    | some _ => throw s!"{path}.coefficients: '{cid}' is not a coefficient field"
    | none => throw s!"{path}.coefficients: unknown id '{cid}'"
    let vars ← (← getArr j "variables" path).toList.mapIdxM fun i v =>
      v.getStr?.mapError (s!"{path}.variables[{i}]: {·}")
    if vars.eraseDups.length ≠ vars.length then
      throw s!"{path}.variables: names must be pairwise distinct"
    let ord ← parseOrder (← getObj j "monomialOrder" path) s!"{path}.monomialOrder"
    return (id, .polyRing cid vars ord)
  | "Ideal" => do
    let rid ← requireRing "ring"
    let gens ← parsePolyArr j "generators" path
    return (id, .ideal rid gens)
  | "Matrix" => do
    let rid ← requireRing "ring"
    let rows ← getNatField j "rows" path
    let cols ← getNatField j "cols" path
    let entries ← (← getArr j "entries" path).toList.mapIdxM fun i r => do
      (← r.getArr?.mapError (s!"{path}.entries[{i}]: {·})")).toList.mapIdxM
        fun k p => parsePoly p s!"{path}.entries[{i}][{k}]"
    if entries.length ≠ rows || entries.any (·.length ≠ cols) then
      throw s!"{path}.entries: dimensions do not match rows={rows}, cols={cols}"
    return (id, .matrix rid rows cols entries)
  | "GradedFreeModule" => do
    let rid ← requireRing "ring"
    let degs ← (← getArr j "degrees" path).toList.mapIdxM fun i d =>
      d.getInt?.mapError (s!"{path}.degrees[{i}]: {·}")
    return (id, .freeModule rid degs)
  | k => throw s!"{path}: unknown object kind '{k}'"

/-! ## Claim parsing -/

def parseSPair (j : Json) (path : String) : P SPairCert := do
  return { i := ← getNatField j "i" path,
           j := ← getNatField j "j" path,
           quotients := ← parsePolyArr j "quotients" path }

def parseCofRows (j : Json) (k : String) (path : String) : P (List (List SPoly)) := do
  (← getArr j k path).toList.mapIdxM fun i r => do
    (← r.getArr?.mapError (s!"{path}.{k}[{i}]: {·}")).toList.mapIdxM
      fun l p => parsePoly p s!"{path}.{k}[{i}][{l}]"

def parseIdList (j : Json) (k : String) (path : String) : P (List String) := do
  (← getArr j k path).toList.mapIdxM fun i v =>
    v.getStr?.mapError (s!"{path}.{k}[{i}]: {·}")

def parseClaim (j : Json) (path : String) : P PClaim := do
  let id ← getStr j "id" path
  let ev ← getObj j "evidence" path
  let data ← match ← getStr j "kind" path with
  | "PolynomialIdentity" => do
    pure <| ClaimData.polyIdentity (← getStr j "ring" path)
      (← parsePoly (← getObj j "lhs" path) s!"{path}.lhs")
      (← parsePoly (← getObj j "rhs" path) s!"{path}.rhs")
  | "IdealMembership" => do
    pure <| ClaimData.membership (← getStr j "ideal" path)
      (← parsePoly (← getObj j "element" path) s!"{path}.element")
      (← parsePolyArr ev "cofactors" s!"{path}.evidence")
  | "SpanInclusion" => do
    pure <| ClaimData.spanInclusion (← getStr j "source" path)
      (← getStr j "target" path)
      (← parseCofRows ev "cofactorRows" s!"{path}.evidence")
  | "GroebnerBasis" => do
    let sps ← (← getArr ev "sPairs" s!"{path}.evidence").toList.mapIdxM
      fun i sp => parseSPair sp s!"{path}.evidence.sPairs[{i}]"
    pure <| ClaimData.groebner (← getStr j "ideal" path)
      (← parsePolyArr j "basis" path)
      (← parseCofRows ev "basisCofactors" s!"{path}.evidence")
      (← parseCofRows ev "generatorCofactors" s!"{path}.evidence")
      sps
  | "ChainComplex" => do
    pure <| ClaimData.chainComplex (← getStr j "ring" path)
      (← parseIdList j "differentials" path)
  | "GradedComplex" => do
    pure <| ClaimData.gradedComplex (← getStr j "ring" path)
      (← parseIdList j "modules" path)
      (← parseIdList j "differentials" path)
  | k => throw s!"{path}: unknown claim kind '{k}'"
  return ⟨id, data⟩

/-! ## Document parsing and structural validation -/

def parseDocument (s : String) : P Document := do
  let j ← match Json.parse s with
    | .ok j => pure j
    | .error e => throw s!"parse: {e}"
  let ver ← getStr j "m2leanVersion" "document"
  if ver ≠ "0.1.0" then throw s!"document.m2leanVersion: unsupported version '{ver}'"
  let docId ← getStr j "documentId" "document"
  let objJs ← getArr j "objects" "document"
  let mut objs : List (String × Entry) := []
  for h : i in [0 : objJs.size] do
    let lookup := fun id => (objs.find? (·.1 == id)).map (·.2)
    let (id, e) ← parseEntry objJs[i] s!"objects[{i}]" lookup
    if (objs.find? (·.1 == id)).isSome then
      throw s!"objects[{i}]: duplicate id '{id}'"
    objs := objs ++ [(id, e)]
  let claimJs ← getArr j "claims" "document"
  let claims ← claimJs.toList.mapIdxM fun i c => parseClaim c s!"claims[{i}]"
  let prov ← getObj j "provenance" "document"
  return { documentId := docId, objects := objs, claims := claims,
           provenance := prov }

/-- Arity and monomial order of the ring referenced (transitively) by
an object id, if it is ring-like. -/
def Document.ringInfo? (d : Document) (id : String) : Option (Nat × MonOrder × String) := do
  match ← d.find? id with
  | .polyRing coeff vars ord => some (vars.length, ord, coeff)
  | _ => none

/-- Structural validation beyond parsing: canonical forms, arities,
graded data (SPEC §3.4).  Returns an error message or `.ok`. -/
def validateDocument (d : Document) : P Unit := do
  let checkCanon := fun (rid : String) (what : String) (ps : List SPoly) => do
    match d.ringInfo? rid with
    | none => throw s!"{what}: '{rid}' is not a PolynomialRing"
    | some (arity, ord, coeff) => do
      if d.find? coeff |>.isNone then throw s!"{what}: dangling coefficient ref"
      for p in ps do
        if !isCanonical ord arity p then
          throw s!"{what}: polynomial is not canonical for the ring's order/arity"
  for (id, e) in d.objects do
    match e with
    | .ideal rid gens => checkCanon rid s!"object '{id}'" gens
    | .matrix rid _ _ entries => checkCanon rid s!"object '{id}'" entries.flatten
    | _ => pure ()
  for c in d.claims do
    match c.data with
    | .polyIdentity rid lhs rhs =>
      match d.ringInfo? rid with
      | none => throw s!"claim '{c.id}': '{rid}' is not a PolynomialRing"
      | some (arity, _, _) =>
        if !isRaw arity lhs || !isRaw arity rhs then
          throw s!"claim '{c.id}': raw polynomial has wrong arity"
    | .membership iid _ cofs =>
      match d.find? iid with
      | some (.ideal rid _) => checkCanon rid s!"claim '{c.id}'" cofs
      | _ => throw s!"claim '{c.id}': '{iid}' is not an Ideal"
    | .spanInclusion src tgt rows => do
      let ridOf := fun (x : String) => match d.find? x with
        | some (.ideal r _) => some r | _ => none
      match ridOf src, ridOf tgt with
      | some r1, some r2 =>
        if r1 ≠ r2 then throw s!"claim '{c.id}': ideals live in different rings"
        checkCanon r1 s!"claim '{c.id}'" rows.flatten
      | _, _ => throw s!"claim '{c.id}': source/target must be Ideals"
    | .groebner iid basis bc gc sps =>
      match d.find? iid with
      | some (.ideal rid _) => do
        checkCanon rid s!"claim '{c.id}'" basis
        checkCanon rid s!"claim '{c.id}'" (bc.flatten ++ gc.flatten)
        checkCanon rid s!"claim '{c.id}'" (sps.flatMap (·.quotients))
      | _ => throw s!"claim '{c.id}': '{iid}' is not an Ideal"
    | .chainComplex rid diffs =>
      for did in diffs do
        match d.find? did with
        | some (.matrix r _ _ _) =>
          if r ≠ rid then throw s!"claim '{c.id}': matrix '{did}' in wrong ring"
        | _ => throw s!"claim '{c.id}': '{did}' is not a Matrix"
    | .gradedComplex rid mods diffs => do
      for mid in mods do
        match d.find? mid with
        | some (.freeModule r _) =>
          if r ≠ rid then throw s!"claim '{c.id}': module '{mid}' in wrong ring"
        | _ => throw s!"claim '{c.id}': '{mid}' is not a GradedFreeModule"
      for did in diffs do
        match d.find? did with
        | some (.matrix r _ _ _) =>
          if r ≠ rid then throw s!"claim '{c.id}': matrix '{did}' in wrong ring"
        | _ => throw s!"claim '{c.id}': '{did}' is not a Matrix"

end M2Lean
