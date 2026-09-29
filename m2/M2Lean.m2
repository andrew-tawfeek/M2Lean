-- M2Lean.m2 : Macaulay2 side of the M2Lean bridge.
--
-- Exports Macaulay2 objects and certificate-bearing claims as
-- M2Lean protocol documents (version 0.2.0, see protocol/SPEC.md).
-- Everything produced here is UNTRUSTED evidence: the Lean checkers
-- re-verify all identities.  Consequently this package may use any
-- convenient M2 machinery (internal Groebner bases, `//`) to
-- construct witnesses; only the S-pair quotients are produced by an
-- explicit division algorithm, because the protocol requires the
-- standard-representation leading-monomial bound to hold literally.

newPackage(
    "M2Lean",
    Version => "0.2.0",
    Date => "August 3, 2026",
    Authors => {{Name => "Andrew Tawfeek",
                 Email => "atawfeek.math@gmail.com",
                 HomePage => "https://github.com/andrew-tawfeek"}},
    HomePage => "https://github.com/andrew-tawfeek/M2Lean",
    Headline => "export certificates for verification in Lean 4",
    Keywords => {"Interfaces"}
    )

export {
    "newM2LeanDocument", "exportRing", "exportIdeal", "exportMatrix",
    "exportGradedFreeModule",
    "polynomialIdentityClaim", "membershipClaim", "unitIdealClaim",
    "spanInclusionClaim", "gbClaim", "chainComplexClaim",
    "gradedComplexClaim", "nonMembershipClaim",
    "writeM2LeanDocument", "divisionAlgorithm",
    "jsonOfPolynomial", "verifyWithLean"
    }

needsPackage "JSON"

----------------------------------------------------------------------
-- minimal deterministic JSON emitter
----------------------------------------------------------------------

jsonEscape = s -> concatenate for c in characters s list (
    if c === "\"" then "\\\"" else if c === "\\" then "\\\\" else c)

jstr = s -> "\"" | jsonEscape s | "\""
jarr = L -> "[" | demark(",", L) | "]"
-- ordered object from a list of ("key", jsonstring) pairs
jobj = L -> "{" | demark(",", for kv in L list (jstr kv#0 | ":" | kv#1)) | "}"
jint = n -> toString n

-- split compact JSON (as emitted above) into punctuation and atoms
jsonPunct = {"{", "}", "[", "]", ",", ":"}
jsonTokens = s -> (
    cs := characters s; n := #cs; toks := new MutableList; i := 0; j := 0;
    while i < n do (
        if cs#i === "\"" then (
            j = i + 1;
            while cs#j =!= "\"" do j = j + (if cs#j === "\\" then 2 else 1);
            toks#(#toks) = concatenate cs_{i..j}; i = j + 1)
        else if member(cs#i, jsonPunct) then (toks#(#toks) = cs#i; i = i + 1)
        else if cs#i === " " or cs#i === "\n" then i = i + 1
        else (
            j = i;
            while j < n and not member(cs#j, jsonPunct) and cs#j =!= " " do j = j + 1;
            toks#(#toks) = concatenate cs_{i..j-1}; i = j));
    toList toks)

-- indent compact JSON by `width` spaces, keeping key order; arrays of
-- scalars (e.g. exponent vectors) and empty containers stay on one line
jsonPretty = (s, width) -> (
    toks := jsonTokens s; out := new MutableList; depth := 0; i := 0; k := 0;
    pad := d -> "\n" | concatenate(d * width : " ");
    while i < #toks do (
        t := toks#i;
        if t === "{" and toks#(i+1) === "}" then (out#(#out) = "{}"; i = i + 2)
        else if t === "[" and (
            k = i + 1;
            while not member(toks#k, {"[", "{", "]"}) do k = k + 1;
            toks#k === "]") then (
            out#(#out) = concatenate for u in toks_{i..k} list (if u === "," then ", " else u);
            i = k + 1)
        else (
            out#(#out) = (
                if t === "{" or t === "[" then (depth = depth + 1; t | pad depth)
                else if t === "}" or t === "]" then (depth = depth - 1; pad depth | t)
                else if t === "," then "," | pad depth
                else if t === ":" then ": "
                else t);
            i = i + 1));
    concatenate toList out)

----------------------------------------------------------------------
-- polynomial encoding
----------------------------------------------------------------------

jsonOfCoefficient = c -> (
    -- c lies in QQ (possibly via ZZ) or a prime field ZZ/p
    K := ring c;
    if K === QQ or K === ZZ then (
        q := promote(c, QQ);
        jobj {("num", jstr toString numerator q),
              ("den", jstr toString denominator q)})
    else (
        -- prime field: canonical representative in [0, p)
        p := char K;
        r := lift(c, ZZ) % p;
        jstr toString r)
    )

-- terms of f in M2's order for its ring, which for the supported
-- GRevLex/Lex orders agrees with SPEC 3.5 (tested by shared fixtures)
jsonOfPolynomial = f -> (
    ts := terms f;
    jobj {("terms", jarr for t in ts list jobj {
        ("coefficient", jsonOfCoefficient leadCoefficient t),
        ("exponents", jarr (jint \ first exponents t))})}
    )

----------------------------------------------------------------------
-- documents
----------------------------------------------------------------------

M2LeanDocument = new Type of MutableHashTable

newM2LeanDocument = method()
newM2LeanDocument String := docId -> (
    D := new M2LeanDocument;
    D#"docId" = docId;
    D#"objects" = {};       -- list of json strings
    D#"claims" = {};        -- list of json strings
    D#"ids" = new MutableHashTable;   -- M2 object => protocol id
    D#"counter" = 0;
    D)

freshId = (D, prefix) -> (D#"counter" = D#"counter" + 1; prefix | toString D#"counter")

registered = (D, x) -> D#"ids"#?x

idOf = (D, x) -> (
    if not D#"ids"#?x then error "M2Lean: object not yet exported to this document";
    D#"ids"#x)

addObject = (D, x, id, json) -> (D#"ids"#x = id; D#"objects" = append(D#"objects", json); id)

addClaim = (D, json) -> (D#"claims" = append(D#"claims", json);)

----------------------------------------------------------------------
-- object export
----------------------------------------------------------------------

orderName = R -> (
    mo := (options monoid R).MonomialOrder;
    -- the monomial order option is a list like {MonomialSize=>32, GRevLex=>{1,..}, Position=>Up}
    names := for entry in toList mo list if instance(entry, Option) then toString entry#0 else toString entry;
    if member("GRevLex", names) then "GRevLex"
    else if member("Lex", names) then "Lex"
    else error "M2Lean: only GRevLex and Lex orders are supported by protocol 0.2.0")

exportRing = method()
exportRing (M2LeanDocument, Ring) := (D, R) -> (
    if registered(D, R) then return idOf(D, R);
    K := coefficientRing R;
    kid := if registered(D, K) then idOf(D, K) else (
        if K === QQ then (
            kid' := freshId(D, "k");
            addObject(D, K, kid', jobj {("id", jstr kid'), ("kind", jstr "RationalField")}))
        else if isField K and char K > 0 then (
            kid'' := freshId(D, "k");
            addObject(D, K, kid'', jobj {("id", jstr kid''), ("kind", jstr "PrimeField"),
                    ("characteristic", jstr toString char K)}))
        else error "M2Lean: coefficient ring must be QQ or a prime field");
    rid := freshId(D, "R");
    addObject(D, R, rid, jobj {
        ("id", jstr rid),
        ("kind", jstr "PolynomialRing"),
        ("coefficients", jstr kid),
        ("variables", jarr for v in gens R list jstr toString v),
        ("monomialOrder", jobj {("kind", jstr orderName R)})}))

exportIdeal = method()
exportIdeal (M2LeanDocument, Ideal) := (D, I) -> (
    if registered(D, I) then return idOf(D, I);
    rid := exportRing(D, ring I);
    iid := freshId(D, "I");
    addObject(D, I, iid, jobj {
        ("id", jstr iid),
        ("kind", jstr "Ideal"),
        ("ring", jstr rid),
        ("generators", jarr for g in first entries gens I list jsonOfPolynomial g)}))

exportMatrix = method()
exportMatrix (M2LeanDocument, Matrix) := (D, M) -> (
    if registered(D, M) then return idOf(D, M);
    rid := exportRing(D, ring M);
    mid := freshId(D, "d");
    addObject(D, M, mid, jobj {
        ("id", jstr mid),
        ("kind", jstr "Matrix"),
        ("ring", jstr rid),
        ("rows", jint numrows M),
        ("cols", jint numcols M),
        ("entries", jarr for i from 0 to numrows M - 1 list
            jarr for j from 0 to numcols M - 1 list jsonOfPolynomial M_(i,j))}))

-- a graded free module is exported from an explicit degree list
exportGradedFreeModule = method()
exportGradedFreeModule (M2LeanDocument, Ring, List) := (D, R, degs) -> (
    rid := exportRing(D, R);
    fid := freshId(D, "F");
    key := (R, degs, fid);  -- free modules with equal degrees are still distinct objects
    addObject(D, key, fid, jobj {
        ("id", jstr fid),
        ("kind", jstr "GradedFreeModule"),
        ("ring", jstr rid),
        ("degrees", jarr (jint \ degs))}))

----------------------------------------------------------------------
-- division algorithm with the standard-representation invariant
----------------------------------------------------------------------

-- divisionAlgorithm(f, B) returns (quotients, remainder) such that
--   f = sum_i quotients_i * B_i + remainder,
-- no term of the remainder is divisible by any lead term of B, and
-- every quotient satisfies  lm(quotients_i * B_i) <= lm(f)
-- in the ring's monomial order (each subtracted term is a lead term
-- of the running polynomial, which only decreases).
divisionAlgorithm = method()
divisionAlgorithm (RingElement, List) := (f, B) -> (
    R := ring f;
    p := f;
    r := 0_R;
    q := new MutableList from apply(#B, i -> 0_R);
    while p != 0 do (
        lt := leadTerm p;
        divided := false;
        i := 0;
        while i < #B and not divided do (
            ltB := leadTerm B#i;
            if lt % ltB == 0 then (
                c := lt // ltB;
                q#i = q#i + c;
                p = p - c * B#i;
                divided = true);
            i = i + 1);
        if not divided then (r = r + lt; p = p - lt));
    (toList q, r))

----------------------------------------------------------------------
-- claims
----------------------------------------------------------------------

polynomialIdentityClaim = method()
polynomialIdentityClaim (M2LeanDocument, String, RingElement, RingElement) := (D, cid, f, g) -> (
    rid := exportRing(D, ring f);
    addClaim(D, jobj {
        ("id", jstr cid), ("kind", jstr "PolynomialIdentity"),
        ("ring", jstr rid),
        ("lhs", jsonOfPolynomial f), ("rhs", jsonOfPolynomial g),
        ("evidence", jobj {})}))

-- cofactors witnessing f in I, via M2's internal GB (untrusted)
memberCofactors = (f, I) -> (
    if f % I != 0 then error "M2Lean: element is not in the ideal (no certificate exists)";
    Q := matrix{{f}} // gens I;   -- (gens I) * Q == f
    first entries transpose Q)

membershipClaim = method()
membershipClaim (M2LeanDocument, String, RingElement, Ideal) := (D, cid, f, I) -> (
    iid := exportIdeal(D, I);
    cof := memberCofactors(f, I);
    -- sanity re-check before emitting (the checker would catch it anyway)
    if f != sum(#cof, i -> cof#i * (first entries gens I)#i)
    then error "M2Lean: internal cofactor identity failed";
    addClaim(D, jobj {
        ("id", jstr cid), ("kind", jstr "IdealMembership"),
        ("ideal", jstr iid),
        ("element", jsonOfPolynomial f),
        ("evidence", jobj {("cofactors", jarr (jsonOfPolynomial \ cof))})}))

unitIdealClaim = method()
unitIdealClaim (M2LeanDocument, String, Ideal) := (D, cid, I) ->
    membershipClaim(D, cid, 1_(ring I), I)

spanInclusionClaim = method()
spanInclusionClaim (M2LeanDocument, String, Ideal, Ideal) := (D, cid, I, J) -> (
    iid := exportIdeal(D, I);
    jid := exportIdeal(D, J);
    rows := for f in first entries gens I list memberCofactors(f, J);
    addClaim(D, jobj {
        ("id", jstr cid), ("kind", jstr "SpanInclusion"),
        ("source", jstr iid), ("target", jstr jid),
        ("evidence", jobj {("cofactorRows",
            jarr for row in rows list jarr (jsonOfPolynomial \ row))})}))

-- Groebner basis claim with full Buchberger evidence
gbClaim = method()
gbClaim (M2LeanDocument, String, Ideal) := (D, cid, I) -> (
    R := ring I;
    iid := exportIdeal(D, I);
    B := first entries gens gb I;
    gensI := first entries gens I;
    basisCofactors := for b in B list memberCofactors(b, I);
    Ggb := forceGB matrix{B};
    generatorCofactors := for g in gensI list (
        Q := matrix{{g}} // matrix{B};
        first entries transpose Q);
    n := numgens R;
    sPairs := flatten for i from 0 to #B-1 list for j from i+1 to #B-1 list (
        ei := first exponents leadMonomial B#i;
        ej := first exponents leadMonomial B#j;
        em := for k from 0 to n-1 list max(ei#k, ej#k);
        m := product(n, k -> R_k^(em#k));
        S := (m // leadTerm B#i) * B#i - (m // leadTerm B#j) * B#j;
        (quots, rem) := divisionAlgorithm(S, B);
        if rem != 0 then error "M2Lean: S-polynomial did not reduce to zero against gb output";
        jobj {("i", jint i), ("j", jint j),
              ("quotients", jarr (jsonOfPolynomial \ quots))});
    addClaim(D, jobj {
        ("id", jstr cid), ("kind", jstr "GroebnerBasis"),
        ("ideal", jstr iid),
        ("basis", jarr (jsonOfPolynomial \ B)),
        ("evidence", jobj {
            ("basisCofactors", jarr for row in basisCofactors list
                jarr (jsonOfPolynomial \ row)),
            ("generatorCofactors", jarr for row in generatorCofactors list
                jarr (jsonOfPolynomial \ row)),
            ("sPairs", jarr sPairs)})}))

-- negative certificate: f is NOT in I, witnessed by division against a
-- Groebner basis leaving a nonzero reduced remainder.  The claim
-- references a GroebnerBasis claim (same document) for the basis; its
-- soundness in Lean rests on the Buchberger soundness theorem.
nonMembershipClaim = method(Options => {"groebnerClaim" => "gb1"})
nonMembershipClaim (M2LeanDocument, String, RingElement, Ideal) := o -> (D, cid, f, I) -> (
    gbId := o#"groebnerClaim";
    if f % I == 0 then error "M2Lean: element IS in the ideal (no non-membership certificate exists)";
    iid := exportIdeal(D, I);
    B := first entries gens gb I;
    (q, r) := divisionAlgorithm(f, B);
    if r == 0 then error "M2Lean: internal error, remainder vanished";
    addClaim(D, jobj {
        ("id", jstr cid), ("kind", jstr "NonMembership"),
        ("ideal", jstr iid),
        ("groebnerClaim", jstr gbId),
        ("element", jsonOfPolynomial f),
        ("evidence", jobj {
            ("quotients", jarr (jsonOfPolynomial \ q)),
            ("remainder", jsonOfPolynomial r)})}))

chainComplexClaim = method()
chainComplexClaim (M2LeanDocument, String, List) := (D, cid, mats) -> (
    rid := exportRing(D, ring first mats);
    ids := for M in mats list exportMatrix(D, M);
    for k from 0 to #mats - 2 do
        if mats#k * mats#(k+1) != 0 then error "M2Lean: matrices do not compose to zero";
    addClaim(D, jobj {
        ("id", jstr cid), ("kind", jstr "ChainComplex"),
        ("ring", jstr rid),
        ("differentials", jarr (jstr \ ids)),
        ("evidence", jobj {})}))

-- graded complex: mats#k is d_{k+1} : F_{k+1} -> F_k; degree lists are
-- read off the (graded) sources and targets
gradedComplexClaim = method()
gradedComplexClaim (M2LeanDocument, String, List) := (D, cid, mats) -> (
    R := ring first mats;
    rid := exportRing(D, R);
    degsOf := M -> for d in degrees M list first d;
    modDegs := prepend(degsOf target first mats,
        for M in mats list degsOf source M);
    fids := for degs in modDegs list exportGradedFreeModule(D, R, degs);
    dids := for M in mats list exportMatrix(D, M);
    for k from 0 to #mats - 2 do
        if mats#k * mats#(k+1) != 0 then error "M2Lean: matrices do not compose to zero";
    addClaim(D, jobj {
        ("id", jstr cid), ("kind", jstr "GradedComplex"),
        ("ring", jstr rid),
        ("modules", jarr (jstr \ fids)),
        ("differentials", jarr (jstr \ dids)),
        ("evidence", jobj {})}))

----------------------------------------------------------------------
-- output
----------------------------------------------------------------------

writeM2LeanDocument = method(Options => {"algorithm" => "gb (engine default)"})
writeM2LeanDocument (M2LeanDocument, String) := o -> (D, filename) -> (
    doc := jobj {
        ("m2leanVersion", jstr "0.2.0"),
        ("documentId", jstr D#"docId"),
        ("objects", jarr D#"objects"),
        ("claims", jarr D#"claims"),
        ("provenance", jobj {
            ("producer", jstr "Macaulay2"),
            ("producerVersion", jstr toString version#"VERSION"),
            ("packageVersion", jstr "0.2.0"),
            ("algorithm", jstr o#"algorithm"),
            ("options", jobj {}),
            ("deterministic", "true")})};
    fh := openOut filename;
    fh << jsonPretty(doc, 2) << endl << close;
    filename)

----------------------------------------------------------------------
-- in-session verification: spawn m2lean-check and display the report
----------------------------------------------------------------------

esc := ascii 27
ansi := (code, s) -> esc | "[" | code | "m" | s | esc | "[0m"
green := s -> ansi("32", s)
red' := s -> ansi("31", s)
amber := s -> ansi("33", s)
gray := s -> ansi("90", s)

findChecker = () -> (
    e := getenv "M2LEAN_CHECK";
    if e != "" then return e;
    if 0 == run "command -v m2lean-check > /dev/null 2>&1" then return "m2lean-check";
    fallback := getenv "HOME" | "/m2lean-lean/.lake/build/bin/m2lean-check";
    if fileExists fallback then return fallback;
    error "M2Lean: cannot find m2lean-check; set the M2LEAN_CHECK environment variable")

-- verifyWithLean D: write the document, run the Lean verifier, display
-- per-claim verdicts with their assurance levels, and return the
-- parsed report (a hash table) for programmatic use.
verifyWithLean = method()
verifyWithLean M2LeanDocument := D -> (
    checker := findChecker();
    tmp := temporaryFileName() | ".m2lean.json";
    writeM2LeanDocument(D, tmp);
    rep := tmp | ".report.json";
    status := run(checker | " " | format tmp | " -o " | format rep | " 2> " | format(tmp | ".err"));
    if status >= 256 then status = status // 256;
    if not fileExists rep then (
        errmsg := if fileExists(tmp | ".err") then get(tmp | ".err") else "";
        << red' "document rejected before verification" << " (exit " << status << ")" << endl;
        if #errmsg > 0 then << gray errmsg;
        return null);
    R := fromJSON get rep;
    << "m2lean-check report for document " << gray D#"docId" << ":" << endl;
    for r in R#"results" do (
        ok := r#"status" == "accepted";
        lvl := r#"assurance";
        << "  " << r#"claim" << ": "
          << (if ok then green "accepted" else red' "REJECTED")
          << " [" << (if lvl == "proved" then green lvl
                      else if lvl == "checked" then amber lvl
                      else gray lvl) << "]"
          << (if r#"message" != "" then "  " | gray r#"message" else "")
          << endl);
    R)

beginDocumentation()
doc ///
Key
  M2Lean
Headline
  export certificate documents for independent verification in Lean 4
Description
  Text
    This package exports Macaulay2 computations, together with the
    explicit evidence needed to verify them independently, as M2Lean
    protocol 0.2.0 documents.  Macaulay2 and this package are untrusted
    witness producers: only the Lean checkers and their formal soundness
    theorems determine the reported assurance.
  Text
    The supported coefficient rings are QQ and prime fields.  Polynomial
    rings must use Lex or GRevLex monomial order.
  Example
    R = QQ[x,y]
    I = ideal(x+y,x-y)
    D = newM2LeanDocument "documentation-example"
    membershipClaim(D,"mem1",x^3+y^3,I)
    assert(D =!= null)
  Text
    Use writeM2LeanDocument to retain the certificate or verifyWithLean to
    invoke a previously built m2lean-check executable.  See protocol/SPEC.md
    and docs/trust-model.md in the source repository for the normative format
    and assurance boundaries.
SeeAlso
  newM2LeanDocument
  writeM2LeanDocument
  verifyWithLean
Subnodes
  newM2LeanDocument
  exportRing
  exportIdeal
  exportMatrix
  exportGradedFreeModule
  jsonOfPolynomial
  divisionAlgorithm
  polynomialIdentityClaim
  membershipClaim
  unitIdealClaim
  spanInclusionClaim
  gbClaim
  nonMembershipClaim
  chainComplexClaim
  gradedComplexClaim
  writeM2LeanDocument
  verifyWithLean
///

doc ///
Key
  newM2LeanDocument
  (newM2LeanDocument,String)
Headline
  create an M2Lean protocol document builder
Usage
  D = newM2LeanDocument id
Inputs
  id:String
    a stable identifier for the document
Outputs
  D:M2LeanDocument
Description
  Text
    The builder accumulates exported objects and claims in dependency order.
    It has no assurance until it is serialized and independently checked.
SeeAlso
  writeM2LeanDocument
///

doc ///
Key
  exportRing
  (exportRing,M2LeanDocument,Ring)
Headline
  export a supported polynomial ring
Usage
  id = exportRing(D,R)
Inputs
  D:M2LeanDocument
  R:Ring
Outputs
  id:String
Description
  Text
    Exports the coefficient field, variable display names, and declared Lex
    or GRevLex order.  Repeated export of the same ring returns its existing
    protocol identifier.
///

doc ///
Key
  exportIdeal
  (exportIdeal,M2LeanDocument,Ideal)
Headline
  export an ideal and its ordered generators
Usage
  id = exportIdeal(D,I)
Inputs
  D:M2LeanDocument
  I:Ideal
Outputs
  id:String
Description
  Text
    The ideal's ring is exported first.  Generator order is part of the
    certificate representation because cofactor vectors are positional.
///

doc ///
Key
  exportMatrix
  (exportMatrix,M2LeanDocument,Matrix)
Headline
  export a polynomial matrix
Usage
  id = exportMatrix(D,M)
Inputs
  D:M2LeanDocument
  M:Matrix
Outputs
  id:String
Description
  Text
    Exports dimensions and entries in row-major order after exporting the
    coefficient polynomial ring.
///

doc ///
Key
  exportGradedFreeModule
  (exportGradedFreeModule,M2LeanDocument,Ring,List)
Headline
  export a graded free module from generator degrees
Usage
  id = exportGradedFreeModule(D,R,degrees)
Inputs
  D:M2LeanDocument
  R:Ring
  degrees:List
    one integer degree for each free generator
Outputs
  id:String
Description
  Text
    Each call creates a distinct protocol object, even when another exported
    module has the same degree list.
///

doc ///
Key
  jsonOfPolynomial
Headline
  encode a polynomial in canonical protocol form
Usage
  s = jsonOfPolynomial f
Inputs
  f:RingElement
Outputs
  s:String
Description
  Text
    Returns the JSON fragment for a canonical sparse polynomial in the ring's
    declared order.  Mathematical integers are represented as strings.
///

doc ///
Key
  divisionAlgorithm
  (divisionAlgorithm,RingElement,List)
Headline
  divide by an ordered polynomial list with standard-representation bounds
Usage
  (quotients,remainder) = divisionAlgorithm(f,basis)
Inputs
  f:RingElement
  basis:List
Outputs
  quotients:List
  remainder:RingElement
Description
  Text
    Returns f = sum_i quotients_i*basis_i + remainder.  No remainder term is
    divisible by a leading term of basis, and every subtraction follows the
    declared monomial order.  This is evidence generation, not a trusted
    decision procedure.
///

doc ///
Key
  polynomialIdentityClaim
  (polynomialIdentityClaim,M2LeanDocument,String,RingElement,RingElement)
Headline
  add a polynomial-identity claim
Usage
  polynomialIdentityClaim(D,id,lhs,rhs)
Description
  Text
    Adds a claim that lhs and rhs denote the same polynomial.  The Lean
    consumer checks canonical equality and has a kernel-checked soundness
    theorem for accepted claims.
///

doc ///
Key
  membershipClaim
  (membershipClaim,M2LeanDocument,String,RingElement,Ideal)
Headline
  add an ideal-membership claim with cofactors
Usage
  membershipClaim(D,id,f,I)
Description
  Text
    Computes cofactors expressing f as a linear combination of the ordered
    generators of I.  It raises an error when f is not in I.
///

doc ///
Key
  unitIdealClaim
  (unitIdealClaim,M2LeanDocument,String,Ideal)
Headline
  add a certificate that an ideal contains one
Usage
  unitIdealClaim(D,id,I)
Description
  Text
    A convenience wrapper around membershipClaim for the element 1.
///

doc ///
Key
  spanInclusionClaim
  (spanInclusionClaim,M2LeanDocument,String,Ideal,Ideal)
Headline
  add an inclusion claim between generated ideals
Usage
  spanInclusionClaim(D,id,source,target)
Description
  Text
    Supplies a cofactor row expressing every source generator in the target
    generators.  The checker establishes only the stated inclusion.
///

doc ///
Key
  gbClaim
  (gbClaim,M2LeanDocument,String,Ideal)
Headline
  add a Gröbner-basis claim with complete Buchberger evidence
Usage
  gbClaim(D,id,I)
Description
  Text
    Exports a basis, both change-of-generator directions, and a standard
    representation for every pair of distinct basis elements.  GRevLex
    acceptance has kernel-checked soundness in M2Lean 0.2.0; Lex acceptance is
    executable-only until its formal order bridge is completed.
///

doc ///
Key
  nonMembershipClaim
  (nonMembershipClaim,M2LeanDocument,String,RingElement,Ideal)
Headline
  add a Gröbner-backed non-membership claim
Usage
  nonMembershipClaim(D,id,f,I)
Description
  Text
    Divides f by a Gröbner basis and exports a nonzero fully reduced remainder.
    The string option "groebnerClaim" names the prerequisite Gröbner claim in
    the same document and defaults to "gb1".  Add that claim before this one.
///

doc ///
Key
  chainComplexClaim
  (chainComplexClaim,M2LeanDocument,String,List)
Headline
  add a chain-complex composition claim
Usage
  chainComplexClaim(D,id,differentials)
Description
  Text
    Checks in Macaulay2 and exports that consecutive matrices compose to zero.
    Acceptance does not assert exactness, minimality, or a resolution.
///

doc ///
Key
  gradedComplexClaim
  (gradedComplexClaim,M2LeanDocument,String,List)
Headline
  add a graded-complex runtime claim
Usage
  gradedComplexClaim(D,id,differentials)
Description
  Text
    Exports the source and target generator degrees together with the
    differentials.  Lean checks dimensions, twists, homogeneity, and
    composition at runtime; graded soundness is not yet formalized.
///

doc ///
Key
  writeM2LeanDocument
  (writeM2LeanDocument,M2LeanDocument,String)
Headline
  serialize a protocol 0.2.0 document
Usage
  filename = writeM2LeanDocument(D,filename)
Inputs
  D:M2LeanDocument
  filename:String
Outputs
  filename:String
Description
  Text
    Writes the accumulated objects and claims in canonical JSON form with
    informational provenance.  The string option "algorithm" customizes the
    recorded producer-algorithm description; it never changes assurance.
///

doc ///
Key
  verifyWithLean
  (verifyWithLean,M2LeanDocument)
Headline
  invoke m2lean-check and return its report
Usage
  report = verifyWithLean D
Inputs
  D:M2LeanDocument
Description
  Text
    Writes a temporary document, invokes m2lean-check, displays per-claim
    status and assurance, and returns the parsed report hash table.  Set the
    M2LEAN_CHECK environment variable when the executable is not on PATH.
    A report is operational output, not a Lean proof object.
///

TEST ///
R = QQ[x,y]
D = newM2LeanDocument "package-test"
I = ideal(x+y,x-y)
membershipClaim(D,"mem",x^3+y^3,I)
assert(D =!= null)
///

TEST ///
R = QQ[a,b,c,d]
I = minors(2,matrix{{a,b,c},{b,c,d}})
B = first entries gens gb I
f = a*B#0+b*B#1+(c+d)*B#2
(q,r) = divisionAlgorithm(f,B)
assert(r == 0)
assert(f == sum(#q,i -> q#i*B#i))
///
