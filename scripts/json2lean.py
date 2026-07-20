#!/usr/bin/env python3
"""Deterministic codegen: embed selected claims of an M2Lean protocol
document as Lean literals, so that example theorems can consume the
certificate through the kernel (`by decide`) rather than through file
I/O at elaboration time.

Usage: python scripts/json2lean.py examples/flagship/flagship.json \
           lean/M2Lean/Examples/FlagshipData.lean

The generated file is checked in (golden output); re-run this script
after regenerating the JSON with Macaulay2.
"""
import json
import sys


def rat(c):
    num, den = int(c["num"]), int(c["den"])
    if den == 1:
        return f"({num} : Rat)" if num >= 0 else f"(({num}) : Rat)"
    return f"(mkRat ({num}) {den})"


def term(t):
    exps = ", ".join(str(e) for e in t["exponents"])
    return f"⟨{rat(t['coefficient'])}, [{exps}]⟩"


def poly(p):
    return "[" + ", ".join(term(t) for t in p["terms"]) + "]"


def polylist(ps, indent="    "):
    return ",\n".join(indent + poly(p) for p in ps)


def main():
    doc = json.load(open(sys.argv[1]))
    objs = {o["id"]: o for o in doc["objects"]}
    claims = {c["id"]: c for c in doc["claims"]}

    unit = claims["unit1"]
    ideal = objs[unit["ideal"]]
    gens = ideal["generators"]
    cofs = unit["evidence"]["cofactors"]

    cx = claims["cx1"]
    d1, d2 = (objs[i] for i in cx["differentials"])

    def matrix(m):
        rows = ",\n".join(
            "    [" + ", ".join(poly(p) for p in row) + "]"
            for row in m["entries"])
        return "[\n" + rows + "]"

    out = f"""/-
GENERATED FILE - do not edit by hand.
Source: {sys.argv[1]} (documentId '{doc["documentId"]}'), produced by
Macaulay2 {doc["provenance"].get("producerVersion", "?")} via m2/M2Lean.m2;
converted by scripts/json2lean.py.

The data below is UNTRUSTED M2 output.  The theorems in
`M2Lean.Examples.Flagship` gain their force by running the certificate
checkers on it inside the Lean kernel.
-/
import M2Lean.Protocol.Sparse
import M2Lean.Certificates.Checkers

namespace M2Lean.Flagship

open M2Lean

/-- Generators of I(C) + I(L): the three 2x2 minors cutting out the
twisted cubic cone, followed by the ideal of the line
{{(t,1,0,0)}} = V(y-1, z, w).  Variables x,y,z,w are positions 0-3. -/
def gens : List SPoly := [
{polylist(gens)}]

/-- Macaulay2's cofactors c_i with 1 = sum c_i * gens_i. -/
def cofactors : List SPoly := [
{polylist(cofs)}]

/-- First differential of the minimal free resolution of R/I(C)
(the {d1["rows"]}x{d1["cols"]} matrix of minors). -/
def resD1 : SMatrix := {matrix(d1)}

/-- Second differential (the {d2["rows"]}x{d2["cols"]} Eagon-Northcott matrix). -/
def resD2 : SMatrix := {matrix(d2)}

end M2Lean.Flagship
"""
    open(sys.argv[2], "w", newline="\n", encoding="utf-8").write(out)
    print(f"wrote {sys.argv[2]}")


if __name__ == "__main__":
    main()
