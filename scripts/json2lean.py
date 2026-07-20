#!/usr/bin/env python3
"""Claim-generic codegen: embed the claims of an M2Lean protocol
document as Lean literals, so example theorems can consume
certificates through the kernel (`by decide +kernel`) rather than
through file I/O at elaboration time.

Supported claim kinds: IdealMembership (incl. unit-ideal
certificates) and ChainComplex.  For a claim `<id>` the generated
file defines `<id>_gens`, `<id>_element`, `<id>_cofactors`
(membership) or `<id>_d<k>` matrices with their dimensions
(chain complex).

Usage:
  python scripts/json2lean.py DOC.json OUT.lean NAMESPACE [claimId ...]

If no claim ids are given, all supported claims are embedded.  The
generated file is checked in (golden output); re-run after
regenerating the JSON with Macaulay2.
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


def matrix(m):
    rows = ",\n".join(
        "    [" + ", ".join(poly(p) for p in row) + "]"
        for row in m["entries"])
    return "[\n" + rows + "]"


def main():
    doc = json.load(open(sys.argv[1]))
    out_path, ns = sys.argv[2], sys.argv[3]
    wanted = set(sys.argv[4:])
    objs = {o["id"]: o for o in doc["objects"]}

    chunks = []
    for c in doc["claims"]:
        if wanted and c["id"] not in wanted:
            continue
        cid = c["id"].replace("-", "_")
        if c["kind"] == "IdealMembership":
            ideal = objs[c["ideal"]]
            chunks.append(f"""/-- Generators of ideal `{c["ideal"]}` (claim `{c["id"]}`). -/
def {cid}_gens : List (SPoly Rat) := [
{polylist(ideal["generators"])}]

/-- The element of claim `{c["id"]}`. -/
def {cid}_element : SPoly Rat :=
    {poly(c["element"])}

/-- Macaulay2's cofactors for claim `{c["id"]}`. -/
def {cid}_cofactors : List (SPoly Rat) := [
{polylist(c["evidence"]["cofactors"])}]
""")
        elif c["kind"] == "ChainComplex":
            for k, did in enumerate(c["differentials"]):
                d = objs[did]
                chunks.append(f"""/-- Differential {k + 1} of claim `{c["id"]}`
(a {d["rows"]}×{d["cols"]} matrix). -/
def {cid}_d{k + 1} : SMatrix Rat := {matrix(d)}

def {cid}_d{k + 1}_rows : Nat := {d["rows"]}
def {cid}_d{k + 1}_cols : Nat := {d["cols"]}
""")

    body = "\n".join(chunks)
    out = f"""/-
GENERATED FILE - do not edit by hand.
Source: {sys.argv[1]} (documentId '{doc["documentId"]}'), produced by
Macaulay2 {doc["provenance"].get("producerVersion", "?")} via m2/M2Lean.m2;
converted by scripts/json2lean.py.

The data below is UNTRUSTED M2 output.  Theorems gain their force by
running the certificate checkers on it inside the Lean kernel.
-/
import M2Lean.Protocol.Sparse
import M2Lean.Certificates.Checkers

namespace {ns}

open M2Lean

{body}
end {ns}
"""
    open(out_path, "w", newline="\n", encoding="utf-8").write(out)
    print(f"wrote {out_path}")


if __name__ == "__main__":
    main()
