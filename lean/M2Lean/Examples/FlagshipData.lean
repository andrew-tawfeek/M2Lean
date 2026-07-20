/-
GENERATED FILE - do not edit by hand.
Source: examples/flagship/flagship.json (documentId 'flagship'), produced by
Macaulay2 1.24.11 via m2/M2Lean.m2;
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
{(t,1,0,0)} = V(y-1, z, w).  Variables x,y,z,w are positions 0-3. -/
def gens : List SPoly := [
    [⟨((-1) : Rat), [0, 2, 0, 0]⟩, ⟨(1 : Rat), [1, 0, 1, 0]⟩],
    [⟨((-1) : Rat), [0, 1, 1, 0]⟩, ⟨(1 : Rat), [1, 0, 0, 1]⟩],
    [⟨((-1) : Rat), [0, 0, 2, 0]⟩, ⟨(1 : Rat), [0, 1, 0, 1]⟩],
    [⟨(1 : Rat), [0, 1, 0, 0]⟩, ⟨((-1) : Rat), [0, 0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 0, 1, 0]⟩],
    [⟨(1 : Rat), [0, 0, 0, 1]⟩]]

/-- Macaulay2's cofactors c_i with 1 = sum c_i * gens_i. -/
def cofactors : List SPoly := [
    [⟨((-1) : Rat), [0, 0, 0, 0]⟩],
    [],
    [],
    [⟨((-1) : Rat), [0, 1, 0, 0]⟩, ⟨((-1) : Rat), [0, 0, 0, 0]⟩],
    [⟨(1 : Rat), [1, 0, 0, 0]⟩],
    []]

/-- First differential of the minimal free resolution of R/I(C)
(the 1x3 matrix of minors). -/
def resD1 : SMatrix := [
    [[⟨(1 : Rat), [0, 2, 0, 0]⟩, ⟨((-1) : Rat), [1, 0, 1, 0]⟩], [⟨(1 : Rat), [0, 1, 1, 0]⟩, ⟨((-1) : Rat), [1, 0, 0, 1]⟩], [⟨(1 : Rat), [0, 0, 2, 0]⟩, ⟨((-1) : Rat), [0, 1, 0, 1]⟩]]]

/-- Second differential (the 3x2 Eagon-Northcott matrix). -/
def resD2 : SMatrix := [
    [[⟨((-1) : Rat), [0, 0, 1, 0]⟩], [⟨(1 : Rat), [0, 0, 0, 1]⟩]],
    [[⟨(1 : Rat), [0, 1, 0, 0]⟩], [⟨((-1) : Rat), [0, 0, 1, 0]⟩]],
    [[⟨((-1) : Rat), [1, 0, 0, 0]⟩], [⟨(1 : Rat), [0, 1, 0, 0]⟩]]]

end M2Lean.Flagship
