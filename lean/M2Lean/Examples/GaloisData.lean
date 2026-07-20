/-
GENERATED FILE - do not edit by hand.
Source: examples/appendix/galois.json (documentId 'appendix-galois'), produced by
Macaulay2 1.24.11 via m2/M2Lean.m2;
converted by scripts/json2lean.py.

The data below is UNTRUSTED M2 output.  Theorems gain their force by
running the certificate checkers on it inside the Lean kernel.
-/
import M2Lean.Protocol.Sparse
import M2Lean.Certificates.Checkers

namespace M2Lean.Galois

open M2Lean

/-- Generators of ideal `I3` (claim `separable`). -/
def separable_gens : List (SPoly Rat) := [
    [⟨(1 : Rat), [4]⟩, ⟨(1 : Rat), [0]⟩],
    [⟨(4 : Rat), [3]⟩]]

/-- The element of claim `separable`. -/
def separable_element : SPoly Rat :=
    [⟨(1 : Rat), [0]⟩]

/-- Macaulay2's cofactors for claim `separable`. -/
def separable_cofactors : List (SPoly Rat) := [
    [⟨(1 : Rat), [0]⟩],
    [⟨(mkRat (-1) 4), [1]⟩]]

end M2Lean.Galois
