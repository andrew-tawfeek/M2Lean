/-
GENERATED FILE - do not edit by hand.
Source: examples/flagship/flagship.json (documentId 'flagship'), produced by
Macaulay2 1.24.11 via m2/M2Lean.m2;
converted by scripts/json2lean.py.

The data below is UNTRUSTED M2 output.  Theorems gain their force by
running the certificate checkers on it inside the Lean kernel.
-/
import M2Lean.Protocol.Sparse
import M2Lean.Certificates.Checkers

namespace M2Lean.Flagship

open M2Lean

/-- Generators of ideal `I3` (claim `unit1`). -/
def unit1_gens : List (SPoly Rat) := [
    [⟨((-1) : Rat), [0, 2, 0, 0]⟩, ⟨(1 : Rat), [1, 0, 1, 0]⟩],
    [⟨((-1) : Rat), [0, 1, 1, 0]⟩, ⟨(1 : Rat), [1, 0, 0, 1]⟩],
    [⟨((-1) : Rat), [0, 0, 2, 0]⟩, ⟨(1 : Rat), [0, 1, 0, 1]⟩],
    [⟨(1 : Rat), [0, 1, 0, 0]⟩, ⟨((-1) : Rat), [0, 0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 0, 1, 0]⟩],
    [⟨(1 : Rat), [0, 0, 0, 1]⟩]]

/-- The element of claim `unit1`. -/
def unit1_element : SPoly Rat :=
    [⟨(1 : Rat), [0, 0, 0, 0]⟩]

/-- Macaulay2's cofactors for claim `unit1`. -/
def unit1_cofactors : List (SPoly Rat) := [
    [⟨((-1) : Rat), [0, 0, 0, 0]⟩],
    [],
    [],
    [⟨((-1) : Rat), [0, 1, 0, 0]⟩, ⟨((-1) : Rat), [0, 0, 0, 0]⟩],
    [⟨(1 : Rat), [1, 0, 0, 0]⟩],
    []]

/-- Differential 1 of claim `cx1`
(a 1×3 matrix). -/
def cx1_d1 : SMatrix Rat := [
    [[⟨(1 : Rat), [0, 2, 0, 0]⟩, ⟨((-1) : Rat), [1, 0, 1, 0]⟩], [⟨(1 : Rat), [0, 1, 1, 0]⟩, ⟨((-1) : Rat), [1, 0, 0, 1]⟩], [⟨(1 : Rat), [0, 0, 2, 0]⟩, ⟨((-1) : Rat), [0, 1, 0, 1]⟩]]]

def cx1_d1_rows : Nat := 1
def cx1_d1_cols : Nat := 3

/-- Differential 2 of claim `cx1`
(a 3×2 matrix). -/
def cx1_d2 : SMatrix Rat := [
    [[⟨((-1) : Rat), [0, 0, 1, 0]⟩], [⟨(1 : Rat), [0, 0, 0, 1]⟩]],
    [[⟨(1 : Rat), [0, 1, 0, 0]⟩], [⟨((-1) : Rat), [0, 0, 1, 0]⟩]],
    [[⟨((-1) : Rat), [1, 0, 0, 0]⟩], [⟨(1 : Rat), [0, 1, 0, 0]⟩]]]

def cx1_d2_rows : Nat := 3
def cx1_d2_cols : Nat := 2

end M2Lean.Flagship
