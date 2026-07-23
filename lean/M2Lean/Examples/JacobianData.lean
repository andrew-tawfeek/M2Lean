/-
GENERATED FILE - do not edit by hand.
Source: examples/jacobian/jacobian.json (documentId 'jacobian-counterexample'), produced by
Macaulay2 1.24.11 via m2/M2Lean.m2;
converted by scripts/json2lean.py.

The data below is UNTRUSTED M2 output.  Theorems gain their force by
running the certificate checkers on it inside the Lean kernel.
-/
import M2Lean.Protocol.Sparse
import M2Lean.Certificates.Checkers

namespace M2Lean.Jacobian

open M2Lean

/-- Generators of ideal `I3` (claim `P0_F1`). -/
def P0_F1_gens : List (SPoly Rat) := [
    [⟨(1 : Rat), [1, 0, 0]⟩],
    [⟨(1 : Rat), [0, 1, 0]⟩],
    [⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (1) 4), [0, 0, 0]⟩]]

/-- The element of claim `P0_F1`. -/
def P0_F1_element : SPoly Rat :=
    [⟨(1 : Rat), [3, 3, 1]⟩, ⟨(3 : Rat), [2, 4, 0]⟩, ⟨(3 : Rat), [2, 2, 1]⟩, ⟨(7 : Rat), [1, 3, 0]⟩, ⟨(3 : Rat), [1, 1, 1]⟩, ⟨(4 : Rat), [0, 2, 0]⟩, ⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (1) 4), [0, 0, 0]⟩]

/-- Macaulay2's cofactors for claim `P0_F1`. -/
def P0_F1_cofactors : List (SPoly Rat) := [
    [],
    [⟨(mkRat (-1) 4), [3, 2, 0]⟩, ⟨(3 : Rat), [2, 3, 0]⟩, ⟨(3 : Rat), [2, 1, 1]⟩, ⟨(7 : Rat), [1, 2, 0]⟩, ⟨(3 : Rat), [1, 0, 1]⟩, ⟨(4 : Rat), [0, 1, 0]⟩],
    [⟨(1 : Rat), [3, 3, 0]⟩, ⟨(1 : Rat), [0, 0, 0]⟩]]

/-- Generators of ideal `I3` (claim `P0_F2`). -/
def P0_F2_gens : List (SPoly Rat) := [
    [⟨(1 : Rat), [1, 0, 0]⟩],
    [⟨(1 : Rat), [0, 1, 0]⟩],
    [⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (1) 4), [0, 0, 0]⟩]]

/-- The element of claim `P0_F2`. -/
def P0_F2_element : SPoly Rat :=
    [⟨(3 : Rat), [3, 2, 1]⟩, ⟨(9 : Rat), [2, 3, 0]⟩, ⟨(6 : Rat), [2, 1, 1]⟩, ⟨(12 : Rat), [1, 2, 0]⟩, ⟨(3 : Rat), [1, 0, 1]⟩, ⟨(1 : Rat), [0, 1, 0]⟩]

/-- Macaulay2's cofactors for claim `P0_F2`. -/
def P0_F2_cofactors : List (SPoly Rat) := [
    [⟨(mkRat (-3) 4), [0, 0, 0]⟩],
    [⟨(mkRat (-3) 4), [3, 1, 0]⟩, ⟨(9 : Rat), [2, 2, 0]⟩, ⟨(6 : Rat), [2, 0, 1]⟩, ⟨(12 : Rat), [1, 1, 0]⟩, ⟨(1 : Rat), [0, 0, 0]⟩],
    [⟨(3 : Rat), [3, 2, 0]⟩, ⟨(3 : Rat), [1, 0, 0]⟩]]

/-- Generators of ideal `I3` (claim `P0_F3`). -/
def P0_F3_gens : List (SPoly Rat) := [
    [⟨(1 : Rat), [1, 0, 0]⟩],
    [⟨(1 : Rat), [0, 1, 0]⟩],
    [⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (1) 4), [0, 0, 0]⟩]]

/-- The element of claim `P0_F3`. -/
def P0_F3_element : SPoly Rat :=
    [⟨((-1) : Rat), [3, 0, 1]⟩, ⟨((-3) : Rat), [2, 1, 0]⟩, ⟨(2 : Rat), [1, 0, 0]⟩]

/-- Macaulay2's cofactors for claim `P0_F3`. -/
def P0_F3_cofactors : List (SPoly Rat) := [
    [⟨(mkRat (1) 4), [2, 0, 0]⟩, ⟨((-3) : Rat), [1, 1, 0]⟩, ⟨(2 : Rat), [0, 0, 0]⟩],
    [],
    [⟨((-1) : Rat), [3, 0, 0]⟩]]

/-- Generators of ideal `I4` (claim `P1_F1`). -/
def P1_F1_gens : List (SPoly Rat) := [
    [⟨(1 : Rat), [1, 0, 0]⟩, ⟨((-1) : Rat), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 1, 0]⟩, ⟨(mkRat (3) 2), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (-13) 2), [0, 0, 0]⟩]]

/-- The element of claim `P1_F1`. -/
def P1_F1_element : SPoly Rat :=
    [⟨(1 : Rat), [3, 3, 1]⟩, ⟨(3 : Rat), [2, 4, 0]⟩, ⟨(3 : Rat), [2, 2, 1]⟩, ⟨(7 : Rat), [1, 3, 0]⟩, ⟨(3 : Rat), [1, 1, 1]⟩, ⟨(4 : Rat), [0, 2, 0]⟩, ⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (1) 4), [0, 0, 0]⟩]

/-- Macaulay2's cofactors for claim `P1_F1`. -/
def P1_F1_cofactors : List (SPoly Rat) := [
    [⟨(mkRat (-351) 16), [2, 0, 0]⟩, ⟨(mkRat (-81) 8), [1, 1, 0]⟩, ⟨(mkRat (-21) 2), [0, 2, 0]⟩, ⟨(mkRat (27) 4), [1, 0, 1]⟩, ⟨(3 : Rat), [0, 1, 1]⟩, ⟨(mkRat (-351) 16), [1, 0, 0]⟩, ⟨(mkRat (-81) 8), [0, 1, 0]⟩, ⟨(mkRat (351) 16), [0, 0, 0]⟩],
    [⟨(mkRat (13) 2), [3, 2, 0]⟩, ⟨(3 : Rat), [2, 3, 0]⟩, ⟨(mkRat (-39) 4), [3, 1, 0]⟩, ⟨(mkRat (-9) 2), [2, 2, 0]⟩, ⟨(3 : Rat), [2, 1, 1]⟩, ⟨(mkRat (117) 8), [3, 0, 0]⟩, ⟨(mkRat (27) 4), [2, 1, 0]⟩, ⟨(7 : Rat), [1, 2, 0]⟩, ⟨(mkRat (-9) 2), [2, 0, 1]⟩, ⟨(mkRat (-13) 2), [0, 1, 0]⟩, ⟨(mkRat (153) 8), [0, 0, 0]⟩],
    [⟨(1 : Rat), [3, 3, 0]⟩, ⟨(mkRat (27) 4), [1, 0, 0]⟩, ⟨(3 : Rat), [0, 1, 0]⟩, ⟨(1 : Rat), [0, 0, 0]⟩]]

/-- Generators of ideal `I4` (claim `P1_F2`). -/
def P1_F2_gens : List (SPoly Rat) := [
    [⟨(1 : Rat), [1, 0, 0]⟩, ⟨((-1) : Rat), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 1, 0]⟩, ⟨(mkRat (3) 2), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (-13) 2), [0, 0, 0]⟩]]

/-- The element of claim `P1_F2`. -/
def P1_F2_element : SPoly Rat :=
    [⟨(3 : Rat), [3, 2, 1]⟩, ⟨(9 : Rat), [2, 3, 0]⟩, ⟨(6 : Rat), [2, 1, 1]⟩, ⟨(12 : Rat), [1, 2, 0]⟩, ⟨(3 : Rat), [1, 0, 1]⟩, ⟨(1 : Rat), [0, 1, 0]⟩]

/-- Macaulay2's cofactors for claim `P1_F2`. -/
def P1_F2_cofactors : List (SPoly Rat) := [
    [⟨(mkRat (351) 8), [2, 0, 0]⟩, ⟨(mkRat (81) 4), [1, 1, 0]⟩, ⟨(12 : Rat), [0, 2, 0]⟩, ⟨((-9) : Rat), [1, 0, 1]⟩, ⟨(mkRat (351) 8), [1, 0, 0]⟩, ⟨(mkRat (81) 4), [0, 1, 0]⟩, ⟨(mkRat (39) 8), [0, 0, 0]⟩],
    [⟨(mkRat (39) 2), [3, 1, 0]⟩, ⟨(9 : Rat), [2, 2, 0]⟩, ⟨(mkRat (-117) 4), [3, 0, 0]⟩, ⟨(mkRat (-27) 2), [2, 1, 0]⟩, ⟨(6 : Rat), [2, 0, 1]⟩, ⟨(12 : Rat), [0, 1, 0]⟩, ⟨(mkRat (13) 4), [0, 0, 0]⟩],
    [⟨(3 : Rat), [3, 2, 0]⟩, ⟨((-6) : Rat), [1, 0, 0]⟩]]

/-- Generators of ideal `I4` (claim `P1_F3`). -/
def P1_F3_gens : List (SPoly Rat) := [
    [⟨(1 : Rat), [1, 0, 0]⟩, ⟨((-1) : Rat), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 1, 0]⟩, ⟨(mkRat (3) 2), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (-13) 2), [0, 0, 0]⟩]]

/-- The element of claim `P1_F3`. -/
def P1_F3_element : SPoly Rat :=
    [⟨((-1) : Rat), [3, 0, 1]⟩, ⟨((-3) : Rat), [2, 1, 0]⟩, ⟨(2 : Rat), [1, 0, 0]⟩]

/-- Macaulay2's cofactors for claim `P1_F3`. -/
def P1_F3_cofactors : List (SPoly Rat) := [
    [⟨(mkRat (-13) 2), [2, 0, 0]⟩, ⟨((-3) : Rat), [1, 1, 0]⟩, ⟨(mkRat (-13) 2), [1, 0, 0]⟩, ⟨((-3) : Rat), [0, 1, 0]⟩, ⟨(mkRat (-9) 2), [0, 0, 0]⟩],
    [⟨((-3) : Rat), [0, 0, 0]⟩],
    [⟨((-1) : Rat), [3, 0, 0]⟩]]

/-- Generators of ideal `I5` (claim `P2_F1`). -/
def P2_F1_gens : List (SPoly Rat) := [
    [⟨(1 : Rat), [1, 0, 0]⟩, ⟨(1 : Rat), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 1, 0]⟩, ⟨(mkRat (-3) 2), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (-13) 2), [0, 0, 0]⟩]]

/-- The element of claim `P2_F1`. -/
def P2_F1_element : SPoly Rat :=
    [⟨(1 : Rat), [3, 3, 1]⟩, ⟨(3 : Rat), [2, 4, 0]⟩, ⟨(3 : Rat), [2, 2, 1]⟩, ⟨(7 : Rat), [1, 3, 0]⟩, ⟨(3 : Rat), [1, 1, 1]⟩, ⟨(4 : Rat), [0, 2, 0]⟩, ⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (1) 4), [0, 0, 0]⟩]

/-- Macaulay2's cofactors for claim `P2_F1`. -/
def P2_F1_cofactors : List (SPoly Rat) := [
    [⟨(mkRat (351) 16), [2, 0, 0]⟩, ⟨(mkRat (81) 8), [1, 1, 0]⟩, ⟨(mkRat (21) 2), [0, 2, 0]⟩, ⟨(mkRat (27) 4), [1, 0, 1]⟩, ⟨(3 : Rat), [0, 1, 1]⟩, ⟨(mkRat (-351) 16), [1, 0, 0]⟩, ⟨(mkRat (-81) 8), [0, 1, 0]⟩, ⟨(mkRat (-351) 16), [0, 0, 0]⟩],
    [⟨(mkRat (13) 2), [3, 2, 0]⟩, ⟨(3 : Rat), [2, 3, 0]⟩, ⟨(mkRat (39) 4), [3, 1, 0]⟩, ⟨(mkRat (9) 2), [2, 2, 0]⟩, ⟨(3 : Rat), [2, 1, 1]⟩, ⟨(mkRat (117) 8), [3, 0, 0]⟩, ⟨(mkRat (27) 4), [2, 1, 0]⟩, ⟨(7 : Rat), [1, 2, 0]⟩, ⟨(mkRat (9) 2), [2, 0, 1]⟩, ⟨(mkRat (-13) 2), [0, 1, 0]⟩, ⟨(mkRat (-153) 8), [0, 0, 0]⟩],
    [⟨(1 : Rat), [3, 3, 0]⟩, ⟨(mkRat (-27) 4), [1, 0, 0]⟩, ⟨((-3) : Rat), [0, 1, 0]⟩, ⟨(1 : Rat), [0, 0, 0]⟩]]

/-- Generators of ideal `I5` (claim `P2_F2`). -/
def P2_F2_gens : List (SPoly Rat) := [
    [⟨(1 : Rat), [1, 0, 0]⟩, ⟨(1 : Rat), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 1, 0]⟩, ⟨(mkRat (-3) 2), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (-13) 2), [0, 0, 0]⟩]]

/-- The element of claim `P2_F2`. -/
def P2_F2_element : SPoly Rat :=
    [⟨(3 : Rat), [3, 2, 1]⟩, ⟨(9 : Rat), [2, 3, 0]⟩, ⟨(6 : Rat), [2, 1, 1]⟩, ⟨(12 : Rat), [1, 2, 0]⟩, ⟨(3 : Rat), [1, 0, 1]⟩, ⟨(1 : Rat), [0, 1, 0]⟩]

/-- Macaulay2's cofactors for claim `P2_F2`. -/
def P2_F2_cofactors : List (SPoly Rat) := [
    [⟨(mkRat (351) 8), [2, 0, 0]⟩, ⟨(mkRat (81) 4), [1, 1, 0]⟩, ⟨(12 : Rat), [0, 2, 0]⟩, ⟨(9 : Rat), [1, 0, 1]⟩, ⟨(mkRat (-351) 8), [1, 0, 0]⟩, ⟨(mkRat (-81) 4), [0, 1, 0]⟩, ⟨(mkRat (39) 8), [0, 0, 0]⟩],
    [⟨(mkRat (39) 2), [3, 1, 0]⟩, ⟨(9 : Rat), [2, 2, 0]⟩, ⟨(mkRat (117) 4), [3, 0, 0]⟩, ⟨(mkRat (27) 2), [2, 1, 0]⟩, ⟨(6 : Rat), [2, 0, 1]⟩, ⟨((-12) : Rat), [0, 1, 0]⟩, ⟨(mkRat (13) 4), [0, 0, 0]⟩],
    [⟨(3 : Rat), [3, 2, 0]⟩, ⟨((-6) : Rat), [1, 0, 0]⟩]]

/-- Generators of ideal `I5` (claim `P2_F3`). -/
def P2_F3_gens : List (SPoly Rat) := [
    [⟨(1 : Rat), [1, 0, 0]⟩, ⟨(1 : Rat), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 1, 0]⟩, ⟨(mkRat (-3) 2), [0, 0, 0]⟩],
    [⟨(1 : Rat), [0, 0, 1]⟩, ⟨(mkRat (-13) 2), [0, 0, 0]⟩]]

/-- The element of claim `P2_F3`. -/
def P2_F3_element : SPoly Rat :=
    [⟨((-1) : Rat), [3, 0, 1]⟩, ⟨((-3) : Rat), [2, 1, 0]⟩, ⟨(2 : Rat), [1, 0, 0]⟩]

/-- Macaulay2's cofactors for claim `P2_F3`. -/
def P2_F3_cofactors : List (SPoly Rat) := [
    [⟨(mkRat (-13) 2), [2, 0, 0]⟩, ⟨((-3) : Rat), [1, 1, 0]⟩, ⟨(mkRat (13) 2), [1, 0, 0]⟩, ⟨(3 : Rat), [0, 1, 0]⟩, ⟨(mkRat (-9) 2), [0, 0, 0]⟩],
    [⟨((-3) : Rat), [0, 0, 0]⟩],
    [⟨((-1) : Rat), [3, 0, 0]⟩]]

end M2Lean.Jacobian
