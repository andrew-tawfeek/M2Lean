/-
M2Lean: `by macaulay2` in action.

The goal below asks whether `x³ + y³` lies in the ideal `(x + y, x − y)`
of `ℚ[x,y]`.  The tactic ships the question to a live Macaulay2
process, receives the cofactors, and closes the goal by kernel-checking
the certificate — the entire M2Lean architecture compressed into a
single tactic call.  (Requires `M2` on `PATH` at build time; this file
is built in CI.)
-/
import M2Lean.Tactic.Macaulay2

namespace M2Lean.TacticDemo

open M2Lean

/-- `x³ + y³` as sparse data. -/
def f : SPoly ℚ := [⟨1, [3, 0]⟩, ⟨1, [0, 3]⟩]

/-- The generators `x + y` and `x − y`. -/
def gs : List (SPoly ℚ) := [[⟨1, [1, 0]⟩, ⟨1, [0, 1]⟩], [⟨1, [1, 0]⟩, ⟨-1, [0, 1]⟩]]

example : toMv 2 f ∈ spanOf 2 gs := by macaulay2

end M2Lean.TacticDemo
