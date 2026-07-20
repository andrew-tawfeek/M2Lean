/-
Axiom audit (README §10, acceptance criterion "no `sorry`, no
project-specific axioms").

`#print axioms` on the flagship results must list at most Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).  In
particular `sorryAx` must not appear.  scripts/audit.sh greps this
file's build output.
-/
import M2Lean.Examples.Flagship

#print axioms M2Lean.Flagship.certificate_checks
#print axioms M2Lean.Flagship.twisted_cubic_cone_misses_line
#print axioms M2Lean.Flagship.resolution_composes_to_zero
#print axioms M2Lean.no_common_zero
#print axioms M2Lean.checkMembership_sound
#print axioms M2Lean.checkSpanInclusion_sound
#print axioms M2Lean.checkComplexPair_sound
