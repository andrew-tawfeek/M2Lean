/-
Axiom audit (README §10, acceptance criterion "no `sorry`, no
project-specific axioms").

`#print axioms` on the flagship results must list at most Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`).  In
particular `sorryAx` must not appear.  scripts/audit.sh greps this
file's build output.
-/
import M2Lean.Examples.Flagship
import M2Lean.Examples.Jacobian
import M2Lean.Examples.Coloring
import M2Lean.Examples.Galois
import M2Lean.Groebner.Criterion
import M2Lean.Groebner.Sound
import M2Lean.Groebner.DegRevLex

#print axioms M2Lean.Flagship.certificate_checks
#print axioms M2Lean.Flagship.twisted_cubic_cone_misses_line
#print axioms M2Lean.Flagship.resolution_composes_to_zero
#print axioms M2Lean.Jacobian.jacF_det
#print axioms M2Lean.Jacobian.certificate_checks
#print axioms M2Lean.Jacobian.F_not_injective
#print axioms M2Lean.Jacobian.jacobian_conjecture_false
#print axioms M2Lean.Coloring.certificate_checks
#print axioms M2Lean.Coloring.gens_interp
#print axioms M2Lean.Coloring.wheel5_not_three_colorable
#print axioms M2Lean.Galois.phi8_separable
#print axioms M2Lean.Groebner.buchberger_criterion
#print axioms M2Lean.checkGroebner_sound
#print axioms M2Lean.checkNonMembership_sound
#print axioms MonomialOrder.degRevLex
#print axioms M2Lean.no_common_zero
#print axioms M2Lean.checkMembership_sound
#print axioms M2Lean.checkSpanInclusion_sound
#print axioms M2Lean.checkComplexPair_sound
