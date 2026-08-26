import ErdosProblems.Erdos768.Main
import ErdosProblems.Erdos49.PNT.MediumPNT

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Axiom audit

Part of the default build target: `lake build` fails unless the main theorem
and the vendored analytic input depend on exactly the three standard axioms.
-/

/-- info: 'Erdos768.erdos_768' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos768.erdos_768

/-- info: 'MediumPNT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MediumPNT
