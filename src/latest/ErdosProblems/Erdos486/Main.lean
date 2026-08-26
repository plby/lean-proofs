import ErdosProblems.Erdos486.BiasedInterface
import ErdosProblems.Erdos486.Global

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! # Final theorems for Erdős Problem 486 -/

namespace Erdos486

/-- The fully instantiated quantitative counterexample. -/
theorem erdos486_quantitativeCounterexample : QuantitativeCounterexample :=
  quantitativeCounterexample_of_dyadicBlockInterface erdos486BlockInterface

/-- Erdős Problem 486 has a negative answer. -/
theorem erdos486_negative : ¬Erdos486Assertion :=
  not_erdos486Assertion_of_dyadicBlockInterface erdos486BlockInterface

end Erdos486
