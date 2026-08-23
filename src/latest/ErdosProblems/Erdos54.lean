/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 54.
https://www.erdosproblems.com/forum/thread/54

Informal authors:
- David Conlon
- Jacob Fox
- Huy Tuan Pham

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos54.md
-/
import ErdosProblems.Erdos54.RobustBlock

/-!
# Erdős Problem 54

Conlon, Fox, and Pham proved that there is a Ramsey `2`-complete set of
positive integers whose counting function is `O((log N)^2)`.  This improves
the earlier cubic logarithmic upper bound of Burr and Erdős.

The definitions imported below use finite sets of a subtype, so every
monochromatic representation has distinct summands.  `RamseyTwoComplete`
has the original quantifier order: the eventual threshold may depend on the
colouring.
-/

namespace Erdos54

/-- The Conlon--Fox--Pham resolution of Erdős Problem 54: a positive Ramsey
`2`-complete set exists with eventual `O((log N)^2)` counting function. -/
theorem erdos_54 : ConlonFoxPhamUpperBoundTwo :=
  upperBound_of_robust_block_existence robust_blocks

end Erdos54

#print axioms Erdos54.erdos_54
