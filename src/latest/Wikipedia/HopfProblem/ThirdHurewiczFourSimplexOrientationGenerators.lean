import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexOrientationGeneratorsCycle
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexOrientationGeneratorsSwapLast

/-!
# Actual orientation-reversing generators on based three-simplices

The cyclic barycentric permutation `(a₀,a₁,a₂,a₃) ↦ (a₁,a₂,a₃,a₀)`
and the last-coordinate transposition `(a₀,a₁,a₂,a₃) ↦ (a₀,a₁,a₃,a₂)`
both negate the class in Mathlib's original third homotopy group.
The proofs retain the original singular simplex and use explicit homotopies
relative to the entire native cube boundary, not homological detection.
-/
