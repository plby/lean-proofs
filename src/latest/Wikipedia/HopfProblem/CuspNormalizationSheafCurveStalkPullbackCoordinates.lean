import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesFibre

/-!
# Literal signed-lift identities in centered axis coordinates

The actual positive and negative maps from a double curve to the
normalization become coordinate-axis inclusions inside their actual
affine branch parametrizations. The identities hold for every scalar
coordinate, not only as abstract maps between germ rings.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk

open CuspQuotient ToricCharts ToricSpace ToricComponent ToricFan
  Triangle NormalizationCurves NormalizationLocalCoordinates

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (s : Triangle) (b : CoordinateSpace 3) (k : Fin 3)
  (hk : sourcePair s k ⊆ Germs.activeBranches b)

include hk in
/-- The actual positive lift in the branch chart centered over `b`. -/
theorem sourcePlusLift_axisSection_centered (z : ℂ) :
    sourcePlusLift C ε hε k
        (axisSection C ε hε s (sourceEdgeIndex k)
          (b (s.axisIndex (sourceEdgeIndex k)) + z)) =
      branchAffine C s (plusBranch s k)
        (removeCoordinate (plusBranch s k) b + Pi.single (plusAxisIndex s k) z) := by
  rw [sourcePlusLift_axisSection]
  change branchAffine C s (plusBranch s k)
    (removeCoordinate (plusBranch s k)
      (axisPoint s (sourceEdgeIndex k) (b (s.axisIndex (sourceEdgeIndex k)) + z))) = _
  rw [axisPoint_add, removeCoordinate_add, ← eq_axisPoint_of_pair_active s b k hk]
  apply congrArg (branchAffine C s (plusBranch s k))
  apply congrArg (fun w => removeCoordinate (plusBranch s k) b + w)
  exact removeCoordinate_single _ _ (plusBranch_ne_axisIndex s k).symm z

include hk in
/-- The actual negative lift in the branch chart centered over `b`. -/
theorem sourceMinusLift_axisSection_centered (z : ℂ) :
    sourceMinusLift C ε hε k
        (axisSection C ε hε s (sourceEdgeIndex k)
          (b (s.axisIndex (sourceEdgeIndex k)) + z)) =
      branchAffine C s (minusBranch s k)
        (removeCoordinate (minusBranch s k) b + Pi.single (minusAxisIndex s k) z) := by
  rw [sourceMinusLift_axisSection]
  change branchAffine C s (minusBranch s k)
    (removeCoordinate (minusBranch s k)
      (axisPoint s (sourceEdgeIndex k) (b (s.axisIndex (sourceEdgeIndex k)) + z))) = _
  rw [axisPoint_add, removeCoordinate_add, ← eq_axisPoint_of_pair_active s b k hk]
  apply congrArg (branchAffine C s (minusBranch s k))
  apply congrArg (fun w => removeCoordinate (minusBranch s k) b + w)
  exact removeCoordinate_single _ _ (minusBranch_ne_axisIndex s k).symm z

end Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk
