import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedSquareNormalizationHomotopy
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleGluedRecovery

/-!
# Recovering a native square class from its normalized singular triangles

The genuine boundary-relative homotopy identifies the original square with
the square pasted from its two normalized triangles. Actual native square
subdivision then recovers its second homotopy class with the original
lower-positive, upper-negative signs.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] {x : X}

/-- Equality in Mathlib's actual boundary-relative homotopy quotient. -/
theorem squareNormalization_quotient (p : GenLoop (Fin 2) X x) :
    (⟦p⟧ : π_ 2 X x) =
      ⟦basedTrianglesLoop (squareNormalizedLowerTriangle p) (squareNormalizedUpperTriangle p)⟧ :=
  Quotient.sound (squareNormalization_homotopic p)

/-- The literal signed normalized triangle classes recover the original native square class. -/
theorem squareNormalization_class (p : GenLoop (Fin 2) X x) :
    basedTriangleClass (squareNormalizedLowerTriangle p) -
        basedTriangleClass (squareNormalizedUpperTriangle p) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  have h := congrArg Additive.ofMul (squareNormalization_quotient p)
  exact (basedTrianglesLoop_class (squareNormalizedLowerTriangle p)
    (squareNormalizedUpperTriangle p)).symm.trans h.symm

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
