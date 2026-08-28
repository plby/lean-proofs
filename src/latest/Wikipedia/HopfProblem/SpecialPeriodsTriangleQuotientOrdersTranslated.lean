import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientOrders

/-!
# Branching orders at all translates of the elliptic centers

The actual real determinant-one action is analytic in the ambient complex
coordinate and has nonzero derivative. Composition with this action therefore
preserves analytic order. Applying this to an invariant quotient-coordinate
function transports its exact order from an elliptic center to every point
of its actual triangle-group orbit.
-/

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The actual determinant-one action is analytic in the ambient complex
germ at every upper-half-plane point. -/
theorem sl_analyticAt_smul (g : SL(2, ℝ)) (z : ℍ) :
    AnalyticAt ℂ (fun w : ℂ => ((g • ofComplex w : ℍ) : ℂ)) (z : ℂ) := by
  have h := UpperHalfPlane.analyticAt_smul
    (g := Matrix.SpecialLinearGroup.mapGL ℝ g) (by simp) z
  simpa only [MulAction.compHom_smul_def] using h

/-- Change of ambient complex coordinate by a real determinant-one matrix
preserves analytic order, with no analyticity assumption on the function. -/
theorem sl_analyticOrderAt_comp_smul (f : ℍ → ℂ) (g : SL(2, ℝ)) (z : ℍ) :
    analyticOrderAt (fun w : ℂ => f (g • ofComplex w)) (z : ℂ) =
      analyticOrderAt (f ∘ ofComplex) ((g • z : ℍ) : ℂ) := by
  let G : ℂ → ℂ := fun w => ((g • ofComplex w : ℍ) : ℂ)
  have he : (fun w : ℂ => f (g • ofComplex w)) = (f ∘ ofComplex) ∘ G := by
    funext w
    simp only [Function.comp_apply, G, ofComplex_apply]
  rw [he, analyticOrderAt_comp_of_deriv_ne_zero]
  · simp only [G, ofComplex_apply]
  · exact sl_analyticAt_smul g z
  · rw [sl_deriv_smul]
    exact div_ne_zero one_ne_zero (pow_ne_zero 2 (slDenom_ne_zero g z))

/-- The same order transport for the actual abstract triangle-group action,
using its proved realization by real determinant-one matrices. -/
theorem triangle_analyticOrderAt_comp_action (f : ℍ → ℂ)
    (g : TriangleGroup) (z : ℍ) :
    analyticOrderAt (fun w : ℂ => f (triangleGeometricRepresentation g (ofComplex w)))
      (z : ℂ) =
      analyticOrderAt (f ∘ ofComplex) (triangleGeometricRepresentation g z : ℂ) := by
  have hl (w : ℍ) : (triangleMatrixLift g).val • w =
      triangleGeometricRepresentation g w := triangleMatrixLift_smul g w
  simpa only [hl] using
    sl_analyticOrderAt_comp_smul f (triangleMatrixLift g).val z

/-- An invariant function has the same ambient analytic order at every
point of an actual triangle orbit. -/
theorem triangle_invariant_analyticOrderAt (f : ℍ → ℂ)
    (hf : ∀ (g : TriangleGroup) (z : ℍ), f (triangleGeometricRepresentation g z) = f z)
    (g : TriangleGroup) (z : ℍ) :
    analyticOrderAt (f ∘ ofComplex) (triangleGeometricRepresentation g z : ℂ) =
      analyticOrderAt (f ∘ ofComplex) (z : ℂ) := by
  have he : (fun w : ℂ => f (triangleGeometricRepresentation g (ofComplex w))) =
      f ∘ ofComplex := by
    funext w
    exact hf g (ofComplex w)
  have h := triangle_analyticOrderAt_comp_action f g z
  rw [he] at h
  exact h.symm

/-- The quotient coordinate has exact order three or four in the original
ambient complex germ at every translate of its elliptic center. -/
theorem ellipticFullChart_order_translated_center (j : Elliptic.Kind) (g : TriangleGroup) :
    analyticOrderAt (ellipticFullChart j ∘ triangleOrbitProjection ∘ ofComplex)
      (triangleGeometricRepresentation g (ellipticCenter j) : ℂ) = (j.order : ℕ∞) := by
  exact (triangle_invariant_analyticOrderAt (ellipticFullChart j ∘ triangleOrbitProjection)
    (by intro h z; simp only [Function.comp_apply, triangleOrbitProjection_smul])
    g (ellipticCenter j)).trans (ellipticFullChart_order_center j)

/-- The translated ambient quotient-coordinate germs are genuinely analytic. -/
theorem ellipticFullChart_complexGerm_analyticAt_translated_center
    (j : Elliptic.Kind) (g : TriangleGroup) :
    AnalyticAt ℂ (ellipticFullChart j ∘ triangleOrbitProjection ∘ ofComplex)
      (triangleGeometricRepresentation g (ellipticCenter j) : ℂ) := by
  apply (analyticOrderAt_ne_zero.mp ?_).1
  rw [ellipticFullChart_order_translated_center]
  exact_mod_cast j.order_pos.ne'

/-- Every translate of the first elliptic center has exact branching order three. -/
theorem ellipticFullChart_order_translated_centerOne (g : TriangleGroup) :
    analyticOrderAt (ellipticFullChart .three ∘ triangleOrbitProjection ∘ ofComplex)
      (triangleGeometricRepresentation g centerOne : ℂ) = 3 :=
  ellipticFullChart_order_translated_center .three g

/-- Every translate of the second elliptic center has exact branching order four. -/
theorem ellipticFullChart_order_translated_centerTwo (g : TriangleGroup) :
    analyticOrderAt (ellipticFullChart .four ∘ triangleOrbitProjection ∘ ofComplex)
      (triangleGeometricRepresentation g centerTwo : ℂ) = 4 :=
  ellipticFullChart_order_translated_center .four g

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
