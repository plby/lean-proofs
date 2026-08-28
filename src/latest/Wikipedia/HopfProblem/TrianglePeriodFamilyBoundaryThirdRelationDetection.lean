import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationNegation
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyGroups

/-!
# Genuine fibre-negation detection of the horizontal third-degree class

The actual regular-family source sequence places every zero-source
class in the literal fibre image.  Negation is minus one on that image.
Consequently a class fixed by the actual involution and with zero source
is zero, since the already computed original homology is torsion-free.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology Homology

variable (D : Data ℂ TriangleRegularPoint)

/-- The actual source sequence and the actual fibre involution detect the horizontal remainder. -/
theorem negation_fixed_source_zero (a : SingularHomology D.Space 3)
    (hneg : singularHomologyMap (familyNegation D) 3 a = a)
    (hsource : sourceKernelProjection D 2 a = 0) : a = 0 := by
  have ha : a ∈ LinearMap.range
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 3) := by
    rw [← sourceKernelProjection_kernel D 2]
    exact hsource
  obtain ⟨b, hb⟩ := ha
  have hminus : singularHomologyMap (familyNegation D) 3 a = -a := by
    rw [← hb]
    exact familyNegation_homology_fibre_three D normalizedSlitBaseLift b
  have heq : a = -a := hneg.symm.trans hminus
  apply (familyH3Equiv D).injective
  rw [map_zero]
  ext i
  have hi := congrArg (fun x => familyH3Equiv D x i) heq
  simp only [map_neg, Pi.neg_apply] at hi
  change familyH3Equiv D a i = 0
  omega

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
