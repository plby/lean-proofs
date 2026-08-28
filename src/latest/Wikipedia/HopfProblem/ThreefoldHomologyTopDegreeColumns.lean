import Wikipedia.HopfProblem.ThreefoldHomologyTopDegreeBoundaryCoordinates
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticSourceProjection

/-!
# The two actual elliptic columns are an isomorphism in degree five

The proved native boundary comparison identifies the genuine Wang
classes with the first and second source-kernel coordinates.  In this
top degree the regular source projection and both Wang maps themselves
are isomorphisms.  Thus the literal sum of the two original elliptic
overlap inclusions is an isomorphism, with no chosen projective splitting.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopDegree

open SingularMayerVietoris PeriodTorusHigherHomology ThreefoldOverlapMappingTorus

/-- The actual order-three boundary occupies the first canonical regular coordinate. -/
theorem boundaryThree_fifth_column (a : SingularHomology (Boundary (some .three)) 5) :
    regularFifthEquiv (boundaryRegularHomologyMap (some .three) 5 a) =
      (boundaryFifthEquiv (some .three) a, 0) := by
  rw [regularFifthEquiv_apply, boundaryFifthEquiv_apply]
  have h := congrArg
    (fun p : SingularHomology RealTorus₄ 4 × SingularHomology RealTorus₄ 4 =>
      (realTorusH4Equiv p.1, realTorusH4Equiv p.2))
    (TrianglePeriodFamily.Boundary.ellipticThreeBoundary_sourceKernelProjection 4 a)
  simpa only [map_zero, monodromy] using! h

/-- The actual order-four boundary occupies the second canonical regular coordinate. -/
theorem boundaryFour_fifth_column (a : SingularHomology (Boundary (some .four)) 5) :
    regularFifthEquiv (boundaryRegularHomologyMap (some .four) 5 a) =
      (0, boundaryFifthEquiv (some .four) a) := by
  rw [regularFifthEquiv_apply, boundaryFifthEquiv_apply]
  have h := congrArg
    (fun p : SingularHomology RealTorus₄ 4 × SingularHomology RealTorus₄ 4 =>
      (realTorusH4Equiv p.1, realTorusH4Equiv p.2))
    (TrianglePeriodFamily.Boundary.ellipticFourBoundary_sourceKernelProjection 4 a)
  simpa only [map_zero, monodromy] using! h

/-- Transfer the first actual boundary column to the literal original intersection. -/
theorem overlapThree_fifth_column (a : SingularHomology (RegularOverlap (some .three)) 5) :
    regularFifthEquiv (singularHomologyMap (overlapToRegularFamily (some .three)) 5 a) =
      (overlapFifthEquiv (some .three) a, 0) := by
  have h := LinearMap.congr_fun (boundaryRegularHomologyMap_retraction (some .three) 5) a
  change boundaryRegularHomologyMap (some .three) 5
    (overlapHomologyEquiv (some .three) 5 a) =
      singularHomologyMap (overlapToRegularFamily (some .three)) 5 a at h
  rw [overlapFifthEquiv_apply, ← h]
  exact boundaryThree_fifth_column _

/-- Transfer the second actual boundary column to the literal original intersection. -/
theorem overlapFour_fifth_column (a : SingularHomology (RegularOverlap (some .four)) 5) :
    regularFifthEquiv (singularHomologyMap (overlapToRegularFamily (some .four)) 5 a) =
      (0, overlapFifthEquiv (some .four) a) := by
  have h := LinearMap.congr_fun (boundaryRegularHomologyMap_retraction (some .four) 5) a
  change boundaryRegularHomologyMap (some .four) 5
    (overlapHomologyEquiv (some .four) 5 a) =
      singularHomologyMap (overlapToRegularFamily (some .four)) 5 a at h
  rw [overlapFifthEquiv_apply, ← h]
  exact boundaryFour_fifth_column _

/-- The complete genuine two-column square commutes. -/
theorem ellipticAttachmentFifth_coordinates (a : EllipticOverlapFifth) :
    regularFifthEquiv (ellipticAttachmentFifth a) = ellipticFifthCoordinates a := by
  classical
  rw [ellipticAttachmentFifth_apply, map_sum]
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four),
    overlapThree_fifth_column, overlapFour_fifth_column, ellipticFifthCoordinates_apply]
  exact Prod.ext (add_zero _) (zero_add _)

/-- The actual sum of the two original elliptic overlap maps is an isomorphism. -/
def ellipticAttachmentFifthEquiv :
    EllipticOverlapFifth ≃ₗ[ℤ] SingularHomology SpecialRegularFamily 5 :=
  ellipticFifthCoordinates.trans regularFifthEquiv.symm

/-- The constructed equivalence is exactly the actual attaching homomorphism. -/
theorem ellipticAttachmentFifthEquiv_toLinearMap :
    ellipticAttachmentFifthEquiv.toLinearMap = ellipticAttachmentFifth := by
  apply LinearMap.ext
  intro a
  apply regularFifthEquiv.injective
  change regularFifthEquiv (regularFifthEquiv.symm (ellipticFifthCoordinates a)) = _
  rw [LinearEquiv.apply_symm_apply, ellipticAttachmentFifth_coordinates]

theorem ellipticAttachmentFifth_bijective : Function.Bijective ellipticAttachmentFifth := by
  rw [← ellipticAttachmentFifthEquiv_toLinearMap]
  exact ellipticAttachmentFifthEquiv.bijective

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopDegree
