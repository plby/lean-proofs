import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusQuotient
import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusMonodromy
import Wikipedia.HopfProblem.EllipticSurfaces

/-!
# The actual elliptic quotient surface is the explicit mapping torus

The verified integral period-coordinate splitting conjugates the actual
affine elliptic generator to the finite circle-fibre twist.  Descending that
literal conjugacy and composing with the proved finite-quotient mapping-torus
homeomorphism identifies every actual fixed-period surface with its concrete
inverse-monodromy mapping torus.  The formulas retain the original real
period representatives and both directions of the quotient map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open PeriodTorusHigherHomology MappingTorusQuotient

/-- The finite product quotient for the actual elliptic fibre map. -/
abbrev surfaceProductQuotient (j : Kind) :=
  ProductQuotient j.order (fibreTorusHomeomorph j) (fibreTorusHomeomorph_pow_order j)

/-- The proved period-coordinate conjugacy descends to the actual
surface orbit quotient, with its existing quotient topology. -/
def surfaceSplitQuotientHomeomorph (j : Kind) (p : FixedPeriod j) :
    Surface j p j.twist (mainTwist_admissible j) ≃ₜ surfaceProductQuotient j :=
  cyclicQuotientCongr (affinePermutation j p j.twist)
    (affinePermutation_pow_order j p j.twist j.matrix_fixes_twist)
    (twist j.order (fibreTorusHomeomorph j)).toEquiv
    (twistPerm_pow_order j.order (fibreTorusHomeomorph j)
      (fibreTorusHomeomorph_pow_order j))
    (splitPeriodTorusHomeomorph j p.val)
    (fun x => splitPeriodTorusHomeomorph_affineBiholomorph j p x)

@[simp] theorem surfaceSplitQuotientHomeomorph_projection (j : Kind) (p : FixedPeriod j)
    (x : p.val.Torus) :
    surfaceSplitQuotientHomeomorph j p
      (surfaceProjection j p j.twist (mainTwist_admissible j) x) =
        MappingTorusQuotient.project j.order (fibreTorusHomeomorph j)
          (fibreTorusHomeomorph_pow_order j) (splitPeriodTorusHomeomorph j p.val x) := rfl

@[simp] theorem surfaceSplitQuotientHomeomorph_symm_project (j : Kind) (p : FixedPeriod j)
    (x : MappingTorus.Circle × ProductTorus 3) :
    (surfaceSplitQuotientHomeomorph j p).symm
      (MappingTorusQuotient.project j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j) x) =
      surfaceProjection j p j.twist (mainTwist_admissible j)
        ((splitPeriodTorusHomeomorph j p.val).symm x) := rfl

/-- The genuine mapping-torus homeomorphism for the actual elliptic
surface and the source's specified admissible twist. -/
def surfaceMappingTorusHomeomorph (j : Kind) (p : FixedPeriod j) :
    Surface j p j.twist (mainTwist_admissible j) ≃ₜ mappingTorusModel j :=
  (surfaceSplitQuotientHomeomorph j p).trans
    (mappingTorusHomeomorph j.order (fibreTorusHomeomorph j)
      (fibreTorusHomeomorph_pow_order j))

/-- On the original split covering torus the time coordinate is
multiplied by the elliptic order. -/
theorem surfaceMappingTorusHomeomorph_splitPeriodTorus (j : Kind) (p : FixedPeriod j)
    (t : ℝ) (x : ProductTorus 3) :
    surfaceMappingTorusHomeomorph j p
      (surfaceProjection j p j.twist (mainTwist_admissible j)
        ((splitPeriodTorusHomeomorph j p.val).symm ((t : MappingTorus.Circle), x))) =
      MappingTorus.mk (fibreTorusHomeomorph j).symm (t * j.order, x) := by
  rw [surfaceMappingTorusHomeomorph, Homeomorph.trans_apply,
    surfaceSplitQuotientHomeomorph_projection, Homeomorph.apply_symm_apply,
    mappingTorusHomeomorph_project]

/-- The literal original real-period representative has the asserted
mapping-torus representative; no auxiliary quotient equivalence is assumed. -/
theorem surfaceMappingTorusHomeomorph_flatProjection (j : Kind) (p : FixedPeriod j)
    (x : RealCoordinates) :
    surfaceMappingTorusHomeomorph j p
      (surfaceProjection j p j.twist (mainTwist_admissible j) (flatProjection p.val x)) =
      MappingTorus.mk (fibreTorusHomeomorph j).symm
        ((splitRealCoordinates j x).1 * j.order,
          coordinateProjection 3 (splitRealCoordinates j x).2) := by
  rw [surfaceMappingTorusHomeomorph, Homeomorph.trans_apply,
    surfaceSplitQuotientHomeomorph_projection,
    splitPeriodTorusHomeomorph_flatProjection, mappingTorusHomeomorph_project]

/-- The inverse takes every actual mapping-torus representative to the
surface quotient of the split torus point with time divided by the order. -/
theorem surfaceMappingTorusHomeomorph_symm_mk (j : Kind) (p : FixedPeriod j)
    (t : ℝ) (x : ProductTorus 3) :
    (surfaceMappingTorusHomeomorph j p).symm
      (MappingTorus.mk (fibreTorusHomeomorph j).symm (t, x)) =
      surfaceProjection j p j.twist (mainTwist_admissible j)
        ((splitPeriodTorusHomeomorph j p.val).symm
          (((t / j.order : ℝ) : MappingTorus.Circle), x)) := by
  change (surfaceSplitQuotientHomeomorph j p).symm
    ((mappingTorusHomeomorph j.order (fibreTorusHomeomorph j)
      (fibreTorusHomeomorph_pow_order j)).symm
        (MappingTorus.mk (fibreTorusHomeomorph j).symm (t, x))) = _
  rw [mappingTorusHomeomorph_symm_mk, surfaceSplitQuotientHomeomorph_symm_project]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
