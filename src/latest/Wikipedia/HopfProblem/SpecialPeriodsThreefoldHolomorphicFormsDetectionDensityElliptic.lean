import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticGeometry

/-!
# Density away from the central fibres of the actual elliptic pieces

Nonzero root coordinates are dense in the actual disc-times-torus family.
The continuous surjective affine quotient carries these points to nonzero
power coordinates. Restricting to the literal open small filling gives
the required density without changing any topology or complex atlas.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.DetectionDensity

open Elliptic EllipticFilling

private theorem fullFilling_parameter_ne_zero_dense (j : Kind) :
    Dense {x : SpecialFullFilling j | (specialFullFillingProjection j x : ℂ) ≠ 0} := by
  have hup : Dense {x : (specialLocalData j).TotalSpace | (x.1 : ℂ) ≠ 0} :=
    (dense_compl_singleton (0 : ℂ)).preimage
      (unitDisc.isOpen.isOpenMap_subtype_val.comp isOpenMap_fst)
  have hq := ((specialLocalData j).quotient_surjective j.twist
    (mainTwist_admissible j)).denseRange
  refine hq.dense_of_mapsTo
      ((specialLocalData j).quotient_continuous j.twist (mainTwist_admissible j)) hup ?_
  intro x hx
  change (x.1 : ℂ) ^ j.order ≠ 0
  exact pow_ne_zero _ hx

/-- Nonzero parameters are dense on each actual small elliptic filling. -/
theorem elliptic_parameter_ne_zero_dense (j : Kind) :
    Dense {x : EllipticGeometry.LocalSpace j | EllipticGeometry.parameter j x ≠ 0} := by
  exact (fullFilling_parameter_ne_zero_dense j).preimage
    (pieceDomain specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
      specialBaseCover j).isOpen.isOpenMap_subtype_val

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.DetectionDensity
