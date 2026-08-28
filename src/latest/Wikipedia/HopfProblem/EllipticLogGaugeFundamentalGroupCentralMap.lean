import Wikipedia.HopfProblem.EllipticEquivariantCentralTopologyGroups

/-!
# The central retraction on actual flat-coordinate representatives

The radial retraction removes only the disc coordinate.  This formula
connects actual noncentral attaching paths to the genuine affine universal
cover of the central surface, without choosing any basepoint-change path.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual central-surface retraction retains the flat real coordinate. -/
theorem fillingSurfaceRetraction_quotient_flat (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (x : RealCoordinates) :
    D.fillingSurfaceRetraction v hv (D.quotient v hv (z, standardLattice.mkQ x)) =
      affineCoverProjection j D.centralPeriod v hv x := by
  apply D.centralFibreInclusion_injective v hv
  have h := congrArg (fun f : C(D.Space v hv, D.Space v hv) =>
      f (D.quotient v hv (z, standardLattice.mkQ x)))
    (D.surfaceIntoFilling_comp_retraction v hv)
  change D.centralFibreInclusion v hv
      (D.fillingSurfaceRetraction v hv (D.quotient v hv (z, standardLattice.mkQ x))) =
    D.fillingRadial v hv 1 (D.quotient v hv (z, standardLattice.mkQ x)) at h
  rw [h, D.fillingRadial_quotient, discRadial_one]
  change D.quotient v hv (Elliptic.discZero, standardLattice.mkQ x) =
    D.centralFibreInclusion v hv
      (surfaceProjection j D.centralPeriod v hv (flatProjection D.centralPeriod.val x))
  rw [D.centralFibreInclusion_surfaceProjection, D.centralInclusion_flatProjection]
  rfl

end Wikipedia.HopfProblem.Elliptic.LogGauge
