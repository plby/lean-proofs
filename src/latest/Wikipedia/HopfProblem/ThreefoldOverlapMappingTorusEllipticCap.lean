import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticSpecial
import Wikipedia.HopfProblem.EllipticEquivariantCentralTopologySurface

/-!
# The actual elliptic boundary map after central-fibre retraction

The real flat coordinate survives the original radial deformation.
Consequently the map from the boundary mapping torus to the genuine
central surface is exactly its original affine finite quotient map.
This is a formula for actual continuous maps, not an assigned homology matrix.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.EllipticFilling
open Wikipedia.HopfProblem.Elliptic

/-- The boundary map with values in the whole original varying-period filling. -/
def specialBoundaryToFullFilling (j : Kind) : C(SpecialBoundary j, SpecialFullFilling j) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
    C(SpecialEllipticPiece j, SpecialFullFilling j)).comp (specialBoundaryToPiece j)

/-- The actual central affine surface, at the original special central period. -/
abbrev BoundaryCentralSurface (j : Kind) :=
  Surface j (specialLocalData j).centralPeriod j.twist (mainTwist_admissible j)

/-- Retract the actual boundary in the actual varying-period filling. -/
def specialBoundaryToCentral (j : Kind) : C(SpecialBoundary j, BoundaryCentralSurface j) :=
  ((specialLocalData j).fillingSurfaceRetraction j.twist (mainTwist_admissible j)).comp
    (specialBoundaryToFullFilling j)

theorem centralInclusion_surfaceRetraction {j : Kind} (D : Equivariant.Data j)
    (v : Lattice) (hv : AdmissibleTwist j v) (y : D.Space v hv) :
    D.centralFibreInclusion v hv (D.fillingSurfaceRetraction v hv y) =
      D.fillingRadial v hv 1 y :=
  congrArg (fun f : C(D.Space v hv, D.Space v hv) => f y)
    (D.surfaceIntoFilling_comp_retraction v hv)

/-- On every real period representative, the cap map forgets only the angle. -/
theorem specialBoundaryToCentral_realCoordinates (j : Kind) (t : ℝ) (x : RealCoordinates) :
    specialBoundaryToCentral j
        (MappingTorus.mk (flatTorusAffine j j.twist) (t, standardLattice.mkQ x)) =
      surfaceProjection j (specialLocalData j).centralPeriod j.twist (mainTwist_admissible j)
        (flatProjection (specialLocalData j).centralPeriod.val x) := by
  let y : (specialLocalData j).Space j.twist (mainTwist_admissible j) :=
    specialBoundaryToFullFilling j
      (MappingTorus.mk (flatTorusAffine j j.twist) (t, standardLattice.mkQ x))
  have hy : y = (specialLocalData j).quotient j.twist (mainTwist_admissible j)
      (root j.order (specialBaseCover.radius (some j)) (specialRootRadius j)
        ((t / j.order : ℝ) : Circle), standardLattice.mkQ x) :=
    specialBoundaryInclusion_mk j t (standardLattice.mkQ x)
  apply (specialLocalData j).centralFibreInclusion_injective j.twist (mainTwist_admissible j)
  change (specialLocalData j).centralFibreInclusion j.twist (mainTwist_admissible j)
    ((specialLocalData j).fillingSurfaceRetraction j.twist (mainTwist_admissible j) y) = _
  rw [centralInclusion_surfaceRetraction, hy,
    Equivariant.Data.fillingRadial_quotient, discRadial_one,
    Equivariant.Data.centralFibreInclusion_surfaceProjection,
    Equivariant.Data.centralInclusion_flatProjection]
  rfl

/-- The same exact formula on the original real-period torus, without choosing a lift. -/
theorem specialBoundaryToCentral_mk (j : Kind) (t : ℝ) (x : RealTorus₄) :
    specialBoundaryToCentral j (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      surfaceProjection j (specialLocalData j).centralPeriod j.twist (mainTwist_admissible j)
        (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val x) := by
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  rw [flatTorusPeriodHomeomorph_mkQ]
  exact specialBoundaryToCentral_realCoordinates j t u

/-- The cap map is independent of the boundary angle on every actual representative. -/
theorem specialBoundaryToCentral_angle (j : Kind) (t s : ℝ) (x : RealTorus₄) :
    specialBoundaryToCentral j (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      specialBoundaryToCentral j (MappingTorus.mk (flatTorusAffine j j.twist) (s, x)) := by
  rw [specialBoundaryToCentral_mk, specialBoundaryToCentral_mk]

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic
