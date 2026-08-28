import Wikipedia.NoExoticSixSphere.JamesSphereRoundCellCoordinates
import Wikipedia.NoExoticSixSphere.RoundDiskNativeSuspension
import Wikipedia.NoExoticSixSphere.DiskMapInterpolation
import Wikipedia.NoExoticSixSphere.BasedHomotopyNativeMap

/-!
# Comparing the original and round James-cell contractions

The two disk families have identical endpoints and agree on the entire
basepoint line. Interpolating inside the actual max-norm disk therefore
gives a based homotopy of their quotient-loop families. No change of
basepoint or unproved equality of suspension conventions is used.
-/

noncomputable section

open Set
open scoped Topology unitInterval
open Wikipedia.HopfProblem.DegreeCollapse

namespace NoExoticSixSphere.JamesSphere.RoundCell

def straightCurve (n : ℕ) (hn : 0 < n) :
    C(unitInterval × Sphere (sphereDimension n),
      DiskCylinder.Disk (E := CellBoundary.Coordinates n)) :=
  (DiskBoundary.segment (CellBoundary.cornerDisk n)).comp
    ⟨fun p ↦ (p.1, DiskCylinder.boundaryToDisk (boundaryHomeomorph n hn p.2)),
      continuous_fst.prodMk (DiskCylinder.boundaryToDisk.continuous.comp
        ((boundaryHomeomorph n hn).continuous.comp continuous_snd))⟩

def roundCurve (n : ℕ) (hn : 0 < n) :
    C(unitInterval × Sphere (sphereDimension n),
      DiskCylinder.Disk (E := CellBoundary.Coordinates n)) :=
  (diskCoordinates n hn : C(_, _)).comp
    ((RoundDiskBoundarySegments.point
      (parameterHomeomorph n hn (spherePole (sphereDimension n)))).comp
        (Homeomorph.prodCongr (Homeomorph.refl unitInterval) (parameterHomeomorph n hn) : C(_, _)))

theorem straightCurve_zero (n : ℕ) (hn : 0 < n) (s : Sphere (sphereDimension n)) :
    straightCurve n hn (0, s) = DiskCylinder.boundaryToDisk (boundaryHomeomorph n hn s) :=
  DiskBoundary.segment_zero _ _

theorem straightCurve_one (n : ℕ) (hn : 0 < n) (s : Sphere (sphereDimension n)) :
    straightCurve n hn (1, s) = CellBoundary.cornerDisk n :=
  DiskBoundary.segment_one _ _

theorem straightCurve_pole (n : ℕ) (hn : 0 < n) (t : unitInterval) :
    straightCurve n hn (t, spherePole (sphereDimension n)) = CellBoundary.cornerDisk n := by
  change DiskBoundary.segment (CellBoundary.cornerDisk n)
    (t, DiskCylinder.boundaryToDisk (boundaryHomeomorph n hn (spherePole (sphereDimension n)))) = _
  rw [boundaryHomeomorph_pole, CellBoundary.boundary_corner, DiskBoundary.segment_fixed]

theorem roundCurve_zero (n : ℕ) (hn : 0 < n) (s : Sphere (sphereDimension n)) :
    roundCurve n hn (0, s) = DiskCylinder.boundaryToDisk (boundaryHomeomorph n hn s) := by
  change diskCoordinates n hn (RoundDiskBoundarySegments.point
    (parameterHomeomorph n hn (spherePole (sphereDimension n)))
      (0, parameterHomeomorph n hn s)) = _
  rw [RoundDiskBoundarySegments.point_zero, disk_boundary_parameter]

theorem roundCurve_one (n : ℕ) (hn : 0 < n) (s : Sphere (sphereDimension n)) :
    roundCurve n hn (1, s) = CellBoundary.cornerDisk n := by
  change diskCoordinates n hn (RoundDiskBoundarySegments.point
    (parameterHomeomorph n hn (spherePole (sphereDimension n)))
      (1, parameterHomeomorph n hn s)) = _
  rw [RoundDiskBoundarySegments.point_one, parameterHomeomorph_pole, disk_corner]

theorem roundCurve_pole (n : ℕ) (hn : 0 < n) (t : unitInterval) :
    roundCurve n hn (t, spherePole (sphereDimension n)) = CellBoundary.cornerDisk n := by
  change diskCoordinates n hn (RoundDiskBoundarySegments.point
    (parameterHomeomorph n hn (spherePole (sphereDimension n)))
      (t, parameterHomeomorph n hn (spherePole (sphereDimension n)))) = _
  rw [RoundDiskBoundarySegments.point_base, parameterHomeomorph_pole, disk_corner]

def protectedSet (n : ℕ) : Set (unitInterval × Sphere (sphereDimension n)) :=
  {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = spherePole (sphereDimension n)}

theorem curves_eqOn (n : ℕ) (hn : 0 < n) :
    EqOn (straightCurve n hn) (roundCurve n hn) (protectedSet n) := by
  rintro ⟨t, s⟩ (ht | ht | hs)
  · change t = 0 at ht
    subst t
    rw [straightCurve_zero, roundCurve_zero]
  · change t = 1 at ht
    subst t
    rw [straightCurve_one, roundCurve_one]
  · change s = spherePole (sphereDimension n) at hs
    subst s
    rw [straightCurve_pole, roundCurve_pole]

def loopHomotopy (n : ℕ) (hn : 0 < n) :
    ((CellBoundary.sphereLoops n hn).comp (boundaryHomeomorph n hn : C(_, _))).HomotopyRel
      (RoundDiskCubicalSuspension.loops (quotient n hn) (spherePole (n + n))
        (quotient_base n hn) (parameterHomeomorph n hn)) {spherePole (sphereDimension n)} :=
  PathFamilies.curryHomotopy
    ((DiskMapInterpolation.homotopyRel (straightCurve n hn) (roundCurve n hn)
      (protectedSet n) (curves_eqOn n hn)).compContinuousMap (maxQuotient n))

theorem quotientHom_comparison (n : ℕ) (hn : 0 < n) (d : ℕ) [NeZero d]
    (c : π_ d (Sphere (sphereDimension n)) (spherePole (sphereDimension n))) :
    CellBoundary.quotientHom n hn d
      (HigherHomotopy.map (N := Fin d)
        (boundaryHomeomorph n hn : C(Sphere (sphereDimension n), CellBoundary.Boundary n))
        (boundaryHomeomorph_pole n hn) c) =
      RoundDiskCubicalSuspension.hom (quotient n hn) (spherePole (n + n))
        (quotient_base n hn) (parameterHomeomorph n hn) d c := by
  rw [CellBoundary.quotientHom_eq_currying, HigherHomotopy.map_comp]
  apply congrArg (GeneralizedLoopCurrying.homotopyMulEquiv d (spherePole (n + n)))
  exact HigherHomotopy.map_eq_of_based_homotopy _ _ _ _ (loopHomotopy n hn) c

end NoExoticSixSphere.JamesSphere.RoundCell
