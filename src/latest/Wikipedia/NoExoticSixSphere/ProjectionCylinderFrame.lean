import Wikipedia.NoExoticSixSphere.ProjectionContractionFrame

/-!
# A simultaneous normal-frame trivialization on a disk homotopy

The parameter interval times the actual closed four-ball contracts to its
zero-time center. Applying projection transport to that contraction gives
one full frame continuous in both the parameter and the disk point.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ProjectionCylinder

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

abbrev Base := unitInterval × Disk (E := Vector 4)

def contraction : (ContinuousMap.id Base).Homotopy
    (ContinuousMap.const Base ((0 : unitInterval), ProjectionDisk.center)) where
  toFun p := (unitInterval.symm p.1 * p.2.1,
    DiskBoundary.segment ProjectionDisk.center (p.1, p.2.2))
  continuous_toFun :=
    ((unitInterval.continuous_symm.comp continuous_fst).mul
      (continuous_fst.comp continuous_snd)).prodMk
        ((DiskBoundary.segment ProjectionDisk.center).continuous.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left p := by
    apply Prod.ext
    · simp
    · exact DiskBoundary.segment_zero ProjectionDisk.center p.2
  map_one_left p := by
    apply Prod.ext
    · simp
    · exact DiskBoundary.segment_one ProjectionDisk.center p.2

theorem exists_frame {N n : ℕ} (P : C(Base, Vector N →L[ℝ] Vector N))
    (hP : ∀ x, IsIdempotentElem (P x))
    (hr : Module.finrank ℝ (P (0, ProjectionDisk.center)).range = n) :
    ∃ t : C(Base, Space N n), ∀ x, (t x).val.range = (P x).range :=
  exists_projectionFrame_of_contraction (0, ProjectionDisk.center) contraction P hP hr

end NoExoticSixSphere.Stiefel.ProjectionCylinder
