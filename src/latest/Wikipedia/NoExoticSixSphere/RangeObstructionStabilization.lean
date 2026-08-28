import Wikipedia.NoExoticSixSphere.PartialFrameBlockRanges
import Wikipedia.NoExoticSixSphere.PartialFrameRangeObstruction

/-!
# Stabilizing the full and partial frames preserves the range obstruction

The actual adjoint-extracted boundary coordinates commute with ordinary
block stabilization. Applying the checked five-column sphere-parity theorem
therefore compares the range obstructions in those exact coordinates.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.RangeObstruction

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

theorem parity_block_five {N : ℕ} (r : ℕ)
    (t : C(Disk (E := Vector 4), Space N (3 + (r + 2))))
    (a : C(NoExoticSixSphere.Sphere 3, Space N (r + 2)))
    (ha : ∀ s, (a s).val.range ≤ (t (boundaryToDisk s)).val.range) :
    parity (r + 5) ((BlockSum.map 5).comp t) ((BlockSum.map 5).comp a)
        (fun s ↦ BlockSum.range_frame_mono 5 (t (boundaryToDisk s)) (a s) (ha s)) =
      parity r t a ha := by
  have he : boundaryCoordinates (r + 5) ((BlockSum.map 5).comp t) ((BlockSum.map 5).comp a)
      (fun s ↦ BlockSum.range_frame_mono 5 (t (boundaryToDisk s)) (a s) (ha s)) =
        (BlockSum.map 5).comp (boundaryCoordinates r t a ha) := by
    apply ContinuousMap.ext
    intro s
    exact BlockSum.extract_frame 5 (t (boundaryToDisk s)) (a s) (ha s)
  change sphereThirdObstruction (r + 5) _ = sphereThirdObstruction r _
  rw [he, BlockSum.sphere_parity_five]

end NoExoticSixSphere.Stiefel.RangeObstruction
