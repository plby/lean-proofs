import Wikipedia.NoExoticSixSphere.ProjectionDiskFrame
import Wikipedia.NoExoticSixSphere.PartialFrameRangeObstruction

/-!
# Intrinsic partial-frame obstruction for a projection family on the four-ball

Construct an orthonormal trivialization using the proved disk transport,
then evaluate the genuine sphere-map parity. Its value agrees with that
from every other orthonormal trivialization. Vanishing is equivalent to
extension of the original ambient partial frame inside the original ranges.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ProjectionObstruction

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {N : ℕ} (r : ℕ)
variable (P : C(Disk (E := Vector 4), Vector N →L[ℝ] Vector N))
variable (hP : ∀ x, IsIdempotentElem (P x))
variable (hr : Module.finrank ℝ (P ProjectionDisk.center).range = 3 + (r + 2))

def chosenFrame : C(Disk (E := Vector 4), Space N (3 + (r + 2))) :=
  (ProjectionDisk.exists_frame P hP hr).choose

theorem chosenFrame_range (x : Disk (E := Vector 4)) :
    (chosenFrame r P hP hr x).val.range = (P x).range :=
  (ProjectionDisk.exists_frame P hP hr).choose_spec x

variable (a : C(NoExoticSixSphere.Sphere 3, Space N (r + 2)))
variable (ha : ∀ s, (a s).val.range ≤ (P (boundaryToDisk s)).range)

include ha in
theorem boundary_range (s : NoExoticSixSphere.Sphere 3) :
    (a s).val.range ≤ (chosenFrame r P hP hr (boundaryToDisk s)).val.range :=
  (ha s).trans_eq (chosenFrame_range r P hP hr (boundaryToDisk s)).symm

def parity : ZMod 2 :=
  RangeObstruction.parity r (chosenFrame r P hP hr) a (boundary_range r P hP hr a ha)

theorem parity_zero_iff_extension : parity r P hP hr a ha = 0 ↔
    ∃ A : C(Disk (E := Vector 4), Space N (r + 2)),
      (∀ x, (A x).val.range ≤ (P x).range) ∧ ∀ s, A (boundaryToDisk s) = a s := by
  change RangeObstruction.parity r (chosenFrame r P hP hr) a _ = 0 ↔ _
  rw [RangeObstruction.parity_zero_iff_extension]
  simp only [chosenFrame_range]

theorem parity_eq_of_trivialization
    (t : C(Disk (E := Vector 4), Space N (3 + (r + 2))))
    (ht : ∀ x, (t x).val.range = (P x).range)
    (hat : ∀ s, (a s).val.range ≤ (t (boundaryToDisk s)).val.range) :
    parity r P hP hr a ha = RangeObstruction.parity r t a hat :=
  RangeObstruction.parity_independent_of_trivialization r (chosenFrame r P hP hr) a
    (boundary_range r P hP hr a ha) t
      (fun x ↦ (chosenFrame_range r P hP hr x).trans (ht x).symm) hat

end NoExoticSixSphere.Stiefel.ProjectionObstruction
