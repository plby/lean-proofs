import Wikipedia.NoExoticSixSphere.PartialFrameConnectivity
import Wikipedia.NoExoticSixSphere.SphereCubeHomotopy
import Wikipedia.NoExoticSixSphere.SphereDiskExtension
import Wikipedia.NoExoticSixSphere.ProjectionDiskFrame
import Wikipedia.NoExoticSixSphere.PartialFrameRangeCoordinates

/-!
# Exact three-sphere frame extension with complement dimension at least four

The native cubical connectivity theorem contracts the original sphere map,
and the actual disk-cone construction retains its full boundary. For a
varying projection family, construct a full orthonormal range frame on the
disk, extend the extracted boundary coordinates, and reconstruct in the
same original subspaces. No trivialization or extension is assumed.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization DiskBoundary
open Wikipedia.HopfProblem.DegreeCollapse

theorem sphereThree_extends_of_complement {c : ℕ} (hc : 3 < c) (n : ℕ)
    (f : C(Sphere 3, Space (c + n) n)) : Extends f :=
  (DiskBoundary.exists_extension_iff (SphereCube.point 3) f).mpr
    ((SphereCubeHomotopy.basedCube_nullhomotopic_iff (by decide : 0 < 3) f).mp
      (genLoop_homotopic_const_of_lt hc n (f (SphereCube.point 3)) (SphereCube.basedCube f)))

namespace ProjectionDisk

open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

theorem exists_partialFrame_extension_of_complement {N c n : ℕ} (hc : 3 < c)
    (P : C(Disk (E := Vector 4), Vector N →L[ℝ] Vector N))
    (hP : ∀ x, IsIdempotentElem (P x))
    (hr : Module.finrank ℝ (P center).range = c + n)
    (a : C(NoExoticSixSphere.Sphere 3, Space N n))
    (ha : ∀ s, (a s).val.range ≤ (P (boundaryToDisk s)).range) :
    ∃ A : C(Disk (E := Vector 4), Space N n),
      (∀ x, (A x).val.range ≤ (P x).range) ∧ ∀ s, A (boundaryToDisk s) = a s := by
  obtain ⟨t, ht⟩ := exists_frame P hP hr
  have hat (s : NoExoticSixSphere.Sphere 3) :
      (a s).val.range ≤ (t (boundaryToDisk s)).val.range :=
    (ha s).trans_eq (ht (boundaryToDisk s)).symm
  let b := RangeCoordinates.map (t.comp boundaryToDisk) a hat
  obtain ⟨F, hF⟩ := sphereThree_extends_of_complement hc n b
  let A : C(Disk (E := Vector 4), Space N n) :=
    ⟨fun x ↦ Stiefel.comp (t x) (F x), continuous_comp t F t.continuous F.continuous⟩
  refine ⟨A, fun x ↦ (RangeCoordinates.range_comp_le (t x) (F x)).trans_eq (ht x), ?_⟩
  intro s
  change Stiefel.comp (t (boundaryToDisk s)) (F (boundaryToDisk s)) = a s
  rw [hF s]
  exact RangeCoordinates.comp_extract _ _ (hat s)

end ProjectionDisk

end NoExoticSixSphere.Stiefel
