import Wikipedia.NoExoticSixSphere.PartialFrameThirdObstruction
import Wikipedia.NoExoticSixSphere.SphereCubeHomotopy
import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy

/-!
# Exact four-ball extension detected by the actual frame-sphere parity

Pull the given map on the Euclidean three-sphere back along the actual cube
quotient and evaluate its proved native parity. The value vanishes precisely
when the original sphere map extends continuously over the closed four-ball
with unchanged boundary values. Free homotopy and adding a column preserve it.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse

def sphereThirdObstruction (r : ℕ) (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) : ZMod 2 :=
  thirdObstruction r (f (SphereCube.point 3)) (SphereCube.basedCube f)

theorem sphereThirdObstruction_zero_iff (r : ℕ)
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction r f = 0 ↔
      f.HomotopicRel (ContinuousMap.const _ (f (SphereCube.point 3))) {SphereCube.point 3} := by
  unfold sphereThirdObstruction
  rw [thirdObstruction_zero_iff]
  exact SphereCubeHomotopy.basedCube_nullhomotopic_iff (by decide : 0 < 3) f

theorem sphereThirdObstruction_zero_iff_extension (r : ℕ)
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction r f = 0 ↔
      ∃ F : C(DiskCylinder.Disk (E := Vector 4), Space (3 + (r + 2)) (r + 2)),
        ∀ s, F (DiskCylinder.boundaryToDisk s) = f s :=
  (sphereThirdObstruction_zero_iff r f).trans
    (DiskBoundary.exists_extension_iff (SphereCube.point 3) f).symm

theorem sphereThirdObstruction_homotopic (r : ℕ)
    {f g : C(Sphere 3, Space (3 + (r + 2)) (r + 2))} (h : f.Homotopic g) :
    sphereThirdObstruction r f = sphereThirdObstruction r g := by
  apply zmodTwo_eq_of_zero_iff
  rw [sphereThirdObstruction_zero_iff_extension, sphereThirdObstruction_zero_iff_extension]
  constructor
  · rintro ⟨F, hF⟩
    exact DiskBoundary.exists_extension_of_homotopic h F hF
  · rintro ⟨G, hG⟩
    exact DiskBoundary.exists_extension_of_homotopic h.symm G hG

theorem sphereThirdObstruction_reconstruction (r : ℕ)
    (v : UnitSphere (Vector ((r + 2) + 1)))
    (c : UnitSphere (Vector ((3 + (r + 2)) + 1)))
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction (r + 1) ((ColumnFiber.reconstructionMap v c).comp f) =
      sphereThirdObstruction r f :=
  thirdObstruction_reconstruction r v c (f (SphereCube.point 3)) (SphereCube.basedCube f)

end NoExoticSixSphere.Stiefel
