import Wikipedia.NoExoticSixSphere.IntegralSphereHomotopyClass
import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy

/-!
# Actual continuous disks from the integral boundary kernel

For a two-connected target, vanishing of the actual integral class of a
three-sphere is equivalent to an extension over the ordinary closed
four-ball with exactly the prescribed boundary map. Naturality applies
this to a sphere whose integral class is killed by an actual inclusion.

These are continuous disks, not smooth immersions. The integral kernel
is used deliberately; vanishing after reduction modulo two is not an
input sufficient for this Hurewicz argument.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.SmoothCube

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralSphereClass_comp (j : C(X, Y)) (f : C(Sphere 3, X)) :
    integralSphereClass (j.comp f) = singularHomologyMap j 3 (integralSphereClass f) := by
  unfold integralSphereClass
  rw [singularHomologyMap_comp]
  rfl

theorem integralSphereClass_zero_of_disk_extension
    (f : C(Sphere 3, X)) (F : C(Disk (E := Vector 4), X))
    (hb : ∀ s, F (boundaryToDisk s) = f s) : integralSphereClass f = 0 := by
  have he : F.comp boundaryToDisk = f := ContinuousMap.ext hb
  have h := (DiskBoundary.contraction F (spherePole 3)).toHomotopy
  have hh : f.Homotopic (ContinuousMap.const (Sphere 3) (F (boundaryToDisk (spherePole 3)))) :=
    ⟨h.cast he rfl⟩
  exact (integralSphereClass_homotopic hh).trans (integralSphereClass_const _)

variable [SimplyConnectedSpace Y] (y : Y) [Subsingleton (π_ 2 Y y)]

include y in
theorem integralSphereClass_zero_iff_disk_extension (f : C(Sphere 3, Y)) :
    integralSphereClass f = 0 ↔
      ∃ F : C(Disk (E := Vector 4), Y), ∀ s, F (boundaryToDisk s) = f s := by
  constructor
  · intro hz
    have hclass : integralSphereClass f =
        integralSphereClass (ContinuousMap.const (Sphere 3) y) :=
      hz.trans (integralSphereClass_const y).symm
    have h := (integralSphereClass_eq_iff_homotopic y f
      (ContinuousMap.const (Sphere 3) y)).mp hclass
    exact DiskBoundary.exists_extension_of_homotopic h.symm
      (ContinuousMap.const (Disk (E := Vector 4)) y) (fun _ ↦ rfl)
  · rintro ⟨F, hb⟩
    exact integralSphereClass_zero_of_disk_extension f F hb

include y in
theorem exists_disk_extension_of_integral_kernel
    (j : C(X, Y)) (f : C(Sphere 3, X))
    (hker : singularHomologyMap j 3 (integralSphereClass f) = 0) :
    ∃ F : C(Disk (E := Vector 4), Y), ∀ s, F (boundaryToDisk s) = j (f s) :=
  (integralSphereClass_zero_iff_disk_extension y (j.comp f)).mp
    ((integralSphereClass_comp j f).trans hker)

end NoExoticSixSphere.SmoothCube
