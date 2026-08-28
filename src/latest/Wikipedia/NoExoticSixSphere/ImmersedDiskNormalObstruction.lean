import Wikipedia.NoExoticSixSphere.NormalDiskObstruction

/-!
# Partial normal frames on an actual smooth immersed four-disk

The differential is the ordinary derivative of the given Euclidean map,
not a separately supplied tangent-plane family. Smoothness near the closed
disk and injectivity there construct the normal projection and its full
orthonormal trivialization. The resulting parity detects continuous extension
of the original partial normal frame, with exact boundary values.

This does not yet construct spanning immersed or embedded disks, prove
independence of their choice, or construct a geometric quadratic refinement.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.Stiefel.ImmersedDisk

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable (r : ℕ) (f : Vector 4 → Vector (r + 9))
variable (hf : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ f x)

def differential : C(Disk (E := Vector 4), Vector 4 →L[ℝ] Vector (r + 9)) where
  toFun x := fderiv ℝ f x.val
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((hf x.val x.property).continuousAt_fderiv (by simp)).comp
      continuous_subtype_val.continuousAt

variable (hi : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Function.Injective (fderiv ℝ f x))

include hi in
theorem differential_injective (x : Disk (E := Vector 4)) :
    Function.Injective (differential r f hf x) := hi x.val x.property

variable (a : C(NoExoticSixSphere.Sphere 3, Space (r + 9) (r + 2)))
variable (ha : ∀ s, (a s).val.range ≤ (fderiv ℝ f s.val).rangeᗮ)

def parity : ZMod 2 :=
  DiskNormal.parity r (differential r f hf) (differential_injective r f hf hi) a ha

theorem parity_zero_iff_extension : parity r f hf hi a ha = 0 ↔
    ∃ A : C(Disk (E := Vector 4), Space (r + 9) (r + 2)),
      (∀ x, (A x).val.range ≤ (fderiv ℝ f x.val).rangeᗮ) ∧
      ∀ s, A (boundaryToDisk s) = a s :=
  DiskNormal.parity_zero_iff_extension r (differential r f hf)
    (differential_injective r f hf hi) a ha

end NoExoticSixSphere.Stiefel.ImmersedDisk
