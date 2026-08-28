import Wikipedia.NoExoticSixSphere.NormalDiskStabilization
import Wikipedia.NoExoticSixSphere.ImmersedDiskNormalObstruction

/-!
# Five-coordinate stabilization preserves an actual immersed disk's parity

The stabilized map is the original map followed by the actual zero-coordinate
inclusion. Its spatial derivative is proved to be the corresponding composite.
The normal-differential stabilization theorem therefore applies to the original
disk and its boundary partial frame.
-/

noncomputable section

open Function Metric
open scoped ContDiff

namespace NoExoticSixSphere.Stiefel.ImmersedDisk

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

def stabilize {N : ℕ} (m : ℕ) (f : Vector 4 → Vector N) : Vector 4 → Vector (N + m) :=
  appendZeroMap N m ∘ f

theorem contDiffAt_stabilize {N : ℕ} (m : ℕ) (f : Vector 4 → Vector N) {x : Vector 4}
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (stabilize m f) x :=
  (appendZeroMap N m).contDiff.contDiffAt.comp x hf

theorem fderiv_stabilize {N : ℕ} (m : ℕ) (f : Vector 4 → Vector N) {x : Vector 4}
    (hf : ContDiffAt ℝ ∞ f x) :
    fderiv ℝ (stabilize m f) x = (appendZeroMap N m).comp (fderiv ℝ f x) :=
  ((appendZeroMap N m).hasFDerivAt.comp x (hf.differentiableAt (by simp)).hasFDerivAt).fderiv

theorem injective_fderiv_stabilize {N : ℕ} (m : ℕ) (f : Vector 4 → Vector N) {x : Vector 4}
    (hf : ContDiffAt ℝ ∞ f x) (hi : Injective (fderiv ℝ f x)) :
    Injective (fderiv ℝ (stabilize m f) x) := by
  rw [fderiv_stabilize m f hf]
  exact (appendZeroMap_injective N m).comp hi

theorem boundary_normal_stabilize {N k : ℕ} (m : ℕ) (f : Vector 4 → Vector N)
    (hf : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ f x)
    (a : C(NoExoticSixSphere.Sphere 3, Space N k))
    (ha : ∀ s, (a s).val.range ≤ (fderiv ℝ f s.val).rangeᗮ) (s : NoExoticSixSphere.Sphere 3) :
    (((BlockSum.map m).comp a) s).val.range ≤ (fderiv ℝ (stabilize m f) s.val).rangeᗮ := by
  rw [fderiv_stabilize m f (hf s.val (sphere_subset_closedBall s.property))]
  exact range_blockFrame_normal m (fderiv ℝ f s.val) (a s) (ha s)

theorem parity_stabilize_five (r : ℕ) (f : Vector 4 → Vector (r + 9))
    (hf : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ f x)
    (hi : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ f x))
    (a : C(NoExoticSixSphere.Sphere 3, Space (r + 9) (r + 2)))
    (ha : ∀ s, (a s).val.range ≤ (fderiv ℝ f s.val).rangeᗮ) :
    parity (r + 5) (stabilize 5 f) (fun x hx ↦ contDiffAt_stabilize 5 f (hf x hx))
        (fun x hx ↦ injective_fderiv_stabilize 5 f (hf x hx) (hi x hx))
        ((BlockSum.map 5).comp a) (boundary_normal_stabilize 5 f hf a ha) =
      parity r f hf hi a ha := by
  have he : differential (r + 5) (stabilize 5 f)
      (fun x hx ↦ contDiffAt_stabilize 5 f (hf x hx)) =
        DiskStabilization.differential 5 (differential r f hf) := by
    apply ContinuousMap.ext
    intro x
    exact fderiv_stabilize 5 f (hf x.val x.property)
  unfold parity
  simpa only [← he] using DiskStabilization.parity_five r (differential r f hf)
    (differential_injective r f hf hi) a ha

end NoExoticSixSphere.Stiefel.ImmersedDisk
