import Wikipedia.NoExoticSixSphere.StabilizedDiskBoundaryNormal
import Wikipedia.NoExoticSixSphere.ImmersedDiskSmoothNormalExtension

/-!
# Normal-frame parity on constructed stabilized spanning disks

The disk is a genuine smooth embedded ball with the exact original boundary
and the constructed open collar. The original partial frame and five added
axes are proved smooth, orthonormal and normal to its actual derivative.
Their parity detects exact smooth extension over that disk.

The parity is attached to specified disk data. Independence of the spanning
disk or embedded representative, and the quadratic identity, are not asserted.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization Stiefel

structure DiskData {N : ℕ} (b : Sphere 3) (f : Sphere 3 → Vector N) where
  toFun : Vector 4 → Vector (N + 6)
  smooth : ContDiff ℝ ∞ toFun
  embedded : IsClosedEmbedding (fun x : closedBall (0 : Vector 4) 1 ↦ toFun x.val)
  immersive : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ toFun x)
  boundary : ∀ s : Sphere 3, toFun s.val = appendZeroMap N 6 (f s)
  avoids : ∀ x ∈ ball (0 : Vector 4) 1, toFun x ∉ range (appendZeroMap N 6)
  collar_eq : ∃ V : Set (Vector 4), IsOpen V ∧ sphere 0 1 ⊆ V ∧ EqOn toFun (collar b f) V

theorem nonempty_diskData {N : ℕ} (b : Sphere 3) (f : Sphere 3 → Vector N)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 N) f s)) : Nonempty (DiskData b f) := by
  obtain ⟨G, hGs, hGe, hGi, hGb, hGa, hGc⟩ := exists_spanningDisk b f hf hi hd
  exact ⟨⟨G, hGs, hGe, hGi, hGb, hGa, hGc⟩⟩

def boundaryFrameMap {N k : ℕ} (a : Sphere 3 → Space N k)
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val)) :
    C(Sphere 3, Space (N + 6) (k + 5)) :=
  ⟨fun s ↦ boundaryFrame (a s),
    (contMDiff_boundaryFrameOperator has).continuous.subtype_mk _⟩

namespace DiskData

variable {k : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector (k + 6)} (D : DiskData b f)
  (hf : ContMDiff (𝓡 3) (𝓡 (k + 6)) ∞ f) (a : Sphere 3 → Space (k + 6) k)
  (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector (k + 6)) ∞ (fun s ↦ (a s).val))
  (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 (k + 6)) f s).rangeᗮ)

include hf ha in
theorem normal_boundaryFrameMap (s : Sphere 3) :
    ((boundaryFrameMap a has) s).val.range ≤ (fderiv ℝ D.toFun s.val).rangeᗮ := by
  obtain ⟨V, hV, hSV, heq⟩ := D.collar_eq
  exact boundaryFrame_normal_disk b f hf a ha hV hSV heq s

/-- The actual normal-disk obstruction for this specified constructed disk. -/
def parity : ZMod 2 :=
  ImmersedDisk.parity (k + 3) D.toFun (fun _ _ ↦ D.smooth.contDiffAt) D.immersive
    (boundaryFrameMap a has) (D.normal_boundaryFrameMap hf a has ha)

theorem parity_zero_iff_smooth_extension : D.parity hf a has ha = 0 ↔
    ∃ T : Vector 4 → Vector (k + 5) →L[ℝ] Vector (k + 12),
      (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, (T x).range ≤ (fderiv ℝ D.toFun x).rangeᗮ) ∧
      ∀ s : Sphere 3, T s.val = boundaryFrameOperator (a s).val :=
  ImmersedDisk.parity_zero_iff_smooth_extension (k + 3) D.toFun
    (fun _ _ ↦ D.smooth.contDiffAt) D.immersive (boundaryFrameMap a has)
    (D.normal_boundaryFrameMap hf a has ha) (contMDiff_boundaryFrameOperator has)

end DiskData

end NoExoticSixSphere.StabilizedSpanningDisk
