import Wikipedia.NoExoticSixSphere.FramedSpanningDisk

/-!
# The normal-disk parity with an explicit ambient codimension

Reindexing a proved dimension equality supplies the existing disk parity
without replacing any map, derivative, or boundary frame.
-/

noncomputable section

open Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel

variable {N k : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector N} (D : DiskData b f)
  (hN : N = k + 6) (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (a : Sphere 3 → Space N k)
  (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
  (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ)

def parityOfDimension : ZMod 2 := by
  subst N
  exact D.parity hf a has ha

theorem parityOfDimension_zero_iff_smooth_extension :
    D.parityOfDimension hN hf a has ha = 0 ↔
      ∃ T : Vector 4 → Vector (k + 5) →L[ℝ] Vector (N + 6),
        (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, (T x).range ≤ (fderiv ℝ D.toFun x).rangeᗮ) ∧
        ∀ s : Sphere 3, T s.val = boundaryFrameOperator (a s).val := by
  subst N
  exact D.parity_zero_iff_smooth_extension hf a has ha

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
