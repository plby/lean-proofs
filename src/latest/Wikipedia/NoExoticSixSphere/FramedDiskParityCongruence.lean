import Wikipedia.NoExoticSixSphere.FramedSpanningDisk

/-!
# Exact map and frame identifications preserve the constructed disk parity
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel

theorem parity_eq_of_map_and_frame {k : ℕ} {b : Sphere 3}
    {f : Sphere 3 → Vector (k + 6)} (D : DiskData b f)
    (hf : ContMDiff (𝓡 3) (𝓡 (k + 6)) ∞ f) (a : Sphere 3 → Space (k + 6) k)
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector (k + 6)) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 (k + 6)) f s).rangeᗮ)
    (g : Vector 4 → Vector (k + 12))
    (hg : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ g x)
    (hgi : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Function.Injective (fderiv ℝ g x))
    (A : C(Sphere 3, Space (k + 12) (k + 5)))
    (hA : ∀ s, (A s).val.range ≤ (fderiv ℝ g s.val).rangeᗮ)
    (heq : D.toFun = g) (hframe : boundaryFrameMap a has = A) :
    D.parity hf a has ha = ImmersedDisk.parity (k + 3) g hg hgi A hA := by
  subst g
  subst A
  rfl

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
