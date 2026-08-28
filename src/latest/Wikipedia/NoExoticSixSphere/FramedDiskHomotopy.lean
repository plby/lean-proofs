import Wikipedia.NoExoticSixSphere.FramedSpanningDisk
import Wikipedia.NoExoticSixSphere.ImmersedDiskHomotopy

/-!
# The specified framed-disk parity is invariant under a relative regular homotopy

The same boundary frame stays normal because the actual collar remains
fixed on one open neighborhood throughout the homotopy. The endpoint
comparison uses the actual constructed disk parities and their original
boundary columns.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel ProjectionHomotopy

theorem parity_eq_of_homotopy {k : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector (k + 6)}
    (D₀ D₁ : DiskData b f) (hf : ContMDiff (𝓡 3) (𝓡 (k + 6)) ∞ f)
    (a : Sphere 3 → Space (k + 6) k)
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector (k + 6)) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 (k + 6)) f s).rangeᗮ)
    (H : ℝ → Vector 4 → Vector (k + 12)) (hH : ContDiff ℝ ∞ (Function.uncurry H))
    (hi : ∀ t : unitInterval, ∀ x ∈ closedBall (0 : Vector 4) 1,
      Injective (fderiv ℝ (H (t : ℝ)) x))
    (h₀ : H 0 = D₀.toFun) (h₁ : H 1 = D₁.toFun)
    {V : Set (Vector 4)} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
    (heq : ∀ t : unitInterval, EqOn (H (t : ℝ)) (collar b f) V) :
    D₀.parity hf a has ha = D₁.parity hf a has ha := by
  let A : C(unitInterval × Sphere 3, Space (k + 12) (k + 5)) :=
    ⟨fun q ↦ boundaryFrame (a q.2), (boundaryFrameMap a has).continuous.comp continuous_snd⟩
  have hA (q : unitInterval × Sphere 3) :
      (A q).val.range ≤ (fderiv ℝ (H (q.1 : ℝ)) q.2.val).rangeᗮ :=
    boundaryFrame_normal_disk b f hf a ha hV hSV (heq q.1) q.2
  have hAt (t : unitInterval) : slice A t = boundaryFrameMap a has := by
    ext s
    rfl
  have h := DiskHomotopy.parity_endpoints (k + 3) H hH hi A hA
  change ImmersedDisk.parity (k + 3) D₀.toFun _ _ _ _ =
    ImmersedDisk.parity (k + 3) D₁.toFun _ _ _ _
  simpa only [h₀, h₁, hAt] using h

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
