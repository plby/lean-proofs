import Wikipedia.NoExoticSixSphere.ImmersedDiskStabilization
import Wikipedia.NoExoticSixSphere.StabilizedDiskHomotopy
import Wikipedia.NoExoticSixSphere.ImmersedDiskHomotopy

/-!
# Independence of the constructed spanning disk

The actual disk data with the fixed boundary collar are joined by the checked
five-coordinate relative homotopy. Their boundary columns stay normal on that
homotopy. Homotopy invariance and the proved ordinary stabilization comparison
therefore identify the original disk parities, not just their stabilized values.

The embedded representative and original normal framing are fixed here.
No quadratic identity or independence of representatives is asserted.
-/

noncomputable section

open Function Set Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel

theorem parity_independent_of_disk {k : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector (k + 6)}
    (D₀ D₁ : DiskData b f) (hf : ContMDiff (𝓡 3) (𝓡 (k + 6)) ∞ f)
    (a : Sphere 3 → Space (k + 6) k)
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector (k + 6)) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 (k + 6)) f s).rangeᗮ) :
    D₀.parity hf a has ha = D₁.parity hf a has ha := by
  obtain ⟨H, hHs, _, hHi, hH₀, hH₁, V, hV, hSV, hfixed⟩ :=
    D₀.exists_homotopy_stabilized D₁
  let a₀ := boundaryFrameMap a has
  let a₅ := (BlockSum.map 5).comp a₀
  let A : C(unitInterval × Sphere 3, Space (k + 17) (k + 10)) :=
    ⟨fun q ↦ a₅ q.2, a₅.continuous.comp continuous_snd⟩
  have hA (q : unitInterval × Sphere 3) :
      (A q).val.range ≤ (fderiv ℝ (H (q.1 : ℝ)) q.2.val).rangeᗮ := by
    have he : H (q.1 : ℝ) =ᶠ[𝓝 q.2.val] ImmersedDisk.stabilize 5 (collar b f) := by
      filter_upwards [hV.mem_nhds (hSV q.2.property)] with x hx
      exact hfixed (q.1 : ℝ) x hx
    have hcs : ContDiffAt ℝ ∞ (collar b f) q.2.val :=
      (coordinates (k + 6) 4).contDiff.contDiffAt.comp q.2.val
        ((SphereExtensionWithHeight.contDiff_map b f hf).contDiffAt.prodMk contDiffAt_const)
    rw [he.fderiv_eq, ImmersedDisk.fderiv_stabilize 5 (collar b f) hcs]
    exact range_blockFrame_normal 5 (fderiv ℝ (collar b f) q.2.val)
      (boundaryFrame (a q.2)) (boundaryFrame_normal_collar b f hf q.2 (a q.2) (ha q.2))
  have hAt (t : unitInterval) : ProjectionHomotopy.slice A t = a₅ := by
    apply ContinuousMap.ext
    intro s
    rfl
  have he₀ : H 0 = ImmersedDisk.stabilize 5 D₀.toFun := funext hH₀
  have he₁ : H 1 = ImmersedDisk.stabilize 5 D₁.toFun := funext hH₁
  have h := DiskHomotopy.parity_endpoints (k + 8) H hHs
    (fun t x hx ↦ hHi (t : ℝ) x hx) A hA
  have hp₀ := ImmersedDisk.parity_stabilize_five (k + 3) D₀.toFun
    (fun _ _ ↦ D₀.smooth.contDiffAt) D₀.immersive a₀ (D₀.normal_boundaryFrameMap hf a has ha)
  have hp₁ := ImmersedDisk.parity_stabilize_five (k + 3) D₁.toFun
    (fun _ _ ↦ D₁.smooth.contDiffAt) D₁.immersive a₀ (D₁.normal_boundaryFrameMap hf a has ha)
  calc
    D₀.parity hf a has ha = _ := hp₀.symm
    _ = _ := by simpa only [he₀, he₁, hAt] using h
    _ = D₁.parity hf a has ha := hp₁

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
