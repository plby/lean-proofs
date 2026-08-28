import Wikipedia.NoExoticSixSphere.FramedDiskHomotopy

/-!
# The continuous boundary frame of a smoothly varying sphere family
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization Stiefel ProjectionHomotopy

theorem continuous_boundaryFrame {N k : ℕ} :
    Continuous (boundaryFrame (N := N) (k := k)) := by
  apply Continuous.subtype_mk
  apply continuous_clm_apply.mpr
  intro w
  change Continuous (fun a : Space N k ↦ coordinates N 4
    ((a.val (EuclideanSpace.finAddEquivProd w).1, 0),
      (DiskGraph.extraCoordinates 4).symm (EuclideanSpace.finAddEquivProd w).2))
  apply (coordinates N 4).continuous.comp
  exact ((continuous_subtype_val.clm_apply continuous_const).prodMk
    continuous_const).prodMk continuous_const

variable {N k : ℕ} (a : ℝ → Sphere 3 → Space N k)
  (has : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3))
    𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun q : ℝ × Sphere 3 ↦ (a q.1 q.2).val))

def boundaryFrameFamily : C(unitInterval × Sphere 3, Space (N + 6) (k + 5)) where
  toFun q := boundaryFrame (a (q.1 : ℝ) q.2)
  continuous_toFun := by
    have hc₀ : Continuous (fun q : ℝ × Sphere 3 ↦ a q.1 q.2) :=
      has.continuous.subtype_mk _
    have hι : Continuous (fun q : unitInterval × Sphere 3 ↦ ((q.1 : ℝ), q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have hc : Continuous (fun q : unitInterval × Sphere 3 ↦ a (q.1 : ℝ) q.2) := hc₀.comp hι
    exact continuous_boundaryFrame.comp hc

theorem boundaryFrameFamily_slice (t : unitInterval) :
    slice (boundaryFrameFamily a has) t = boundaryFrameMap (a (t : ℝ))
      (has.comp (contMDiff_const.prodMk contMDiff_id)) := by
  apply ContinuousMap.ext
  intro s
  rfl

end NoExoticSixSphere.StabilizedSpanningDisk
