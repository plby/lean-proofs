import Wikipedia.NoExoticSixSphere.SmoothOpenCoverInclusion
import Wikipedia.NoExoticSixSphere.LocalDiffeomorphSmoothMaps

/-!
# Smooth maps out of a manifold glued from open pieces

A map from the glued atlas is smooth exactly when its restrictions are smooth
for the originally supplied local atlases. Each inclusion is a local
diffeomorphism, so this conclusion does not presume equality of the atlases.
-/

open scoped Manifold ContDiff
open TopologicalSpace

namespace NoExoticSixSphere.SmoothOpenCover

variable {B H X ι : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace X]
  {U : ι → Opens X} (A : SmoothOpenCover I U)
  {C H' Y : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace Y] [ChartedSpace H' Y]

theorem contMDiff_iff_onPieces (f : X → Y) : letI := A.chartedSpace;
    ContMDiff I J ∞ f ↔ ∀ i, letI := A.localAtlas i;
      ContMDiff I J ∞ (fun x : U i ↦ f x.val) := by
  let := A.chartedSpace
  constructor
  · intro hf i
    let := A.localAtlas i
    exact hf.comp (A.contMDiff_inclusion i)
  · intro hlocal x
    obtain ⟨i, hx⟩ := A.covers x
    let := A.localAtlas i
    let p : U i := ⟨x, hx⟩
    exact (contMDiffAt_comp_localDiffeomorph_iff (A.isLocalDiffeomorphAt_inclusion i p) f).mp
      (hlocal i p)

end NoExoticSixSphere.SmoothOpenCover
