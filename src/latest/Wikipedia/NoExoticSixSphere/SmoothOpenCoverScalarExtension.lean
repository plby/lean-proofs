import Wikipedia.NoExoticSixSphere.SmoothOpenCoverInclusion
import Wikipedia.NoExoticSixSphere.LocalDiffeomorphSmoothMaps

/-! # Extending a scalar function on a native open piece for weighted gluing -/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothOpenCover

variable {B H X ι : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace X]
  {U : ι → Opens X} (A : SmoothOpenCover I U)

def scalarExtension (_A : SmoothOpenCover I U) (i : ι) (g : U i → ℝ) (x : X) : ℝ := by
  classical
  exact if hx : x ∈ U i then g ⟨x, hx⟩ else 0

theorem scalarExtension_on_piece (i : ι) (g : U i → ℝ) (x : U i) :
    A.scalarExtension i g x.val = g x := by
  simp only [scalarExtension, dif_pos x.property]

theorem scalarExtension_nonneg (i : ι) (g : U i → ℝ) (hg : ∀ x, 0 ≤ g x) (x : X) :
    0 ≤ A.scalarExtension i g x := by
  classical
  by_cases hx : x ∈ U i
  · simpa only [scalarExtension, dif_pos hx] using hg ⟨x, hx⟩
  · simp only [scalarExtension, dif_neg hx, le_refl]

theorem contMDiffAt_scalarExtension (i : ι) (g : U i → ℝ)
    (hg : letI := A.localAtlas i; ContMDiff I 𝓘(ℝ, ℝ) ∞ g) (x : U i) :
    letI := A.chartedSpace; ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (A.scalarExtension i g) x.val := by
  let := A.chartedSpace
  let := A.localAtlas i
  apply (contMDiffAt_comp_localDiffeomorph_iff (A.isLocalDiffeomorphAt_inclusion i x)
    (A.scalarExtension i g)).mp
  have he : A.scalarExtension i g ∘ (Subtype.val : U i → X) = g :=
    funext (A.scalarExtension_on_piece i g)
  rw [he]
  exact hg x

end NoExoticSixSphere.SmoothOpenCover
