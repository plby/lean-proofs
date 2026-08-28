import Wikipedia.NoExoticSixSphere.SmoothOpenCoverInclusion

/-! # Injectivity of a differential can be checked on the glued atlas pieces -/

open scoped Manifold ContDiff
open TopologicalSpace Function

namespace NoExoticSixSphere.SmoothOpenCover

variable {B H X ι C K Y : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace X] {U : ι → Opens X}
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace K]
  {J : ModelWithCorners ℝ C K} [TopologicalSpace Y] [ChartedSpace K Y]

theorem injective_mfderiv_of_onPieces (A : SmoothOpenCover I U) (f : X → Y)
    (hf : letI := A.chartedSpace; ContMDiff I J ∞ f)
    (hlocal : ∀ i, letI := A.localAtlas i;
      ∀ x : U i, Injective (mfderiv I J (fun y : U i ↦ f y.val) x)) :
    letI := A.chartedSpace; ∀ x, Injective (mfderiv I J f x) := by
  let := A.chartedSpace
  intro x
  obtain ⟨i, hx⟩ := A.covers x
  let := A.localAtlas i
  let y : U i := ⟨x, hx⟩
  have hi := A.isLocalDiffeomorphAt_inclusion i y
  have h := hlocal i y
  change Injective (mfderiv I J (f ∘ (Subtype.val : U i → X)) y) at h
  rw [mfderiv_comp y (hf.mdifferentiable (by simp) x) (hi.mdifferentiableAt (by simp))] at h
  exact Function.Injective.of_comp_right
    (g := mfderiv I I (Subtype.val : U i → X) y) h
    (hi.mfderivToContinuousLinearEquiv (by simp)).surjective

end NoExoticSixSphere.SmoothOpenCover
