import Wikipedia.NoExoticSixSphere.NormalFrameOfEquations

/-!
# Nonzero constant scaling preserves the actual tangent image

The derivative is computed in the original source atlas. Only the ambient
map is multiplied by a scalar; the equality of tangent images is proved
using explicit preimages, not by changing that atlas.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.NormalFrameOfEquations

variable {B H M E : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {i : M → E}

theorem ambientDifferential_smul (hi : ContMDiff I 𝓘(ℝ, E) ∞ i) (s : ℝ) (x : M) :
    ambientDifferential I (fun p ↦ s • i p) x = s • ambientDifferential I i x := by
  let L : E →L[ℝ] E := s • ContinuousLinearMap.id ℝ E
  change mfderiv I 𝓘(ℝ, E) (L ∘ i) x = s • ambientDifferential I i x
  rw [mfderiv_comp x L.differentiableAt.mdifferentiableAt
    (hi.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem range_ambientDifferential_smul (hi : ContMDiff I 𝓘(ℝ, E) ∞ i)
    (s : ℝ) (hs : s ≠ 0) (x : M) :
    (ambientDifferential I (fun p ↦ s • i p) x).range =
      (ambientDifferential I i x).range := by
  rw [ambientDifferential_smul hi]
  ext y
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨s • v, ?_⟩
    change ambientDifferential I i x (s • v) = y
    rw [map_smul]
    exact hv
  · rintro ⟨v, hv⟩
    refine ⟨s⁻¹ • v, ?_⟩
    change s • ambientDifferential I i x (s⁻¹ • v) = y
    rw [map_smul, smul_smul, mul_inv_cancel₀ hs, one_smul]
    exact hv

theorem injective_ambientDifferential_smul (hi : ContMDiff I 𝓘(ℝ, E) ∞ i)
    (s : ℝ) (hs : s ≠ 0) (x : M) (hx : Function.Injective (ambientDifferential I i x)) :
    Function.Injective (ambientDifferential I (fun p ↦ s • i p) x) := by
  rw [ambientDifferential_smul hi]
  exact (LinearEquiv.smulOfNeZero ℝ E s hs).injective.comp hx

end NoExoticSixSphere.NormalFrameOfEquations
