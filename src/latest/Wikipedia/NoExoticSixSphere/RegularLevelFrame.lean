import Wikipedia.NoExoticSixSphere.SmoothKernelFrame
import Wikipedia.NoExoticSixSphere.RegularLevelDifferential

/-!
# The induced normal frame of an actual Euclidean regular level

The frame is smooth for the already-constructed regular-level atlas. Its
range is the orthogonal complement of the actual inclusion differential,
and applying the defining differential gives the identity.
-/

open scoped Manifold ContDiff
open Module

namespace NoExoticSixSphere.RegularLevelAtlas

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
  {f : E → F} (A : RegularLevelAtlas (K := K) 𝓘(ℝ, E) f)

noncomputable def ambientInclusionDifferential (x : {x : E // f x = 0}) :
    letI := A.chartedSpace;
    K →L[ℝ] E := by
  let := A.chartedSpace
  exact mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) (Subtype.val : {x : E // f x = 0} → E) x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ K] in
theorem contMDiff_levelDifferential
    (hf : ∀ x, f x = 0 → ContDiffAt ℝ ∞ f x) :
    letI := A.chartedSpace;
    ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, E →L[ℝ] F) ∞
      (fun x : {x : E // f x = 0} ↦ fderiv ℝ f x.val) := by
  let := A.chartedSpace
  intro x
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ f) x.val :=
    (hf x.val x.property).fderiv_right (by simp)
  exact hD.contMDiffAt.comp x (A.contMDiff_subtype_val x)

omit [FiniteDimensional ℝ F] in
theorem level_inclusion_range_eq_kernel (x : {x : E // f x = 0})
    (hf : ContDiffAt ℝ ∞ f x.val) (hreg : Function.Surjective (fderiv ℝ f x.val))
    (hd : finrank ℝ E = finrank ℝ F + finrank ℝ K) :
    letI := A.chartedSpace;
    (A.ambientInclusionDifferential x).range =
      (fderiv ℝ f x.val).ker := by
  let := A.chartedSpace
  have he : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x.val : E →L[ℝ] F) = fderiv ℝ f x.val :=
    mfderiv_eq_fderiv
  have hreg' : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x.val) := by
    intro w
    obtain ⟨v, hv⟩ := hreg w
    exact ⟨v, (congrArg (fun L : E →L[ℝ] F ↦ L v) he).trans hv⟩
  have h := A.range_inclusion_eq_kernel x
    (hf.differentiableAt (by simp)).mdifferentiableAt hreg' hd
  rw [he] at h
  exact h

noncomputable def inducedNormalFrame
    (hf : ∀ x, f x = 0 → ContDiffAt ℝ ∞ f x)
    (hreg : ∀ x, f x = 0 → Function.Surjective (fderiv ℝ f x))
    (hd : finrank ℝ E = finrank ℝ F + finrank ℝ K) :
    letI := A.chartedSpace;
    SmoothRangeFrame 𝓘(ℝ, K)
      (fun x : {x : E // f x = 0} ↦
        (A.ambientInclusionDifferential x).rangeᗮ.starProjection) F := by
  let := A.chartedSpace
  let R := fun x : {x : E // f x = 0} ↦ orthogonalRightInverse (fderiv ℝ f x.val)
  let P := fun x : {x : E // f x = 0} ↦ (A.ambientInclusionDifferential x).rangeᗮ.starProjection
  have hrange (x : {x : E // f x = 0}) : (R x).range = (P x).range := by
    change (orthogonalRightInverse (fderiv ℝ f x.val)).range =
      ((A.ambientInclusionDifferential x).rangeᗮ.starProjection).range
    rw [Submodule.range_starProjection, range_orthogonalRightInverse _ (hreg x.val x.property)]
    exact congrArg (fun S : Submodule ℝ E ↦ Sᗮ)
      (A.level_inclusion_range_eq_kernel x (hf x.val x.property) (hreg x.val x.property) hd).symm
  let e (x : {x : E // f x = 0}) : F ≃L[ℝ] (P x).range :=
    (LinearEquiv.ofInjective (R x).toLinearMap
      (orthogonalRightInverse_injective _ (hreg x.val x.property))).toContinuousLinearEquiv.trans
        (ContinuousLinearEquiv.ofEq _ _ (hrange x))
  refine ⟨e, ?_⟩
  have heq : (fun x ↦ (P x).range.subtypeL.comp (e x).toContinuousLinearMap) = R := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [heq]
  exact fun x ↦ contMDiffAt_orthogonalRightInverse
    (A.contMDiff_levelDifferential hf x) (hreg x.val x.property)

theorem inducedNormalFrame_ambient
    (hf : ∀ x, f x = 0 → ContDiffAt ℝ ∞ f x)
    (hreg : ∀ x, f x = 0 → Function.Surjective (fderiv ℝ f x))
    (hd : finrank ℝ E = finrank ℝ F + finrank ℝ K) (x : {x : E // f x = 0}) :
    letI := A.chartedSpace;
    (A.inducedNormalFrame hf hreg hd).ambient x = orthogonalRightInverse (fderiv ℝ f x.val) := by
  let := A.chartedSpace
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem inducedNormalFrame_differential
    (hf : ∀ x, f x = 0 → ContDiffAt ℝ ∞ f x)
    (hreg : ∀ x, f x = 0 → Function.Surjective (fderiv ℝ f x))
    (hd : finrank ℝ E = finrank ℝ F + finrank ℝ K) (x : {x : E // f x = 0}) :
    letI := A.chartedSpace;
    (fderiv ℝ f x.val).comp ((A.inducedNormalFrame hf hreg hd).ambient x) =
      ContinuousLinearMap.id ℝ F := by
  let := A.chartedSpace
  rw [A.inducedNormalFrame_ambient]
  exact comp_orthogonalRightInverse _ (hreg x.val x.property)

end NoExoticSixSphere.RegularLevelAtlas
