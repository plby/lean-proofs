import Wikipedia.NoExoticSixSphere.QuaternionicHopfOriginalNormalFrame
import Wikipedia.NoExoticSixSphere.HilbertProductEquations

/-!
# The induced normal frame on the actual product of south Hopf fibers

The ambient inclusion is the product of the two original S3 inclusions.
The actual paired equations induce its normal frame, with both radial
directions and both right-quaternion-multiplication blocks retained.
This does not yet identify its collapse with the original suspended smash.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

abbrev SouthPairAmbientModel := WithLp 2 (V 8 × V 8)
abbrev SouthPairNormalModel := WithLp 2 (SouthNormalModel × SouthNormalModel)

def southPairAmbient (p : Sphere 3 × Sphere 3) : SouthPairAmbientModel :=
  WithLp.toLp 2 (southFiberAmbient p.1, southFiberAmbient p.2)

def southPairEquations : SouthPairAmbientModel → SouthPairNormalModel :=
  HilbertProduct.equations southNormalEquations southNormalEquations

theorem contMDiff_southPairAmbient :
    ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, SouthPairAmbientModel) ∞ southPairAmbient :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (V 8) (V 8)).symm.contDiff.contMDiff.comp
    ((contMDiff_southFiberAmbient.comp contMDiff_fst).prodMk_space
      (contMDiff_southFiberAmbient.comp contMDiff_snd))

theorem contDiff_southPairEquations : ContDiff ℝ ∞ southPairEquations :=
  HilbertProduct.contDiff_equations contDiff_southNormalEquations contDiff_southNormalEquations

theorem southPairAmbient_injective : Function.Injective southPairAmbient := by
  intro p q h
  apply Prod.ext
  · apply southFiberPoint_injective
    exact Subtype.ext (congrArg (fun v : SouthPairAmbientModel ↦ v.fst) h)
  · apply southFiberPoint_injective
    exact Subtype.ext (congrArg (fun v : SouthPairAmbientModel ↦ v.snd) h)

theorem southPairAmbient_isClosedEmbedding : Topology.IsClosedEmbedding southPairAmbient :=
  contMDiff_southPairAmbient.continuous.isClosedEmbedding southPairAmbient_injective

theorem southPairEquations_zero (p : Sphere 3 × Sphere 3) :
    southPairEquations (southPairAmbient p) = 0 := by
  change WithLp.toLp 2 (southNormalEquations (southFiberPoint p.1).val,
    southNormalEquations (southFiberPoint p.2).val) = 0
  rw [southNormalEquations_zero _ (first_southFiberPoint p.1),
    southNormalEquations_zero _ (first_southFiberPoint p.2)]
  rfl

theorem southPairEquations_derivative (x : SouthPairAmbientModel) :
    fderiv ℝ southPairEquations x = HilbertProduct.map
      (fderiv ℝ southNormalEquations x.fst) (fderiv ℝ southNormalEquations x.snd) :=
  HilbertProduct.fderiv_equations
    (contDiff_southNormalEquations.differentiable (by simp) x.fst)
    (contDiff_southNormalEquations.differentiable (by simp) x.snd)

theorem southPairEquations_surjective (p : Sphere 3 × Sphere 3) :
    Function.Surjective (fderiv ℝ southPairEquations (southPairAmbient p)) := by
  rw [southPairEquations_derivative]
  exact HilbertProduct.map_surjective _ _
    (southNormalEquations_surjective (southFiberPoint p.1) (first_southFiberPoint p.1))
    (southNormalEquations_surjective (southFiberPoint p.2) (first_southFiberPoint p.2))

theorem southPairAmbient_derivative (p : Sphere 3 × Sphere 3) :
    NormalFrameOfEquations.ambientDifferential ((𝓡 3).prod (𝓡 3)) southPairAmbient p =
      (WithLp.prodContinuousLinearEquiv 2 ℝ (V 8) (V 8)).symm.toContinuousLinearMap.comp
        ((NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient p.1).prodMap
          (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient p.2)) := by
  let u := (WithLp.prodContinuousLinearEquiv 2 ℝ (V 8) (V 8)).symm.toContinuousLinearMap
  have hi : ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, V 8 × V 8) ∞
      (Prod.map southFiberAmbient southFiberAmbient) :=
    (contMDiff_southFiberAmbient.comp contMDiff_fst).prodMk_space
      (contMDiff_southFiberAmbient.comp contMDiff_snd)
  change mfderiv ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, SouthPairAmbientModel)
    (u ∘ Prod.map southFiberAmbient southFiberAmbient) p = _
  have hp : (mfderiv ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, V 8 × V 8)
    (Prod.map southFiberAmbient southFiberAmbient) p : (V 3 × V 3) →L[ℝ] V 8 × V 8) =
      (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient p.1).prodMap
        (NormalFrameOfEquations.ambientDifferential (𝓡 3) southFiberAmbient p.2) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact mfderiv_prodMap (p := p)
      (contMDiff_southFiberAmbient.mdifferentiableAt (by simp))
      (contMDiff_southFiberAmbient.mdifferentiableAt (by simp))
  have h := mfderiv_comp p u.differentiableAt.mdifferentiableAt
    (hi.mdifferentiableAt (by simp))
  change (mfderiv ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, SouthPairAmbientModel)
    (u ∘ Prod.map southFiberAmbient southFiberAmbient) p :
      (V 3 × V 3) →L[ℝ] SouthPairAmbientModel) =
    (mfderiv 𝓘(ℝ, V 8 × V 8) 𝓘(ℝ, SouthPairAmbientModel) u
      (Prod.map southFiberAmbient southFiberAmbient p) :
        (V 8 × V 8) →L[ℝ] SouthPairAmbientModel).comp
      (mfderiv ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, V 8 × V 8)
        (Prod.map southFiberAmbient southFiberAmbient) p : (V 3 × V 3) →L[ℝ] V 8 × V 8) at h
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv, hp] at h
  exact h

theorem southPairAmbient_differential_injective (p : Sphere 3 × Sphere 3) :
    Function.Injective (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) southPairAmbient p) := by
  rw [southPairAmbient_derivative]
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ (V 8) (V 8)).symm.injective.comp
  intro v w h
  exact Prod.ext
    (southFiberAmbient_differential_injective p.1 (congrArg Prod.fst h))
    (southFiberAmbient_differential_injective p.2 (congrArg Prod.snd h))

theorem southPairNormalDimensions : Module.finrank ℝ SouthPairAmbientModel =
    Module.finrank ℝ SouthPairNormalModel + Module.finrank ℝ (V 3 × V 3) := by
  have hE := (WithLp.prodContinuousLinearEquiv 2 ℝ (V 8) (V 8)).toLinearEquiv.finrank_eq
  have hF := (WithLp.prodContinuousLinearEquiv 2 ℝ
    SouthNormalModel SouthNormalModel).toLinearEquiv.finrank_eq
  rw [hE, hF, Module.finrank_prod, Module.finrank_prod, Module.finrank_prod]
  have hd := southNormalDimensions
  omega

def southPairNormalFrame : SmoothRangeFrame ((𝓡 3).prod (𝓡 3))
    (fun p : Sphere 3 × Sphere 3 ↦ (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) southPairAmbient p).rangeᗮ.starProjection) SouthPairNormalModel :=
  NormalFrameOfEquations.inducedFrame contMDiff_southPairAmbient
    (fun _ ↦ contDiff_southPairEquations.contDiffAt) southPairEquations_zero
    southPairEquations_surjective southPairAmbient_differential_injective southPairNormalDimensions

theorem southPairNormalFrame_ambient (p : Sphere 3 × Sphere 3) :
    southPairNormalFrame.ambient p =
      HilbertProduct.map (southNormalFrame.ambient p.1) (southNormalFrame.ambient p.2) := by
  change orthogonalRightInverse (fderiv ℝ southPairEquations (southPairAmbient p)) = _
  rw [southPairEquations_derivative]
  change orthogonalRightInverse (HilbertProduct.map
    (fderiv ℝ southNormalEquations (southFiberPoint p.1).val)
    (fderiv ℝ southNormalEquations (southFiberPoint p.2).val)) = _
  rw [orthogonalRightInverse_product _ _
    (southNormalEquations_surjective (southFiberPoint p.1) (first_southFiberPoint p.1))
    (southNormalEquations_surjective (southFiberPoint p.2) (first_southFiberPoint p.2))]
  rfl

theorem southPairNormalFrame_transverse (p : Sphere 3 × Sphere 3) (w z : ℍ) :
    southPairNormalFrame.ambient p
      (WithLp.toLp 2 (WithLp.toLp 2 (0, (2 : ℝ) • w),
        WithLp.toLp 2 (0, (2 : ℝ) • z))) =
      WithLp.toLp 2 (firstAxis (w * Quaternion.linearIsometryEquivTuple.symm p.1.val),
        firstAxis (z * Quaternion.linearIsometryEquivTuple.symm p.2.val)) := by
  rw [southPairNormalFrame_ambient, HilbertProduct.map_apply]
  change WithLp.toLp 2
    (southNormalFrame.ambient p.1 (WithLp.toLp 2 (0, (2 : ℝ) • w)),
      southNormalFrame.ambient p.2 (WithLp.toLp 2 (0, (2 : ℝ) • z))) = _
  rw [southNormalFrame_transverse, southNormalFrame_transverse]

theorem southPairNormalFrame_radial_left (p : Sphere 3 × Sphere 3) :
    southPairNormalFrame.ambient p (WithLp.toLp 2 (WithLp.toLp 2 (2, (0 : ℍ)), 0)) =
      WithLp.toLp 2 (southFiberAmbient p.1, (0 : V 8)) := by
  rw [southPairNormalFrame_ambient, HilbertProduct.map_apply]
  change WithLp.toLp 2 (southNormalFrame.ambient p.1 (WithLp.toLp 2 (2, (0 : ℍ))),
    southNormalFrame.ambient p.2 0) = _
  rw [southNormalFrame_radial, map_zero]

theorem southPairNormalFrame_radial_right (p : Sphere 3 × Sphere 3) :
    southPairNormalFrame.ambient p (WithLp.toLp 2 (0, WithLp.toLp 2 (2, (0 : ℍ)))) =
      WithLp.toLp 2 ((0 : V 8), southFiberAmbient p.2) := by
  rw [southPairNormalFrame_ambient, HilbertProduct.map_apply]
  change WithLp.toLp 2 (southNormalFrame.ambient p.1 0,
    southNormalFrame.ambient p.2 (WithLp.toLp 2 (2, (0 : ℍ)))) = _
  rw [map_zero, southNormalFrame_radial]

theorem southPairNormalFrame_original (a b : Sphere 7) (p : Sphere 3 × Sphere 3)
    (v w : WithLp 2 (ℝ × V 4)) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    southPairNormalFrame.ambient p
      (WithLp.toLp 2 (augmentedTargetChange.symm v, augmentedTargetChange.symm w)) =
      WithLp.toLp 2
        ((SphereFiberNormalFrame.normalFrame sphereMap contMDiff_sphereMap south south_regular
          3 (by decide) a).ambient (southFiberDiffeomorph p.1) v,
        (SphereFiberNormalFrame.normalFrame sphereMap contMDiff_sphereMap south south_regular
          3 (by decide) b).ambient (southFiberDiffeomorph p.2) w) := by
  let := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin])
  rw [southPairNormalFrame_ambient, HilbertProduct.map_apply,
    original_southNormalFrame_parametrized, original_southNormalFrame_parametrized]
  rfl

end NoExoticSixSphere.QuaternionicHopf
