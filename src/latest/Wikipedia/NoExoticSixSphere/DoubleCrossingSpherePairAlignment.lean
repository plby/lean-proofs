import Wikipedia.NoExoticSixSphere.DoubleCrossingSpherePairTransversality
import Wikipedia.NoExoticSixSphere.SphereLinearDiskExtension
import Wikipedia.NoExoticSixSphere.SphereSumCapCoordinates
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Aligning the reference crossing with the original source-chart center

A genuine linear reflection sends the specified source-chart center to the
first crossing. Its sphere restriction is a native diffeomorphism. Precomposing
both embedded reference spheres preserves their exact intersection count and
native transversality, and puts their common value at the required center.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DoubleCrossingSpherePair

open GLOrthonormalization SphereCylinder SphereSumNeck SphereLinearReparametrization

def alignmentLinear : Vector 4 ≃ₗᵢ[ℝ] Vector 4 :=
  (ℝ ∙ ((sourceChart 0).val - (endPole 2 false).val))ᗮ.reflection

def alignment : Diffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Sphere 3) ∞ :=
  sphereDiffeomorph alignmentLinear

theorem alignment_center : alignment (sourceChart 0) = endPole 2 false := by
  apply Subtype.ext
  change alignmentLinear (sourceChart 0).val = (endPole 2 false).val
  exact Submodule.reflection_sub
    ((ClosedHemisphere.unit_norm (sourceChart 0)).trans
      (ClosedHemisphere.unit_norm (endPole 2 false)).symm)

def alignedLeft : C(Sphere 3, Vector 3 × Vector 3) :=
  leftMap.comp ⟨alignment, alignment.contMDiff_toFun.continuous⟩

def alignedRight : C(Sphere 3, Vector 3 × Vector 3) :=
  rightMap.comp ⟨alignment, alignment.contMDiff_toFun.continuous⟩

theorem contMDiff_alignedLeft : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) ∞ alignedLeft :=
  contMDiff_left.comp alignment.contMDiff_toFun

theorem contMDiff_alignedRight : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) ∞ alignedRight :=
  contMDiff_right.comp alignment.contMDiff_toFun

theorem injective_alignedLeft : Injective alignedLeft := injective_left.comp alignment.injective

theorem injective_alignedRight : Injective alignedRight := injective_right.comp alignment.injective

theorem alignedLeft_center : alignedLeft (sourceChart 0) = 0 := by
  change left (alignment (sourceChart 0)) = 0
  rw [alignment_center, left_first]

theorem alignedRight_center : alignedRight (sourceChart 0) = 0 := by
  change right (alignment (sourceChart 0)) = 0
  rw [alignment_center, right_first]

theorem alignedLeft_zero_fiber (x : Sphere 3) : alignedLeft x = 0 ↔ x = sourceChart 0 := by
  rw [← alignedLeft_center]
  exact injective_alignedLeft.eq_iff

theorem alignedRight_zero_fiber (x : Sphere 3) : alignedRight x = 0 ↔ x = sourceChart 0 := by
  rw [← alignedRight_center]
  exact injective_alignedRight.eq_iff

theorem norm_alignedLeft_le_two (x : Sphere 3) : ‖alignedLeft x‖ ≤ 2 :=
  norm_left_le_two (alignment x)

theorem norm_alignedRight_le_two (x : Sphere 3) : ‖alignedRight x‖ ≤ 2 :=
  norm_right_le_two (alignment x)

theorem mfderiv_alignedLeft (x : Sphere 3) :
    mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) alignedLeft x =
      (leftDerivative (alignment x)).comp (mfderiv (𝓡 3) (𝓡 3) alignment x) := by
  change mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) (left ∘ alignment) x = _
  exact mfderiv_comp x (contMDiff_left.mdifferentiableAt (by simp))
    (alignment.contMDiff_toFun.mdifferentiableAt (by simp))

theorem mfderiv_alignedRight (x : Sphere 3) :
    mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) alignedRight x =
      (rightDerivative (alignment x)).comp (mfderiv (𝓡 3) (𝓡 3) alignment x) := by
  change mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) (right ∘ alignment) x = _
  exact mfderiv_comp x (contMDiff_right.mdifferentiableAt (by simp))
    (alignment.contMDiff_toFun.mdifferentiableAt (by simp))

theorem injective_mfderiv_alignedLeft (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) alignedLeft x) := by
  rw [mfderiv_alignedLeft]
  exact (injective_mfderiv_left (alignment x)).comp
    (alignment.mfderivToContinuousLinearEquiv (by simp) x).injective

theorem injective_mfderiv_alignedRight (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) alignedRight x) := by
  rw [mfderiv_alignedRight]
  exact (injective_mfderiv_right (alignment x)).comp
    (alignment.mfderivToContinuousLinearEquiv (by simp) x).injective

theorem aligned_pairTransverse (x y : Sphere 3) (h : alignedLeft x = alignedRight y) :
    Surjective ((mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) alignedLeft x).coprod
      (mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) alignedRight y)) := by
  intro z
  obtain ⟨⟨u, v⟩, huv⟩ := pairTransverse (alignment x) (alignment y) h z
  let Dx := alignment.mfderivToContinuousLinearEquiv (by simp) x
  let Dy := alignment.mfderivToContinuousLinearEquiv (by simp) y
  refine ⟨(Dx.symm u, Dy.symm v), ?_⟩
  rw [mfderiv_alignedLeft, mfderiv_alignedRight]
  change ((leftDerivative (alignment x)).coprod (rightDerivative (alignment y)))
    (Dx (Dx.symm u), Dy (Dy.symm v)) = z
  exact (congrArg ((leftDerivative (alignment x)).coprod (rightDerivative (alignment y)))
    (Prod.ext (Dx.apply_symm_apply u) (Dy.apply_symm_apply v))).trans huv

theorem aligned_intersectionPairs_ncard :
    (MapIntersections.pairs alignedLeft alignedRight).ncard = 2 :=
  (MapIntersections.pairs_ncard_reparametrize left right alignment.toEquiv alignment.toEquiv).trans
    intersectionPairs_ncard

theorem aligned_intersectionParity_zero : MapIntersections.parity alignedLeft alignedRight = 0 := by
  rw [MapIntersections.parity, aligned_intersectionPairs_ncard]
  decide

end NoExoticSixSphere.DoubleCrossingSpherePair
