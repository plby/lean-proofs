import Wikipedia.NoExoticSixSphere.CayleyDifferential
import Wikipedia.NoExoticSixSphere.OrthogonalExponential
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# Local invertibility of the orthogonal exponential in Cayley coordinates

The exponential in Cayley coordinates has differential `-1/2` at zero.
The inverse-function theorem gives a smooth local inverse on the genuine
open set where the exponential lies in the identity Cayley chart.
-/

open scoped Manifold ContDiff
open Set

namespace NoExoticSixSphere.OrthogonalExponential

open GLOrthonormalization CayleyTransform CayleyAtlas

variable {n : ℕ}

noncomputable def inCoordinates (K : SkewOperators n) : SkewOperators n :=
  skewProjection (fraction (exp K).1.1)

theorem inCoordinates_zero : inCoordinates (0 : SkewOperators n) = 0 := by
  rw [inCoordinates, exp_zero]
  change skewProjection (fraction (1 : Vector n →L[ℝ] Vector n)) = 0
  rw [fraction_one, map_zero]

theorem hasFDerivAt_exp_operator_zero :
    HasFDerivAt (fun K : SkewOperators n ↦ (exp K).1.1)
      (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL 0 := by
  let L := (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL
  have he : HasFDerivAt (NormedSpace.exp : (Vector n →L[ℝ] Vector n) → _)
      (1 : (Vector n →L[ℝ] Vector n) →L[ℝ] (Vector n →L[ℝ] Vector n)) (L 0) := by
    simpa only [map_zero] using (hasFDerivAt_exp_zero (𝕂 := ℝ)
      (𝔸 := Vector n →L[ℝ] Vector n))
  convert! he.comp (0 : SkewOperators n) L.hasFDerivAt using 1

theorem hasFDerivAt_fraction_exp_zero :
    HasFDerivAt (fun K : SkewOperators n ↦ fraction (exp K).1.1)
      ((-(1 / 2) : ℝ) • (skewAdjoint.submodule ℝ
        (Vector n →L[ℝ] Vector n)).subtypeL) 0 := by
  have hf : HasFDerivAt (fraction (n := n))
      ((-(1 / 2) : ℝ) • (1 : (Vector n →L[ℝ] Vector n) →L[ℝ]
        (Vector n →L[ℝ] Vector n))) (exp (0 : SkewOperators n)).1.1 := by
    rw [exp_zero]
    exact hasFDerivAt_fraction_one
  simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp] using!
    (HasFDerivAt.comp (f := fun K : SkewOperators n ↦ (exp K).1.1)
      (g := fraction (n := n)) (0 : SkewOperators n) hf
      (hasFDerivAt_exp_operator_zero (n := n)))

theorem hasFDerivAt_inCoordinates_zero :
    HasFDerivAt (inCoordinates (n := n))
      ((-(1 / 2) : ℝ) • (1 : SkewOperators n →L[ℝ] SkewOperators n)) 0 := by
  have hd := HasFDerivAt.comp
    (f := fun K : SkewOperators n ↦ fraction (exp K).1.1)
    (g := skewProjection (n := n)) (0 : SkewOperators n)
    (skewProjection (n := n)).hasFDerivAt (hasFDerivAt_fraction_exp_zero (n := n))
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro K
  change (-(1 / 2) : ℝ) • K = skewProjection ((-(1 / 2) : ℝ) •
    (K : Vector n →L[ℝ] Vector n))
  rw [map_smul, skewProjection_coe]

def coordinateDomain (n : ℕ) : Set (SkewOperators n) := exp ⁻¹' domain

theorem isOpen_coordinateDomain (n : ℕ) : IsOpen (coordinateDomain n) :=
  isOpen_domain.preimage contMDiff_exp.continuous

theorem zero_mem_coordinateDomain (n : ℕ) : 0 ∈ coordinateDomain n := by
  change exp (0 : SkewOperators n) ∈ domain
  rw [exp_zero]
  exact identity_mem_domain

theorem contDiffOn_inCoordinates : ContDiffOn ℝ ∞ (inCoordinates (n := n))
    (coordinateDomain n) := by
  intro K hK
  have hf : ContDiffAt ℝ ∞ (fun K : SkewOperators n ↦ fraction (exp K).1.1) K :=
    ContDiffAt.comp (f := fun K : SkewOperators n ↦ (exp K).1.1)
      (g := fraction (n := n)) K
      (contDiffAt_fraction (n := n) _ hK) contDiff_exp_operator.contDiffAt
  exact ((skewProjection (n := n)).contDiff.contDiffAt.comp K hf).contDiffWithinAt

theorem inCoordinates_eq_chart (K : SkewOperators n) (hK : K ∈ coordinateDomain n) :
    inCoordinates K = CayleyTransform.chart (exp K) := by
  change skewProjection (fraction (exp K).1.1) = coordinates (exp K)
  rw [coordinates_of_mem _ hK]
  exact skewProjection_fraction (n := n) (exp K) hK

theorem inCoordinates_fderiv_isInvertible :
    (fderiv ℝ (inCoordinates (n := n)) 0).IsInvertible := by
  rw [(hasFDerivAt_inCoordinates_zero (n := n)).fderiv]
  refine ⟨ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := SkewOperators n)
    (Units.mk0 (-(1 / 2) : ℝ) (by norm_num)), ?_⟩
  apply ContinuousLinearMap.ext
  intro K
  rfl

/-- A smooth inverse exists locally in the verified Cayley chart. -/
theorem exists_coordinatePartialDiffeomorph :
    ∃ d : PartialDiffeomorph 𝓘(ℝ, SkewOperators n) 𝓘(ℝ, SkewOperators n)
        (SkewOperators n) (SkewOperators n) ∞,
      0 ∈ d.source ∧ d.source ⊆ coordinateDomain n ∧ (d : _ → _) = inCoordinates :=
  exists_partialDiffeomorph_of_contDiffOn (isOpen_coordinateDomain n)
    (zero_mem_coordinateDomain n) contDiffOn_inCoordinates inCoordinates_fderiv_isInvertible

end NoExoticSixSphere.OrthogonalExponential
