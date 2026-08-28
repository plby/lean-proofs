import Wikipedia.HopfProblem.TriangleHalfPlaneHomeomorphData
import Wikipedia.HopfProblem.TriangleRiemannNormalization

/-!
# The actual normalized Riemann map supplies all finite gluing inputs

The constructed homeomorphism of the finite half-Ford triangle supplies
the signed half-plane map, including its real boundary, injectivity,
surjectivity and local properness. In the open triangle it is the
holomorphic cross-ratio of the original Riemann map. Its two finite
marked values remain exactly zero and one.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannSphere RiemannSphere.MobiusCircle
open TriangleUniformizationGluing

/-- The actual normalized finite map, ready for the proved reflection gluing. -/
def triangleSignedHalfPlaneMap : SignedHalfPlaneMap :=
  signedHalfPlaneMapOfHomeomorph normalizationOrientation_ne_zero
    halfFordNormalizationHomeomorph halfFordNormalizationHomeomorph_strict_iff

@[simp] theorem triangleSignedHalfPlaneMap_coe (z : halfFordRegion) :
    triangleSignedHalfPlaneMap z = (halfFordNormalizationHomeomorph z : ℂ) :=
  signedHalfPlaneMapOfHomeomorph_apply normalizationOrientation_ne_zero
    halfFordNormalizationHomeomorph halfFordNormalizationHomeomorph_strict_iff z

theorem triangleSignedHalfPlaneMap_of_mem {z : ℍ} (hz : z ∈ halfFordRegion) :
    triangleSignedHalfPlaneMap z = (halfFordNormalizationHomeomorph ⟨z, hz⟩ : ℂ) :=
  triangleSignedHalfPlaneMap_coe ⟨z, hz⟩

theorem triangleSignedHalfPlaneMap_of_interior (z : ℍ) (hz : z ∈ halfFordInterior) :
    triangleSignedHalfPlaneMap z =
      crossRatio normalizationZeroValue normalizationOneValue normalizationPoleValue
        (triangleMap (z : ℂ)) := by
  rw [triangleSignedHalfPlaneMap_of_mem (halfFordInterior_subset_halfFordRegion hz)]
  exact halfFordNormalizationHomeomorph_apply_of_interior z hz

@[simp] theorem triangleSignedHalfPlaneMap_centerOne :
    triangleSignedHalfPlaneMap centerOne = 0 := by
  rw [triangleSignedHalfPlaneMap_of_mem centerOne_mem_halfFordRegion]
  exact halfFordNormalizationHomeomorph_centerOne

@[simp] theorem triangleSignedHalfPlaneMap_centerTwo :
    triangleSignedHalfPlaneMap centerTwo = 1 := by
  rw [triangleSignedHalfPlaneMap_of_mem centerTwo_mem_halfFordRegion]
  exact halfFordNormalizationHomeomorph_centerTwo

/-- Properness is proved from the actual closed-half homeomorphism. -/
theorem triangleSignedHalfPlaneMap_isProperMap :
    IsProperMap (fun z : halfFordRegion => triangleSignedHalfPlaneMap z) :=
  halfFordHomeomorphExtension_isProperMap halfFordNormalizationHomeomorph

/-- The actual normalized finite map is holomorphic on the original
open triangle, with no analytic input left to supply to the gluing. -/
theorem triangleSignedHalfPlaneMap_holomorphicOn :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω triangleSignedHalfPlaneMap halfFordInterior := by
  have hab : normalizationZeroValue ≠ normalizationOneValue := by
    simpa only [normalizationZeroValue_eq, normalizationOneValue_eq] using
      triangleCorner_boundary_values_ne
  have hc : ‖normalizationPoleValue‖ = 1 := by
    simpa only [normalizationPoleValue_eq] using triangleIdealGerm.unit
  have hf : ContDiffOn ℂ ω triangleMap triangleInterior :=
    (triangleMap_differentiable.analyticOnNhd triangleInterior_isOpen).contDiffOn
      triangleInterior_isOpen.uniqueDiffOn
  have hcr : ContDiffOn ℂ ω
      (crossRatio normalizationZeroValue normalizationOneValue normalizationPoleValue)
      {z : ℂ | ‖z‖ < 1} := crossRatio_holomorphicOn_disc hab hc
  have hcomp : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : ℂ => crossRatio normalizationZeroValue normalizationOneValue
        normalizationPoleValue (triangleMap z)) triangleInterior :=
    contMDiffOn_iff_contDiffOn.mpr
      (hcr.comp hf (fun _ hz => triangleMap_norm_lt_one hz))
  have hu := hcomp.comp UpperHalfPlane.contMDiff_coe.contMDiffOn
    (show MapsTo ((↑) : ℍ → ℂ) halfFordInterior triangleInterior from by
      intro z hz
      simpa only [halfFordInterior_eq_preimage_triangleInterior, mem_preimage] using hz)
  apply hu.congr
  intro z hz
  exact triangleSignedHalfPlaneMap_of_interior z hz

end Wikipedia.HopfProblem.RiemannMapping
