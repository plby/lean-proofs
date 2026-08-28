import Wikipedia.NoExoticSixSphere.SphereFourTubeHalfCoverMaps
import Wikipedia.NoExoticSixSphere.ProductThirdHomologyFactors

/-!
# The exact integral half-image relation from the actual tube cover

A class in the full core complement whose old-half image is twice the
marked core image comes from a unit tube-boundary class after radial
retraction. The longitude projection of this boundary class is exactly
twice the original sphere generator. The proof does not require that
the core-to-half homology map be injective, including on torsion classes.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (t τ : C(M, ℝ))
  (hpos : ∀ x ∈ Φ.target, 0 < t x)
  (hhalf : ∀ x, 0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1)
  (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)

theorem exists_boundary_class_of_double_core_image
    (a : SingularHomology (halfCoreComplement Φ t) 3)
    (hclass : singularHomologyMap (subtypeInclusion (halfCoreComplement Φ t)) 3 a =
      (2 : ℤ) • singularHomologyMap (coreInHalf Φ hΦ t hpos) 3 (unitSphereTopClass 2)) :
    ∃ v : SingularHomology (Sphere 3 × Sphere 3) 3,
      singularHomologyMap (halfComplementRetraction Φ hΦ t τ hpos hhalf) 3 a =
        singularHomologyMap (boundaryInNewHalf Φ hΦ τ hinner) 3 v ∧
      singularHomologyMap ContinuousMap.fst 3 v = (2 : ℤ) • unitSphereTopClass 2 := by
  let U := halfCoreComplement Φ t
  let V := halfOpenTube Φ t
  let c := singularHomologyMap (tubeCore Φ hΦ t hpos) 3 (unitSphereTopClass 2)
  have hcore : singularHomologyMap (subtypeInclusion V) 3 c =
      singularHomologyMap (coreInHalf Φ hΦ t hpos) 3 (unitSphereTopClass 2) := by
    change singularHomologyMap (subtypeInclusion V) 3
      (singularHomologyMap (tubeCore Φ hΦ t hpos) 3 (unitSphereTopClass 2)) = _
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, inclusion_tubeCore]
  have hker : (a, -((2 : ℤ) • c)) ∈ LinearMap.ker (rightHomologyMap U V 3) := by
    rw [LinearMap.mem_ker, rightHomologyMap_apply]
    change singularHomologyMap (subtypeInclusion U) 3 a +
      singularHomologyMap (subtypeInclusion V) 3 (-((2 : ℤ) • c)) = 0
    rw [map_neg, map_zsmul, hcore, hclass, add_neg_cancel]
  have hrange : (a, -((2 : ℤ) • c)) ∈ LinearMap.range (leftHomologyMap U V 3) := by
    rw [exact_at_pair U V (isOpen_halfCoreComplement Φ hΦ t)
      (isOpen_halfOpenTube Φ hΦ t) (halfCoreComplement_union_halfOpenTube Φ t) 3]
    exact hker
  obtain ⟨z, hz⟩ := hrange
  have hleft : singularHomologyMap (overlapLeft Φ t) 3 z = a := by
    have h := congrArg Prod.fst hz
    rw [leftHomologyMap_apply] at h
    exact h
  have hright : singularHomologyMap (overlapRight Φ t) 3 z = (2 : ℤ) • c := by
    have h := congrArg Prod.snd hz
    rw [leftHomologyMap_apply] at h
    exact neg_injective h
  let b : Sphere 3 := basePoint 3
  let v := singularHomologyMap (overlapDirection Φ hΦ t b) 3 z
  refine ⟨v, ?_, ?_⟩
  · rw [← hleft, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
      overlap_retraction, singularHomologyMap_comp]
    rfl
  · change singularHomologyMap ContinuousMap.fst 3
      (singularHomologyMap (overlapDirection Φ hΦ t b) 3 z) = _
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, ← overlap_projection,
      singularHomologyMap_comp, LinearMap.comp_apply, hright, map_zsmul]
    change (2 : ℤ) • singularHomologyMap (halfTubeProjection Φ hΦ t) 3
      (singularHomologyMap (tubeCore Φ hΦ t hpos) 3 (unitSphereTopClass 2)) = _
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, halfTubeProjection_tubeCore,
      singularHomologyMap_id]
    rfl

end NoExoticSixSphere.SphereFourTube
