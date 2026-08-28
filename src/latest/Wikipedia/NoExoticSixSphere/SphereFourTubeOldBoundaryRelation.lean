import Wikipedia.NoExoticSixSphere.SphereFourTubeHalfImageCoordinates

/-!
# The half-image relation for the original boundary class

The old zero set enters the core complement by its original ambient
points. Radial retraction fixes those points exactly and agrees with
the already constructed native old-zero inclusion into the new half.
Thus the exact even-longitude relation holds for an arbitrary integral
old-boundary class, including when the old boundary is disconnected.
No quadratic comparison between its components is asserted here.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.PeriodTorusHigherHomology ProductThirdHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [T2Space M]
  [IsManifold (𝓡 7) ∞ M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

def zeroToHalf (t : C(M, ℝ)) : C({x : M // t x = 0}, NonnegativeHalf t) :=
  ⟨fun p ↦ ⟨p.val, p.property.ge⟩, continuous_subtype_val.subtype_mk _⟩

variable (hΦ : Φ.source = univ) (t τ : C(M, ℝ))
  (hpos : ∀ x ∈ Φ.target, 0 < t x)
  (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x)
  (hhalf : ∀ x, 0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1)
  (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)

def oldZeroToComplement : C({x : M // t x = 0}, halfCoreComplement Φ t) :=
  ⟨fun p ↦ ⟨zeroToHalf t p, fun hx ↦
    (ne_of_gt (hpos p.val ((core_mem_iff Φ hΦ p.val).mp hx).1)) p.property⟩,
    (zeroToHalf t).continuous.subtype_mk _⟩

def oldZeroToNewHalf : C({x : M // t x = 0}, NonnegativeHalf τ) := by
  let i : C({x : M // t x = 0}, {x : M // τ x = 0}) :=
    ⟨oldZeroInclusion Φ hΦ t τ hpos hout, continuous_subtype_val.subtype_mk _⟩
  exact (zeroToHalf τ).comp i

theorem inclusion_oldZeroToComplement :
    (subtypeInclusion (halfCoreComplement Φ t)).comp (oldZeroToComplement Φ hΦ t hpos) =
      zeroToHalf t := rfl

theorem retraction_oldZeroToComplement :
    (halfComplementRetraction Φ hΦ t τ hpos hhalf).comp
      (oldZeroToComplement Φ hΦ t hpos) = oldZeroToNewHalf Φ hΦ t τ hpos hout := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply rawRetraction_eq_of_exterior Φ hΦ
  intro hx
  exact (ne_of_gt (hpos p.val ((mem_openRegion_iff Φ hΦ 1 p.val).mp hx).1)) p.property

include hhalf in
theorem old_boundary_class_of_double_core_image
    (x : SingularHomology {p : M // t p = 0} 3)
    (hclass : singularHomologyMap (zeroToHalf t) 3 x =
      (2 : ℤ) • singularHomologyMap (coreInHalf Φ hΦ t hpos) 3 (unitSphereTopClass 2)) :
    ∃ v : SingularHomology (Sphere 3 × Sphere 3) 3,
      singularHomologyMap (oldZeroToNewHalf Φ hΦ t τ hpos hout) 3 x =
        singularHomologyMap (boundaryInNewHalf Φ hΦ τ hinner) 3 v ∧
      singularHomologyMap ContinuousMap.fst 3 v = (2 : ℤ) • unitSphereTopClass 2 := by
  let a := singularHomologyMap (oldZeroToComplement Φ hΦ t hpos) 3 x
  have ha : singularHomologyMap (subtypeInclusion (halfCoreComplement Φ t)) 3 a =
      (2 : ℤ) • singularHomologyMap (coreInHalf Φ hΦ t hpos) 3 (unitSphereTopClass 2) := by
    change singularHomologyMap (subtypeInclusion (halfCoreComplement Φ t)) 3
      (singularHomologyMap (oldZeroToComplement Φ hΦ t hpos) 3 x) = _
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, inclusion_oldZeroToComplement]
    exact hclass
  obtain ⟨v, hv, hfst⟩ :=
    exists_boundary_class_of_double_core_image Φ hΦ t τ hpos hhalf hinner a ha
  refine ⟨v, ?_, hfst⟩
  change singularHomologyMap (halfComplementRetraction Φ hΦ t τ hpos hhalf) 3
    (singularHomologyMap (oldZeroToComplement Φ hΦ t hpos) 3 x) = _ at hv
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, retraction_oldZeroToComplement] at hv
  exact hv

include hhalf in
theorem old_boundary_even_longitude_relation
    (x : SingularHomology {p : M // t p = 0} 3)
    (hclass : singularHomologyMap (zeroToHalf t) 3 x =
      (2 : ℤ) • singularHomologyMap (coreInHalf Φ hΦ t hpos) 3 (unitSphereTopClass 2))
    (s v₀ : Sphere 3) : ∃ k : ℤ,
    singularHomologyMap (oldZeroToNewHalf Φ hΦ t τ hpos hout) 3 x =
      (2 : ℤ) • singularHomologyMap
        ((boundaryInNewHalf Φ hΦ τ hinner).comp (leftSection v₀)) 3 (unitSphereTopClass 2) +
      k • singularHomologyMap
        ((boundaryInNewHalf Φ hΦ τ hinner).comp (rightSection s)) 3 (unitSphereTopClass 2) := by
  obtain ⟨v, hv, hfst⟩ :=
    old_boundary_class_of_double_core_image Φ hΦ t τ hpos hout hhalf hinner x hclass
  obtain ⟨k, hk⟩ := two_longitude_decomposition s v₀ v hfst
  refine ⟨k, ?_⟩
  rw [hv, hk, map_add, map_zsmul, map_zsmul]
  simp only [singularHomologyMap_comp, LinearMap.comp_apply]

end NoExoticSixSphere.SphereFourTube
