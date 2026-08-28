import Wikipedia.HopfProblem.DegreeCollapseSevenHalfTorsionDecrease

/-!
# Preserve the actual half-exterior classes under positive tube shrinking

Two normalized products related by a constant positive transverse scale
have the same original core and defining time. Their exterior homotopy
equivalence factors through that literal common core complement. Retraction
of a smaller radial sphere gives the original corner exactly, so the
section, meridian, and every integral relation between them are retained.
-/

noncomputable section

open Function Set Metric ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2)
  (B : FramedAttachingProduct e a f) (hB : B.radius = 2)
  (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
  (ht : ∀ (s : Sphere 3) (w : Vector 4), B.tube (s, w) = A.tube (s, r • w))
  (T : TimeData A)

def scaledTimeData : TimeData B where
  time := T.time
  smooth := T.smooth
  regular := T.regular
  margin := T.margin
  margin_pos := T.margin_pos
  tube_time s w hw := by
    rw [ht]
    apply T.tube_time
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hA]
    have hw2 : ‖w‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right, hB] using hw
    exact (mul_le_of_le_one_left (norm_nonneg w) hr1).trans hw2

theorem scaled_attachingSphere :
    (halfBoundaryPair B hB (scaledTimeData A hA B hB r hr hr1 ht T)).attachingSphere =
      (halfBoundaryPair A hA T).attachingSphere := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  exact (halfBoundaryPair_attachingSphere B hB _ s).trans
    (halfBoundaryPair_attachingSphere A hA T s).symm

def scaledCoreComplementHomeomorph :
    (halfBoundaryPair B hB (scaledTimeData A hA B hB r hr hr1 ht T)).OldComplement ≃ₜ
      (halfBoundaryPair A hA T).OldComplement :=
  Homeomorph.setCongr (by
    change (range (halfBoundaryPair B hB
      (scaledTimeData A hA B hB r hr hr1 ht T)).attachingSphere)ᶜ =
        (range (halfBoundaryPair A hA T).attachingSphere)ᶜ
    rw [scaled_attachingSphere]
    rfl)

theorem scaled_corner_in_complement :
    (scaledCoreComplementHomeomorph A hA B hB r hr hr1 ht T : C(_, _)).comp
      ((SurgeryExteriorRetraction.exteriorInclusion
        (halfBoundaryPair B hB (scaledTimeData A hA B hB r hr hr1 ht T))).comp
          (halfCornerMap B hB (scaledTimeData A hA B hB r hr hr1 ht T))) =
      SurgeryExteriorRetraction.radialSphereMap (halfBoundaryPair A hA T) ⟨r, hr, hr1⟩ := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  apply Subtype.ext
  exact ht q.1 q.2.val

def scaledExteriorHomotopyEquiv :
    HalfExterior B hB (scaledTimeData A hA B hB r hr hr1 ht T) ≃ₕ HalfExterior A hA T :=
  (SurgeryExteriorRetraction.homotopyEquiv
    (halfBoundaryPair B hB (scaledTimeData A hA B hB r hr hr1 ht T))).trans
      ((scaledCoreComplementHomeomorph A hA B hB r hr hr1 ht T).toHomotopyEquiv.trans
        (SurgeryExteriorRetraction.homotopyEquiv (halfBoundaryPair A hA T)).symm)

theorem scaledExterior_corner :
    (scaledExteriorHomotopyEquiv A hA B hB r hr hr1 ht T).toFun.comp
      (halfCornerMap B hB (scaledTimeData A hA B hB r hr hr1 ht T)) = halfCornerMap A hA T := by
  change (SurgeryExteriorRetraction.retraction (halfBoundaryPair A hA T)).comp
    ((scaledCoreComplementHomeomorph A hA B hB r hr hr1 ht T : C(_, _)).comp
      ((SurgeryExteriorRetraction.exteriorInclusion
        (halfBoundaryPair B hB (scaledTimeData A hA B hB r hr hr1 ht T))).comp
          (halfCornerMap B hB (scaledTimeData A hA B hB r hr hr1 ht T)))) = _
  rw [scaled_corner_in_complement, SurgeryExteriorRetraction.retraction_radialSphereMap]
  rfl

theorem scaledExterior_section (v : Sphere 3) :
    (scaledExteriorHomotopyEquiv A hA B hB r hr hr1 ht T).toFun.comp
      (halfSectionMap B hB (scaledTimeData A hA B hB r hr hr1 ht T) v) =
        halfSectionMap A hA T v := by
  change ((scaledExteriorHomotopyEquiv A hA B hB r hr hr1 ht T).toFun.comp
    (halfCornerMap B hB (scaledTimeData A hA B hB r hr hr1 ht T))).comp
      (ProductThirdHomology.leftSection v) = _
  rw [scaledExterior_corner]
  rfl

theorem scaledExterior_meridian (s : Sphere 3) :
    (scaledExteriorHomotopyEquiv A hA B hB r hr hr1 ht T).toFun.comp
      (halfMeridianMap B hB (scaledTimeData A hA B hB r hr hr1 ht T) s) =
        halfMeridianMap A hA T s := by
  change ((scaledExteriorHomotopyEquiv A hA B hB r hr hr1 ht T).toFun.comp
    (halfCornerMap B hB (scaledTimeData A hA B hB r hr hr1 ht T))).comp
      (ProductThirdHomology.rightSection s) = _
  rw [scaledExterior_corner]
  rfl

def scaledExteriorHomologyEquiv :
    SingularHomology (HalfExterior B hB (scaledTimeData A hA B hB r hr hr1 ht T)) 3 ≃ₗ[ℤ]
      SingularHomology (HalfExterior A hA T) 3 :=
  homotopyEquivHomologyEquiv (scaledExteriorHomotopyEquiv A hA B hB r hr hr1 ht T) 3

theorem scaledExterior_section_class (v : Sphere 3) :
    scaledExteriorHomologyEquiv A hA B hB r hr hr1 ht T
      (halfSectionClass B hB (scaledTimeData A hA B hB r hr hr1 ht T) v) =
        halfSectionClass A hA T v := by
  change singularHomologyMap (scaledExteriorHomotopyEquiv A hA B hB r hr hr1 ht T).toFun 3
    (singularHomologyMap (halfSectionMap B hB
      (scaledTimeData A hA B hB r hr hr1 ht T) v) 3 (SphereHomology.unitSphereTopClass 2)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, scaledExterior_section]
  rfl

theorem scaledExterior_meridian_class (s : Sphere 3) :
    scaledExteriorHomologyEquiv A hA B hB r hr hr1 ht T
      (halfMeridianClass B hB (scaledTimeData A hA B hB r hr hr1 ht T) s) =
        halfMeridianClass A hA T s := by
  change singularHomologyMap (scaledExteriorHomotopyEquiv A hA B hB r hr hr1 ht T).toFun 3
    (singularHomologyMap (halfMeridianMap B hB
      (scaledTimeData A hA B hB r hr hr1 ht T) s) 3 (SphereHomology.unitSphereTopClass 2)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, scaledExterior_meridian]
  rfl

theorem scaledExterior_relation (v s : Sphere 3) (l p : ℤ)
    (h : l • halfSectionClass A hA T v + p • halfMeridianClass A hA T s = 0) :
    l • halfSectionClass B hB (scaledTimeData A hA B hB r hr hr1 ht T) v +
      p • halfMeridianClass B hB (scaledTimeData A hA B hB r hr hr1 ht T) s = 0 := by
  apply (scaledExteriorHomologyEquiv A hA B hB r hr hr1 ht T).injective
  rw [map_add, map_zsmul, map_zsmul, scaledExterior_section_class,
    scaledExterior_meridian_class, map_zero]
  exact h

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist
