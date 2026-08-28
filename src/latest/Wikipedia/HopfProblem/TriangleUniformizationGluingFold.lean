import Wikipedia.HopfProblem.SpecialPeriodsTriangleTiling
import Mathlib.Topology.Piecewise

/-!
# Folding a real-boundary map across the Ford symmetry axis

The input is an actual continuous complex-valued map on the closed
half-Ford triangle, real-valued on its boundary.  The reflected formula
defines a continuous map on the full closed Ford polygon.  Its values
agree on both concrete paired sides.  No quotient descent or boundary
orbit classification is presumed in the input data.
-/

noncomputable section

open Set UpperHalfPlane Complex
open scoped Topology MatrixGroups ComplexConjugate

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

/-- The finite closed-half-triangle data needed for the continuous fold.
Later analytic input supplies such a map from the normalized Riemann map. -/
structure BoundaryMap where
  toFun : ℍ → ℂ
  continuousOn : ContinuousOn toFun halfFordRegion
  boundary_real : ∀ z ∈ halfFordRegion, z ∉ halfFordInterior → (toFun z).im = 0

instance : CoeFun BoundaryMap (fun _ => ℍ → ℂ) := ⟨BoundaryMap.toFun⟩

namespace BoundaryMap

variable (D : BoundaryMap)

/-- The actual reflected formula, defined on the ambient upper half-plane. -/
def foldedFordMap (z : ℍ) : ℂ := by
  classical
  exact if z.re ≤ -(1 / 2) then D z else conj (D (rightReflection z))

theorem foldedFordMap_of_left {z : ℍ} (hz : z.re ≤ -(1 / 2)) :
    D.foldedFordMap z = D z := by
  simp only [foldedFordMap, if_pos hz]

theorem foldedFordMap_of_right {z : ℍ} (hz : -(1 / 2) < z.re) :
    D.foldedFordMap z = conj (D (rightReflection z)) := by
  simp only [foldedFordMap, if_neg hz.not_ge]

theorem foldedFordMap_eqOn_left : EqOn D.foldedFordMap D halfFordRegion :=
  fun _ hz => D.foldedFordMap_of_left hz.2

theorem real_at_axis {z : ℍ} (hz : z ∈ fordRegion) (hx : z.re = -(1 / 2)) :
    (D z).im = 0 := by
  apply D.boundary_real z ⟨hz, hx.le⟩
  intro hi
  have hh : z.re < -(1 / 2) := hi.2
  linarith

/-- The reflected formula agrees with the conjugate original formula,
including the common vertical side. -/
theorem foldedFordMap_reflected (z : ℍ) (hz : z ∈ halfFordRegion) :
    D.foldedFordMap (rightReflection z) = conj (D z) := by
  by_cases hx : (rightReflection z).re ≤ -(1 / 2)
  · have hcut : z.re = -(1 / 2) := by
      rw [rightReflection_re] at hx
      have hleft : z.re ≤ -(1 / 2) := hz.2
      linarith
    have hfix : rightReflection z = z := (rightReflection_fixed_iff z).mpr hcut
    rw [hfix, D.foldedFordMap_of_left hz.2]
    exact (Complex.conj_eq_iff_im.mpr (D.real_at_axis hz.1 hcut)).symm
  · simp only [foldedFordMap, if_neg hx]
    rw [rightReflection_involutive z]

theorem foldedFordMap_eqOn_right :
    EqOn D.foldedFordMap (fun z => conj (D (rightReflection z)))
      (rightReflection '' halfFordRegion) := by
  rintro z ⟨w, hw, rfl⟩
  change D.foldedFordMap (rightReflection w) = conj (D (rightReflection (rightReflection w)))
  rw [D.foldedFordMap_reflected w hw, rightReflection_involutive w]

theorem foldedFordMap_continuousOn : ContinuousOn D.foldedFordMap fordRegion := by
  have hl : ContinuousOn D.foldedFordMap halfFordRegion :=
    D.continuousOn.congr D.foldedFordMap_eqOn_left
  have hm : MapsTo rightReflection (rightReflection '' halfFordRegion) halfFordRegion := by
    rintro z ⟨w, hw, rfl⟩
    rw [rightReflection_involutive w]
    exact hw
  have hr : ContinuousOn D.foldedFordMap (rightReflection '' halfFordRegion) := by
    apply (Complex.continuous_conj.continuousOn.comp
      (D.continuousOn.comp rightReflection.continuous.continuousOn hm)
      (mapsTo_univ _ _)).congr
    exact D.foldedFordMap_eqOn_right
  rw [← halfFordRegion_union_reflection]
  exact hl.union_of_isClosed hr halfFordRegion_isClosed
    (rightReflection.isClosedMap _ halfFordRegion_isClosed)

/-- Reflection conjugates the folded value on the whole Ford polygon. -/
theorem foldedFordMap_rightReflection {z : ℍ} (hz : z ∈ fordRegion) :
    D.foldedFordMap (rightReflection z) = conj (D.foldedFordMap z) := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [D.foldedFordMap_of_left hx]
    exact D.foldedFordMap_reflected z ⟨hz, hx⟩
  · have hright : -(1 / 2) < z.re := lt_of_not_ge hx
    have hleft : (rightReflection z).re ≤ -(1 / 2) := by
      rw [rightReflection_re]
      linarith
    rw [D.foldedFordMap_of_left hleft, D.foldedFordMap_of_right hright, conj_conj]

/-- The whole boundary of the closed Ford polygon has real folded values. -/
theorem foldedFordMap_real_of_not_mem_interior {z : ℍ} (hz : z ∈ fordRegion)
    (hi : z ∉ fordInterior) : (D.foldedFordMap z).im = 0 := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [D.foldedFordMap_of_left hx]
    exact D.boundary_real z ⟨hz, hx⟩ (fun hh => hi hh.1)
  · have hright : -(1 / 2) < z.re := lt_of_not_ge hx
    have hleft : (rightReflection z).re ≤ -(1 / 2) := by
      rw [rightReflection_re]
      linarith
    have hr : rightReflection z ∈ halfFordRegion :=
      ⟨rightReflection_mapsTo_fordRegion hz, hleft⟩
    have hn : rightReflection z ∉ halfFordInterior := by
      intro hh
      exact hi ((rightReflection_mem_fordInterior_iff z).mp hh.1)
    rw [D.foldedFordMap_of_right hright, Complex.conj_im, D.boundary_real _ hr hn, neg_zero]

theorem foldedFordMap_rightReflection_boundary {z : ℍ} (hz : z ∈ fordRegion)
    (hi : z ∉ fordInterior) :
    D.foldedFordMap (rightReflection z) = D.foldedFordMap z := by
  rw [D.foldedFordMap_rightReflection hz]
  exact Complex.conj_eq_iff_im.mpr (D.foldedFordMap_real_of_not_mem_interior hz hi)

/-- Agreement on the actual paired circular sides. -/
theorem foldedFordMap_generatorOne_side {z : ℍ} (hz : z ∈ leftCircularArc) :
    D.foldedFordMap (generatorOneSL • z) = D.foldedFordMap z := by
  rw [generatorOne_eq_rightReflection_of_norm_add_one z hz.2]
  apply D.foldedFordMap_rightReflection_boundary hz.1
  intro hi
  have hn := hi.2.2.1
  rw [hz.2] at hn
  exact lt_irrefl _ hn

/-- Agreement on the actual paired vertical cusp sides. -/
theorem foldedFordMap_cusp_side {z : ℍ} (hz : z ∈ rightVerticalRay) :
    D.foldedFordMap (cuspSL • z) = D.foldedFordMap z := by
  rw [cusp_eq_rightReflection_of_re_eq_stripRight z hz.2]
  apply D.foldedFordMap_rightReflection_boundary hz.1
  intro hi
  have hn := hi.2.1
  rw [hz.2] at hn
  exact lt_irrefl _ hn

end BoundaryMap
end Wikipedia.HopfProblem.TriangleUniformizationGluing
