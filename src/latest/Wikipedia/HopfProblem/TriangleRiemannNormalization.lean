import Wikipedia.HopfProblem.TriangleRiemannNormalizationAbstract
import Wikipedia.HopfProblem.TriangleRiemannNormalizationMarks
import Wikipedia.HopfProblem.TriangleClosedDomainFinite

/-!
# Actual finite half-Ford normalization

The actual compactified-triangle homeomorphism supplies three distinct
unit-circle values. Its cross-ratio normalization, composed with the
literal finite-source homeomorphism, identifies the original closed
half-Ford region with one closed complex half-plane. The two elliptic
vertices map to zero and one. On the open triangle the map is exactly the
cross-ratio of the original holomorphic Riemann map.
-/

noncomputable section

open Set UpperHalfPlane

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannSphere RiemannSphere.MobiusCircle

/-- The first marked value of the actual closed-disc homeomorphism. -/
def normalizationZeroValue : ℂ := triangleClosedDiscHomeomorph triangleClosedCenterOne

/-- The second marked value of the actual closed-disc homeomorphism. -/
def normalizationOneValue : ℂ := triangleClosedDiscHomeomorph triangleClosedCenterTwo

/-- The ideal marked value of the actual closed-disc homeomorphism. -/
def normalizationPoleValue : ℂ := triangleClosedDiscHomeomorph triangleClosedInfinity

@[simp] theorem normalizationZeroValue_eq :
    normalizationZeroValue = triangleCornerThreeGerm.function 0 :=
  triangleClosedDiscHomeomorph_centerOne

@[simp] theorem normalizationOneValue_eq :
    normalizationOneValue = triangleCornerFourGerm.function 0 :=
  triangleClosedDiscHomeomorph_centerTwo

@[simp] theorem normalizationPoleValue_eq :
    normalizationPoleValue = triangleIdealGerm.function 0 :=
  triangleClosedDiscHomeomorph_infty

/-- The explicit nonzero real coefficient selecting the image half-plane. -/
def normalizationOrientation : ℝ :=
  orientation normalizationZeroValue normalizationOneValue normalizationPoleValue

theorem normalizationOrientation_ne_zero : normalizationOrientation ≠ 0 :=
  TriangleRiemannNormalization.normalization_orientation_ne_zero triangleClosedDiscHomeomorph
    triangleClosedCenterOne triangleClosedCenterTwo triangleClosedInfinity
    triangleClosedCenterOne_ne_centerTwo triangleClosedCenterOne_ne_infty
    triangleClosedCenterTwo_ne_infty triangleClosedDiscHomeomorph_norm_centerOne
    triangleClosedDiscHomeomorph_norm_centerTwo triangleClosedDiscHomeomorph_norm_infty

/-- The actual closed triangle, with its ideal vertex removed, normalized
to a closed half-plane in its original complex subspace topology. -/
def triangleFiniteNormalizationHomeomorph :
    TriangleClosedFinite ≃ₜ closedOrientedHalfPlane normalizationOrientation :=
  TriangleRiemannNormalization.normalizationHomeomorph triangleClosedDiscHomeomorph
    triangleClosedCenterOne triangleClosedCenterTwo triangleClosedInfinity
    triangleClosedCenterOne_ne_centerTwo triangleClosedCenterOne_ne_infty
    triangleClosedCenterTwo_ne_infty triangleClosedDiscHomeomorph_norm_centerOne
    triangleClosedDiscHomeomorph_norm_centerTwo triangleClosedDiscHomeomorph_norm_infty

@[simp] theorem triangleFiniteNormalizationHomeomorph_apply (x : TriangleClosedFinite) :
    (triangleFiniteNormalizationHomeomorph x : ℂ) =
      crossRatio normalizationZeroValue normalizationOneValue normalizationPoleValue
        (triangleClosedDiscHomeomorph (x : TriangleClosedDomain) : ℂ) :=
  TriangleRiemannNormalization.normalizationHomeomorph_apply triangleClosedDiscHomeomorph
    triangleClosedCenterOne triangleClosedCenterTwo triangleClosedInfinity
    triangleClosedCenterOne_ne_centerTwo triangleClosedCenterOne_ne_infty
    triangleClosedCenterTwo_ne_infty triangleClosedDiscHomeomorph_norm_centerOne
    triangleClosedDiscHomeomorph_norm_centerTwo triangleClosedDiscHomeomorph_norm_infty x

@[simp] theorem triangleFiniteNormalizationHomeomorph_centerOne :
    (triangleFiniteNormalizationHomeomorph
      ⟨triangleClosedCenterOne, triangleClosedCenterOne_ne_infty⟩ : ℂ) = 0 :=
  TriangleRiemannNormalization.normalizationHomeomorph_first triangleClosedDiscHomeomorph
    triangleClosedCenterOne triangleClosedCenterTwo triangleClosedInfinity
    triangleClosedCenterOne_ne_centerTwo triangleClosedCenterOne_ne_infty
    triangleClosedCenterTwo_ne_infty triangleClosedDiscHomeomorph_norm_centerOne
    triangleClosedDiscHomeomorph_norm_centerTwo triangleClosedDiscHomeomorph_norm_infty

@[simp] theorem triangleFiniteNormalizationHomeomorph_centerTwo :
    (triangleFiniteNormalizationHomeomorph
      ⟨triangleClosedCenterTwo, triangleClosedCenterTwo_ne_infty⟩ : ℂ) = 1 :=
  TriangleRiemannNormalization.normalizationHomeomorph_second triangleClosedDiscHomeomorph
    triangleClosedCenterOne triangleClosedCenterTwo triangleClosedInfinity
    triangleClosedCenterOne_ne_centerTwo triangleClosedCenterOne_ne_infty
    triangleClosedCenterTwo_ne_infty triangleClosedDiscHomeomorph_norm_centerOne
    triangleClosedDiscHomeomorph_norm_centerTwo triangleClosedDiscHomeomorph_norm_infty

theorem triangleFiniteNormalizationHomeomorph_strict_iff (x : TriangleClosedFinite) :
    0 < normalizationOrientation * (triangleFiniteNormalizationHomeomorph x : ℂ).im ↔
      (x : TriangleClosedDomain) ∈ triangleClosedInterior := by
  have h := TriangleRiemannNormalization.normalizationHomeomorph_strict_iff
    triangleClosedDiscHomeomorph triangleClosedCenterOne triangleClosedCenterTwo
    triangleClosedInfinity triangleClosedCenterOne_ne_centerTwo
    triangleClosedCenterOne_ne_infty triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty x
  exact h.trans (triangleClosedDiscHomeomorph_norm_lt_iff x)

/-- A genuine homeomorphism from the literal finite half-Ford region to
the closed half-plane; no additional source-topology identification is assumed. -/
def halfFordNormalizationHomeomorph :
    halfFordRegion ≃ₜ closedOrientedHalfPlane normalizationOrientation :=
  halfFordClosedHomeomorph.trans triangleFiniteNormalizationHomeomorph

@[simp] theorem halfFordNormalizationHomeomorph_apply (z : halfFordRegion) :
    (halfFordNormalizationHomeomorph z : ℂ) =
      crossRatio normalizationZeroValue normalizationOneValue normalizationPoleValue
        (triangleClosedDiscHomeomorph (halfFordClosedHomeomorph z).val : ℂ) :=
  triangleFiniteNormalizationHomeomorph_apply (halfFordClosedHomeomorph z)

@[simp] theorem halfFordNormalizationHomeomorph_centerOne :
    (halfFordNormalizationHomeomorph ⟨centerOne, centerOne_mem_halfFordRegion⟩ : ℂ) = 0 :=
  triangleFiniteNormalizationHomeomorph_centerOne

@[simp] theorem halfFordNormalizationHomeomorph_centerTwo :
    (halfFordNormalizationHomeomorph ⟨centerTwo, centerTwo_mem_halfFordRegion⟩ : ℂ) = 1 :=
  triangleFiniteNormalizationHomeomorph_centerTwo

/-- On the interior the normalization still uses the original analytic
Riemann map, with its already proved source coordinate. -/
theorem halfFordNormalizationHomeomorph_apply_of_interior (z : ℍ)
    (hz : z ∈ halfFordInterior) :
    (halfFordNormalizationHomeomorph ⟨z, halfFordInterior_subset_halfFordRegion hz⟩ : ℂ) =
      crossRatio normalizationZeroValue normalizationOneValue normalizationPoleValue
        (triangleMap (z : ℂ)) := by
  rw [halfFordNormalizationHomeomorph_apply, halfFordClosedHomeomorph_of_interior z hz,
    triangleClosedDiscHomeomorph_triangle]

theorem halfFordNormalizationHomeomorph_strict_iff (z : halfFordRegion) :
    0 < normalizationOrientation * (halfFordNormalizationHomeomorph z : ℂ).im ↔
      (z : ℍ) ∈ halfFordInterior :=
  (triangleFiniteNormalizationHomeomorph_strict_iff (halfFordClosedHomeomorph z)).trans
    (halfFordClosedHomeomorph_mem_interior_iff z)

/-- The real boundary is exactly the non-interior part of the actual
closed half-Ford region. -/
theorem halfFordNormalizationHomeomorph_boundary_iff (z : halfFordRegion) :
    (halfFordNormalizationHomeomorph z : ℂ).im = 0 ↔ (z : ℍ) ∉ halfFordInterior := by
  constructor
  · intro hz hin
    have h := (halfFordNormalizationHomeomorph_strict_iff z).mpr hin
    simp only [hz, mul_zero, lt_self_iff_false] at h
  · intro hz
    have hn : ¬0 < normalizationOrientation * (halfFordNormalizationHomeomorph z : ℂ).im :=
      fun h => hz ((halfFordNormalizationHomeomorph_strict_iff z).mp h)
    have he : normalizationOrientation * (halfFordNormalizationHomeomorph z : ℂ).im = 0 :=
      le_antisymm (le_of_not_gt hn) (halfFordNormalizationHomeomorph z).property
    exact (mul_eq_zero.mp he).resolve_left normalizationOrientation_ne_zero

/-- The inverse's value in the original disc coordinate is explicit too. -/
theorem halfFordNormalizationHomeomorph_symm_discCoordinate
    (w : closedOrientedHalfPlane normalizationOrientation) :
    (triangleClosedDiscHomeomorph
      (halfFordClosedHomeomorph (halfFordNormalizationHomeomorph.symm w)).val : ℂ) =
        inverseCrossRatio normalizationZeroValue normalizationOneValue
          normalizationPoleValue w := by
  change (triangleClosedDiscHomeomorph
      (halfFordClosedHomeomorph
      (halfFordClosedHomeomorph.symm
        (triangleFiniteNormalizationHomeomorph.symm w))).val : ℂ) = _
  rw [halfFordClosedHomeomorph.apply_symm_apply]
  exact TriangleRiemannNormalization.normalizationHomeomorph_symm_coordinate
    triangleClosedDiscHomeomorph triangleClosedCenterOne triangleClosedCenterTwo
    triangleClosedInfinity triangleClosedCenterOne_ne_centerTwo
    triangleClosedCenterOne_ne_infty triangleClosedCenterTwo_ne_infty
    triangleClosedDiscHomeomorph_norm_centerOne triangleClosedDiscHomeomorph_norm_centerTwo
    triangleClosedDiscHomeomorph_norm_infty w

end Wikipedia.HopfProblem.RiemannMapping
