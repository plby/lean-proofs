import Wikipedia.HopfProblem.CuspCircleOrbitGlobalBasic
import Wikipedia.HopfProblem.CuspCircleOrbitGlobalOrbit

/-!
# The actual fixed curve in genuine quotient coordinates

An original cusp coordinate point maps to the actual fixed curve exactly
when its two normal coordinates vanish. Descending the unchanged cover
to the actual global circle quotient therefore takes the zero section of
the normal invariant coordinates precisely to the global fixed-curve
image. No normal-bundle identification is assumed.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
namespace Global

open ToricCharts ToricFan
open Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

local notation "E₃" => CoordinateSpace 3
local notation "Circle" => AddCircle (1 : ℝ)

/-- The actual fixed curve has exactly the two vanishing normal coordinates in every cover. -/
theorem globalMap_mem_D₀_iff (a : Triangle) (z : Domain) :
    globalMap a z ∈ VerticalAction.D₀ ↔ (z : E₃) 0 = 0 ∧ (z : E₃) 2 = 0 := by
  constructor
  · intro hz
    obtain ⟨t, ht⟩ := exists_circleParameter_of_norm_eq_one (-1 : ℂˣ) (by simp)
    have hact : coordinateAction (DeltaSweep.circleParameter t) z =
        coordinateAction (DeltaSweep.circleParameter (0 : Circle)) z :=
      coordinateCircleOrbit_subsingleton_of_fixed a z hz
        (Set.mem_range_self t) (Set.mem_range_self (0 : Circle))
    rw [ht, DeltaSweep.circleParameter_zero] at hact
    have h₀ : -(z : E₃) 0 = (z : E₃) 0 := by
      simpa [coordinateAction_coe, diagonal_apply] using
        congrArg (fun w : Domain => (w : E₃) 0) hact
    have h₂ : -(z : E₃) 2 = (z : E₃) 2 := by
      simpa [coordinateAction_coe, diagonal_apply] using
        congrArg (fun w : Domain => (w : E₃) 2) hact
    constructor
    · linear_combination (-(1 / 2 : ℂ)) * h₀
    · linear_combination (-(1 / 2 : ℂ)) * h₂
  · rintro ⟨h₀, h₂⟩
    apply (VerticalAction.action_fixed_iff (globalMap a z)).mp
    intro u
    change actionBiholomorph u (globalMap a z) = globalMap a z
    rw [globalMap_coordinateAction]
    apply congrArg (globalMap a)
    apply Subtype.ext
    ext j
    fin_cases j <;> simp [coordinateAction_coe, diagonal_apply, h₀, h₂]

/-- The global fixed-curve image is exactly the normal zero section in actual orbit coordinates. -/
theorem invariantMap_mem_fixedCurveRange_iff (a : Triangle) (p : orbitDomain) :
    invariantMap a p ∈ Set.range CircleOrbitSpace.fixedCurveMap ↔
      (p : ℂ × ℂ × ℝ).2 = 0 := by
  obtain ⟨z, rfl⟩ := localOrbitProjection_surjective p
  rw [invariantMap_projection]
  change globalMap a z ∈
      CircleOrbitSpace.quotientMap ⁻¹' Set.range CircleOrbitSpace.fixedCurveMap ↔
    (localOrbitMap z).2 = 0
  rw [CircleOrbitSpace.quotientMap_preimage_fixedCurveRange,
    globalMap_mem_D₀_iff, localOrbitMap_normal_zero_iff]

/-- The literal inverse image of the fixed-curve image, as a subset of the native orbit domain. -/
theorem invariantMap_preimage_fixedCurveRange (a : Triangle) :
    invariantMap a ⁻¹' Set.range CircleOrbitSpace.fixedCurveMap =
      {p : orbitDomain | (p : ℂ × ℂ × ℝ).2 = 0} := by
  ext p
  exact invariantMap_mem_fixedCurveRange_iff a p

end Global
end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
