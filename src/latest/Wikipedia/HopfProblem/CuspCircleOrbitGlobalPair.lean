import Wikipedia.HopfProblem.CuspCircleOrbitGlobalCover
import Wikipedia.HopfProblem.CuspCircleOrbitGlobalFixed

/-!
# The actual fixed pair and base map in the global quotient charts

On every original cusp quotient chart the globally embedded fixed curve
is exactly the zero section of the normal invariant coordinates. The
original sphere-valued base projection still has cusp coordinate `aβ/2`.
These are statements about the actual global orbit space and fixed curve,
not about a separately chosen model pair.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
namespace Global

open ToricFan

local notation "Q" => CircleOrbitSpace.OrbitSpace
local notation "Target" => ℂ × ℂ × ℝ

/-- The original descended cover is the actual inverse of the chosen local quotient chart. -/
theorem invariantMap_quotientChart (a : Triangle) (p : orbitDomain) (q : Q)
    (hq : q ∈ (quotientChart a p).source) :
    invariantMap a (quotientChart a p q) = q :=
  (invariantMap_isLocalHomeomorph a).apply_localInverseAt_of_mem hq

/-- In the genuine global chart, the actual fixed curve is exactly the normal zero section. -/
theorem quotientChart_mem_fixed_iff (a : Triangle) (p : orbitDomain) (q : Q)
    (hq : q ∈ (quotientChart a p).source) :
    q ∈ range CircleOrbitSpace.fixedCurveMap ↔
      (quotientChart a p q : Target).2 = 0 := by
  have he := invariantMap_quotientChart a p q hq
  calc
    _ ↔ invariantMap a (quotientChart a p q) ∈ range CircleOrbitSpace.fixedCurveMap := by rw [he]
    _ ↔ _ := invariantMap_mem_fixedCurveRange_iff a (quotientChart a p q)

theorem quotientChart_symm_mem_fixed_iff (a : Triangle) (p v : orbitDomain) :
    (quotientChart a p).symm v ∈ range CircleOrbitSpace.fixedCurveMap ↔
      (v : Target).2 = 0 := by
  rw [quotientChart_symm_apply]
  exact invariantMap_mem_fixedCurveRange_iff a v

/-- Equality of the actual fixed subset with the chart's normal zero section on its source. -/
theorem quotientChart_fixed_source (a : Triangle) (p : orbitDomain) :
    (quotientChart a p).source ∩ range CircleOrbitSpace.fixedCurveMap =
      (quotientChart a p).source ∩
        (quotientChart a p) ⁻¹' {v : orbitDomain | (v : Target).2 = 0} := by
  ext q
  constructor
  · rintro ⟨hq, hfixed⟩
    exact ⟨hq, (quotientChart_mem_fixed_iff a p q hq).mp hfixed⟩
  · rintro ⟨hq, hzero⟩
    exact ⟨hq, (quotientChart_mem_fixed_iff a p q hq).mpr hzero⟩

/-- The original global base map retains the original monomial time in every quotient chart. -/
theorem quotientChart_sphereChart_base (a : Triangle) (p : orbitDomain) (q : Q)
    (hq : q ∈ (quotientChart a p).source) :
    CuspGeometry.sphereChart (CircleOrbitSpace.baseProjection q) =
      orbitTime (quotientChart a p q : Target) := by
  have he := invariantMap_quotientChart a p q hq
  calc
    _ = CuspGeometry.sphereChart
      (CircleOrbitSpace.baseProjection (invariantMap a (quotientChart a p q))) := by rw [he]
    _ = _ := sphereChart_baseProjection_invariantMap a (quotientChart a p q)

end Global
end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
