import Wikipedia.HopfProblem.CuspCircleOrbitLocalCoordinates
import Wikipedia.HopfProblem.CuspCircleOrbitLocalProper
import Wikipedia.HopfProblem.CuspCircleOrbitLocalSurjective
import Mathlib.Topology.LocalAtTarget

/-!
# The exact invariant-coordinate domain of the original cusp chart

The original condition `‖z₀z₁z₂‖ < radius` becomes exactly
`‖aβ/2‖ < radius` in the invariant coordinates. The map from the original
domain to this open set is proper, surjective, and a quotient map. No
quotient by the additional cusp deck transformations is taken here.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

open ToricCharts

local notation "E₃" => CoordinateSpace 3
local notation "Target" => ℂ × ℂ × ℝ
local notation "CD" => CuspGeometry.data

/-- Reorder the original coordinates without altering any coordinate value. -/
def coordinateSplitHomeomorph : E₃ ≃ₜ ℂ × ℂ × ℂ where
  toFun z := (z 1, z 0, z 2)
  invFun p := ![p.2.1, p.1, p.2.2]
  left_inv z := by
    ext i
    fin_cases i <;> rfl
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The invariant map before restricting to the native cusp tube. -/
def rawOrbitMap : E₃ → Target :=
  (Prod.map id hopfMap) ∘ coordinateSplitHomeomorph

@[simp] theorem rawOrbitMap_apply (z : E₃) :
    rawOrbitMap z = (z 1, 2 * z 0 * z 2, Complex.normSq (z 0) - Complex.normSq (z 2)) := rfl

theorem rawOrbitMap_isProperMap : IsProperMap rawOrbitMap :=
  (isProperMap_id.prodMap hopfMap_isProperMap).comp coordinateSplitHomeomorph.isProperMap

theorem rawOrbitMap_surjective : Function.Surjective rawOrbitMap := by
  rintro ⟨a, p⟩
  obtain ⟨z, hz⟩ := hopfMap_surjective p
  refine ⟨![z.1, a, z.2], ?_⟩
  change (a, hopfMap z) = (a, p)
  rw [hz]

/-- The original normal-crossing time, expressed in invariant coordinates. -/
def orbitTime (p : Target) : ℂ := p.1 * p.2.1 / 2

theorem orbitTime_continuous : Continuous orbitTime := by
  unfold orbitTime
  fun_prop

theorem orbitTime_rawOrbitMap (z : E₃) :
    orbitTime (rawOrbitMap z) = ToricFan.Triangle.time z := by
  simp only [orbitTime, rawOrbitMap_apply, ToricFan.Triangle.time]
  ring

theorem orbitTime_localOrbitMap (z : Domain) :
    orbitTime (localOrbitMap z) = ToricFan.Triangle.time (z : E₃) :=
  orbitTime_rawOrbitMap z

/-- The exact open target for the original cusp coordinate domain. -/
def orbitDomain : Set Target := {p | ‖orbitTime p‖ < (CD).radius}

theorem orbitDomain_isOpen : IsOpen orbitDomain :=
  isOpen_lt orbitTime_continuous.norm continuous_const

/-- The native coordinate domain is precisely the preimage of the invariant domain. -/
def nativePreimageHomeomorph : Domain ≃ₜ rawOrbitMap ⁻¹' orbitDomain where
  toFun z := ⟨(z : E₃), by
    change ‖orbitTime (rawOrbitMap (z : E₃))‖ < (CD).radius
    rw [orbitTime_rawOrbitMap]
    exact z.property⟩
  invFun z := ⟨(z : E₃), by
    change ‖ToricFan.Triangle.time (z : E₃)‖ < (CD).radius
    have hz : ‖orbitTime (rawOrbitMap (z : E₃))‖ < (CD).radius := z.property
    rwa [orbitTime_rawOrbitMap] at hz⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The original invariant map with its exact, unchanged tube-radius condition. -/
def localOrbitProjection (z : Domain) : orbitDomain :=
  ⟨localOrbitMap z, by
    change ‖orbitTime (localOrbitMap z)‖ < (CD).radius
    rw [orbitTime_localOrbitMap]
    exact z.property⟩

@[simp] theorem localOrbitProjection_val (z : Domain) :
    (localOrbitProjection z : Target) = localOrbitMap z := rfl

theorem localOrbitProjection_eq_restrict :
    localOrbitProjection =
      orbitDomain.restrictPreimage rawOrbitMap ∘ nativePreimageHomeomorph := rfl

theorem localOrbitProjection_isProperMap : IsProperMap localOrbitProjection := by
  rw [localOrbitProjection_eq_restrict]
  exact (rawOrbitMap_isProperMap.restrictPreimage orbitDomain).comp
    nativePreimageHomeomorph.isProperMap

theorem localOrbitProjection_continuous : Continuous localOrbitProjection :=
  localOrbitProjection_isProperMap.continuous

theorem localOrbitProjection_surjective : Function.Surjective localOrbitProjection := by
  rw [localOrbitProjection_eq_restrict]
  exact (rawOrbitMap_surjective.restrictPreimage orbitDomain).comp
    nativePreimageHomeomorph.surjective

theorem localOrbitProjection_isQuotientMap : IsQuotientMap localOrbitProjection :=
  localOrbitProjection_isProperMap.isClosedMap.isQuotientMap
    localOrbitProjection_continuous localOrbitProjection_surjective

/-- The quotient fibres retain the original additive-circle action on the native domain. -/
theorem localOrbitProjection_eq_iff_circle (z w : Domain) :
    localOrbitProjection z = localOrbitProjection w ↔
      ∃ t : AddCircle (1 : ℝ),
        coordinateAction (Homology.DeltaSweep.circleParameter t) z = w := by
  rw [Subtype.ext_iff]
  exact localOrbitMap_eq_iff_circle z w

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
