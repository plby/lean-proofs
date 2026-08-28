import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingSmallOverlap
import Wikipedia.HopfProblem.SpecialPeriodsExistence
import Wikipedia.HopfProblem.EllipticEquivariantLocalModel

/-!
# Elliptic fillings for the genuine global special period map

The globally constructed admissible periods instantiate both main
elliptic fillings.  Their disc periods are the actual restrictions in
the normalized Cayley charts, and their full punctured parts are
biholomorphic over the actual compact base to the regular triangle
period family.  No period map, generator law, local comparison,
uniformization, or resulting threefold is an input to this specialization.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.LogGauge TrianglePeriodFamily

local notation "IF" => modelWithCornersSelf ℂ FamilyModel
local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The two actual equivariant disc period maps, derived from the
unconditional global special periods. -/
def specialLocalData (j : Kind) : Equivariant.Data j :=
  localData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂ j

@[simp] theorem specialLocalData_point (j : Kind) (z : Disc) :
    (specialLocalData j).periods.point z =
      specialPeriodMap.point (neighborhoodLift j z) := rfl

@[simp] theorem specialLocalData_center (j : Kind) :
    (specialLocalData j).centralPeriod.val =
      specialPeriodMap.point (Triangle.ellipticCenter j) :=
  localData_centralPeriod_val specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ j

/-- The whole affine filling, with the source's specified main twist. -/
abbrev SpecialFullFilling (j : Kind) :=
  fillingSpace specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂ j

@[instance_reducible] def specialFullFillingChartedSpace (j : Kind) :
    ChartedSpace FamilyModel (SpecialFullFilling j) :=
  fillingChartedSpace specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ j

def specialFullFillingProjection (j : Kind) : SpecialFullFilling j → Disc :=
  fillingProjection specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ j

/-- Both actual full fillings are proper surjective holomorphic complex
threefolds over the normalized unit disc. -/
theorem specialFullFilling_construction (j : Kind) :
    letI := specialFullFillingChartedSpace j
    T2Space (SpecialFullFilling j) ∧ SecondCountableTopology (SpecialFullFilling j) ∧
      IsManifold IF ω (SpecialFullFilling j) ∧
      IsProperMap (specialFullFillingProjection j) ∧
      Function.Surjective (specialFullFillingProjection j) ∧
      ContMDiff IF I₁ ω (specialFullFillingProjection j) := by
  let := specialFullFillingChartedSpace j
  exact ⟨inferInstance, inferInstance,
    filling_isManifold specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂ j,
    fillingProjection_proper specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ j,
    fillingProjection_surjective specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ j,
    fillingProjection_holomorphic specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ j⟩

/-- The actual open complement of the central fibre. -/
abbrev SpecialFullFillingStar (j : Kind) :=
  MainFillingStar specialPeriodMap j specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The full overlap with the genuine regular special-period family. -/
def specialFullFillingPuncturedBiholomorph (j : Kind) :
    letI := specialFullFillingChartedSpace j
    letI := (regularData specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂).chartedSpace
        (regularCovering specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂)
    Diffeomorph IF IF (SpecialFullFillingStar j)
      (regularOverlap specialPeriodMap j specialPeriodMap_generator₁ specialPeriodMap_generator₂)
      ω :=
  puncturedFillingBiholomorph specialPeriodMap j specialPeriodMap_generator₁
    specialPeriodMap_generator₂

/-- Exact base preservation, using the original compactified quotient
chart and not a separately supplied coordinate identification. -/
theorem specialFullFillingPuncturedBiholomorph_base (j : Kind)
    (x : SpecialFullFillingStar j) :
    regularCompactProjection specialPeriodMap specialPeriodMap_generator₁
        specialPeriodMap_generator₂ (specialFullFillingPuncturedBiholomorph j x).val =
      (Triangle.ellipticCompactifiedChart j).symm
        (specialFullFillingProjection j x.val : ℂ) :=
  puncturedFillingBiholomorph_base specialPeriodMap j specialPeriodMap_generator₁
    specialPeriodMap_generator₂ x

/-- The actual full projection is precisely the third or fourth power
of the transverse coordinate in its selected quotient atlas. -/
theorem specialFullFilling_projection_chart (j : Kind)
    (y : SpecialFullFilling j) (u : FamilyModel) :
    letI := specialFullFillingChartedSpace j
    u ∈ (chartAt FamilyModel y).target →
      (specialFullFillingProjection j ((chartAt FamilyModel y).symm u) : ℂ) =
        u.1 ^ j.order :=
  (specialLocalData j).projection_chart_symm j.twist (mainTwist_admissible j) y u

/-- The actual reduced central support is a smooth coordinate
hyperplane in each selected complex quotient chart. -/
theorem specialFullFilling_central_chart (j : Kind) (y x : SpecialFullFilling j) :
    letI := specialFullFillingChartedSpace j
    x ∈ (chartAt FamilyModel y).source →
      (specialFullFillingProjection j x = Elliptic.discZero ↔
        (chartAt FamilyModel y x).1 = 0) :=
  (specialLocalData j).central_chart_iff j.twist (mainTwist_admissible j) y x

def specialTransverseProjection (j : Kind) (y : SpecialFullFilling j) : ℂ → ℂ :=
  (specialLocalData j).transverseProjection j.twist (mainTwist_admissible j) y

/-- The multiplicity of the actual central fibre is exactly three or
four, measured as the analytic order of its actual transverse map. -/
theorem specialFullFilling_central_order (j : Kind) (y : SpecialFullFilling j)
    (hy : specialFullFillingProjection j y = Elliptic.discZero) :
    analyticOrderAt (specialTransverseProjection j y) 0 = (j.order : ℕ∞) :=
  (specialLocalData j).central_transverse_order j.twist (mainTwist_admissible j) y hy

theorem specialFullFilling_noncentral_order (j : Kind) (y : SpecialFullFilling j)
    (hy : specialFullFillingProjection j y ≠ Elliptic.discZero) :
    letI := specialFullFillingChartedSpace j
    analyticOrderAt (fun z : ℂ => specialTransverseProjection j y z -
      (specialFullFillingProjection j y : ℂ)) (chartAt FamilyModel y y).1 = 1 :=
  (specialLocalData j).noncentral_transverse_order j.twist (mainTwist_admissible j) y hy

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
