import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapFamily
import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyComparison

/-!
# The genuine cusp-to-regular-family overlap

This is the actual whole-family biholomorphism used to glue the cusp
filling to the regular triangle family.  It combines the proved toric
exponential comparison, the genuine integer family quotient, and the
precisely invariant cusp subgroup in the actual triangle action.  Both
the full base map and its original exponential formula are preserved.

The period agreement in this interface is a formula between actual
period functions, not a supplied overlap map.  The construction leaf
discharges it for the periods constructed from the normalized sphere
coordinate, and the existence leaf supplies that coordinate outright.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap

open CuspFamily Triangle CuspUniformization ToricCharts

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)

variable (C : CuspFamily.Data)
    (D : TrianglePeriodFamily.Data ℂ TriangleRegularPoint)
    (hrcap : C.radius ≤ cuspRadius width)
    (hperiod : ∀ s : LogBase C.radius,
      D.periods.point (logBaseToRegular C.radius hrcap s) = C.periods.point s)

/-- The actual projection from the regular family to the full compact
triangle base, retaining the already constructed regular family. -/
def compactProjection : D.Space → TriangleCompactifiedOrbitSpace :=
  compactBase ∘ D.projection

/-- The actual punctured cusp is biholomorphic to the entire regular
family over the small cusp coordinate disc. -/
def puncturedBiholomorph :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    Diffeomorph I₃ IF (PuncturedQuotient C.correction C.radius) (familyPatch C D hrcap) ω := by
  letI := C.chartedSpace
  letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  letI := D.chartedSpace (familyCovering D)
  exact C.puncturedFamilyBiholomorph.symm.trans (familyBiholomorph C D hrcap hperiod)

/-- The map agrees with the actual toric exponential and regular orbit
projection on every original logarithmic covering point. -/
theorem puncturedBiholomorph_cover (x : LogCover C.radius) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    (puncturedBiholomorph C D hrcap hperiod (puncturedCuspCover C.correction C.radius x) :
      D.Space) = familyMap C D hrcap (C.iteratedCover x) := by
  let := C.chartedSpace
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  change familyMap C D hrcap
    (C.puncturedFamilyBiholomorph.symm (puncturedCuspCover C.correction C.radius x)) = _
  rw [← C.puncturedFamilyBiholomorph_iteratedCover, Diffeomorph.symm_apply_apply]

theorem familyMap_compactProjection_mem_chart (x : C.Space) :
    compactProjection D (familyMap C D hrcap x) ∈ (cuspFullChart width le_rfl).source := by
  obtain ⟨a, rfl⟩ := C.quotient_surjective x
  exact compactBase_baseCover_mem_chart C.radius hrcap a.1

/-- The full compact-base coordinate of the cyclic comparison is
exactly the original exponential parameter, not just a germ. -/
theorem familyMap_compactProjection_coordinate (x : C.Space) :
    cuspFullChart width le_rfl (compactProjection D (familyMap C D hrcap x)) =
      (C.projection x : ℂ) := by
  obtain ⟨a, rfl⟩ := C.quotient_surjective x
  exact cuspFullChart_compactBase_baseCover C.radius hrcap a.1

/-- The cusp overlap preserves the entire actual base map in the
unchanged cusp coordinate. -/
theorem puncturedBiholomorph_coordinate (x : PuncturedQuotient C.correction C.radius) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    cuspFullChart width le_rfl
      (compactProjection D (puncturedBiholomorph C D hrcap hperiod x)) =
        CuspQuotient.projection C.correction C.radius x := by
  let := C.chartedSpace
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  obtain ⟨y, rfl⟩ := C.puncturedFamilyBiholomorph.surjective x
  change cuspFullChart width le_rfl (compactProjection D (familyMap C D hrcap
    (C.puncturedFamilyBiholomorph.symm (C.puncturedFamilyBiholomorph y)))) = _
  rw [Diffeomorph.symm_apply_apply, familyMap_compactProjection_coordinate]
  exact (C.puncturedFamilyBiholomorph_preserves_base y).symm

theorem puncturedBiholomorph_base_mem_chart (x : PuncturedQuotient C.correction C.radius) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    compactProjection D (puncturedBiholomorph C D hrcap hperiod x) ∈
      (cuspFullChart width le_rfl).source := by
  let := C.chartedSpace
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  exact familyMap_compactProjection_mem_chart C D hrcap (C.puncturedFamilyBiholomorph.symm x)

/-- Equality of the actual maps to the compact base, using the genuine
inverse cusp chart on its full punctured coordinate disc. -/
theorem puncturedBiholomorph_preserves_base (x : PuncturedQuotient C.correction C.radius) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    compactProjection D (puncturedBiholomorph C D hrcap hperiod x) =
      (cuspFullChart width le_rfl).symm (CuspQuotient.projection C.correction C.radius x) := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [← puncturedBiholomorph_coordinate C D hrcap hperiod x]
  exact ((cuspFullChart width le_rfl).left_inv
    (puncturedBiholomorph_base_mem_chart C D hrcap hperiod x)).symm

/-- The inverse overlap has the same exact coordinate formula. -/
theorem puncturedBiholomorph_symm_preserves_base (y : familyPatch C D hrcap) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    CuspQuotient.projection C.correction C.radius
      ((puncturedBiholomorph C D hrcap hperiod).symm y) =
        cuspFullChart width le_rfl (compactProjection D y) := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  have h := puncturedBiholomorph_coordinate C D hrcap hperiod
    ((puncturedBiholomorph C D hrcap hperiod).symm y)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm

end Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap
