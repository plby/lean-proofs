import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapQuotient
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapGeometry
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapMonodromy
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapPeriodPullback

/-!
# The actual cyclic family is the full regular family near the cusp

The period equality on the normalized logarithmic base makes the literal
real-coordinate inclusion locally biholomorphic for the independently
constructed period-family atlases.  The proved cusp monodromy and precise
horodisc returns then identify its actual cyclic quotient with every
regular-family fibre over the genuine small cusp chart.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap

open CuspFamily Triangle

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

variable (C : CuspFamily.Data)
    (D : TrianglePeriodFamily.Data ℂ TriangleRegularPoint)
    (hrcap : C.radius ≤ cuspRadius width)

/-- The actual base covering of every period family over the regular
triangle locus; its proof is independent of the chosen periods. -/
theorem familyCovering : IsQuotientCoveringMap D.baseQuotient TriangleGroup :=
  triangleRegularProject_covering

/-- The actual map from the integer family quotient into the full
regular triangle family quotient. -/
def familyMap : C.Space → D.Space :=
  QuotientComparison.descend C D (logBaseToRegular C.radius hrcap)
    (logBaseToRegular_translate C.radius hrcap) triangleTorusHomeomorph_cusp_zpow

@[simp] theorem familyMap_quotient (x : C.TotalSpace) :
    familyMap C D hrcap (C.quotient x) =
      D.quotient (logBaseToRegular C.radius hrcap x.1, x.2) := rfl

@[simp] theorem projection_familyMap_quotient (x : C.TotalSpace) :
    D.projection (familyMap C D hrcap (C.quotient x)) =
      baseCover C.radius hrcap x.1 := rfl

theorem familyMap_injective : Injective (familyMap C D hrcap) :=
  QuotientComparison.descend_injective C D (logBaseToRegular C.radius hrcap)
    (logBaseToRegular_translate C.radius hrcap) triangleTorusHomeomorph_cusp_zpow
    (logBaseToRegular_injective C.radius hrcap) (logBaseToRegular_return C.radius hrcap)

/-- The full inverse image of the genuine cusp base patch, including
all its torus fibres. -/
def familyPatch : TopologicalSpace.Opens D.Space :=
  ⟨D.projection ⁻¹' (basePatch C.radius hrcap : Set TriangleRegularQuotient),
    (basePatch C.radius hrcap).isOpen.preimage D.projection_continuous⟩

theorem familyMap_range : range (familyMap C D hrcap) = (familyPatch C D hrcap : Set D.Space) :=
  QuotientComparison.range_descend C D (logBaseToRegular C.radius hrcap)
    (logBaseToRegular_translate C.radius hrcap) triangleTorusHomeomorph_cusp_zpow

theorem familyMap_mem_patch (x : C.Space) : familyMap C D hrcap x ∈ familyPatch C D hrcap := by
  change familyMap C D hrcap x ∈ (familyPatch C D hrcap : Set D.Space)
  rw [← familyMap_range]
  exact mem_range_self x

/-- Codomain restriction to its proved full-fibre image. -/
def familyMapInto (x : C.Space) : familyPatch C D hrcap :=
  ⟨familyMap C D hrcap x, familyMap_mem_patch C D hrcap x⟩

@[simp] theorem familyMapInto_val (x : C.Space) :
    (familyMapInto C D hrcap x : D.Space) = familyMap C D hrcap x := rfl

theorem familyMapInto_bijective : Bijective (familyMapInto C D hrcap) := by
  constructor
  · intro x y h
    exact familyMap_injective C D hrcap (congrArg Subtype.val h)
  · intro y
    have hy : y.val ∈ range (familyMap C D hrcap) := by
      rw [familyMap_range]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

variable (hperiod : ∀ s : LogBase C.radius,
  D.periods.point (logBaseToRegular C.radius hrcap s) = C.periods.point s)

include hperiod

/-- The cyclic-to-triangle map is locally biholomorphic for the actual
covering-quotient atlases, by descent of the vector-cover square. -/
theorem familyMap_isLocalDiffeomorph :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    IsLocalDiffeomorph IF IF ω (familyMap C D hrcap) := by
  let := C.periods.totalChartedSpace
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := C.chartedSpace
  let := D.chartedSpace (familyCovering D)
  have hmap := HolomorphicPeriodMap.periodPullbackMap_isLocalDiffeomorph
    C.periods D.periods (logBaseToRegular C.radius hrcap) hperiod
    (logBaseToRegular_isLocalDiffeomorph C.radius hrcap)
  have hq : IsLocalDiffeomorph IF IF ω D.quotient := by
    let := D.totalAction
    exact CoveringQuotient.project_isLocalDiffeomorph (D.quotientCoveringMap (familyCovering D))
      D.totalAction_holomorphic
  apply isLocalDiffeomorph_of_comp_surjective IF IF IF
    C.quotient_isLocalDiffeomorph C.quotient_surjective
  intro x
  exact (hmap x).comp (K := IF) (P := D.Space)
    (hq (logBaseToRegular C.radius hrcap x.1, x.2))

theorem familyMap_holomorphic :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    ContMDiff IF IF ω (familyMap C D hrcap) := by
  let := C.chartedSpace
  let := D.chartedSpace (familyCovering D)
  exact (familyMap_isLocalDiffeomorph C D hrcap hperiod).contMDiff

theorem familyMapInto_isLocalDiffeomorph :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    IsLocalDiffeomorph IF IF ω (familyMapInto C D hrcap) := by
  let := C.chartedSpace
  let := D.chartedSpace (familyCovering D)
  exact isLocalDiffeomorph_codRestrictOpens IF IF
    (familyMap_isLocalDiffeomorph C D hrcap hperiod) (familyPatch C D hrcap)
    (familyMap_mem_patch C D hrcap)

/-- The actual integer-monodromy quotient is biholomorphic to the full
regular triangle family restricted over the genuine small cusp patch. -/
def familyBiholomorph :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    Diffeomorph IF IF C.Space (familyPatch C D hrcap) ω := by
  letI := C.chartedSpace
  letI := D.chartedSpace (familyCovering D)
  exact (familyMapInto_isLocalDiffeomorph C D hrcap hperiod).diffeomorphOfBijective
    (familyMapInto_bijective C D hrcap)

@[simp] theorem familyBiholomorph_val (x : C.Space) :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    (familyBiholomorph C D hrcap hperiod x : D.Space) = familyMap C D hrcap x := rfl

@[simp] theorem familyBiholomorph_quotient (x : C.TotalSpace) :
    letI := C.chartedSpace
    letI := D.chartedSpace (familyCovering D)
    (familyBiholomorph C D hrcap hperiod (C.quotient x) : D.Space) =
      D.quotient (logBaseToRegular C.radius hrcap x.1, x.2) := rfl

end Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap
