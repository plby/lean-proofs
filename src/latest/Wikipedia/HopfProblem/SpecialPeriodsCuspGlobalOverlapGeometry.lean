import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapBase
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspChart

/-!
# The actual base of the global cusp overlap

The logarithmic parameter maps into the proved high-horodisc regular
locus.  Its image in the regular triangle quotient is exactly the
punctured part of the actual filled cusp chart, restricted to the chosen
round coordinate disc.  The precise-return statement below uses the
proved stabilizer of the genuine triangle action.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap

open CuspFamily Triangle CuspUniformization

attribute [local instance] triangleRegularQuotientChartedSpace

variable (r : ℝ) (hrcap : r ≤ cuspRadius width)

/-- The actual map from a logarithmic cusp parameter to the regular
triangle orbit quotient. -/
def baseCover : LogBase r → TriangleRegularQuotient :=
  triangleRegularProject ∘ logBaseToRegular r hrcap

theorem baseCover_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (baseCover r hrcap) := by
  intro s
  exact (logBaseToRegular_isLocalDiffeomorph r hrcap s).comp
    (K := 𝓘(ℂ)) (P := TriangleRegularQuotient)
    (triangleRegularProject_isLocalDiffeomorph (logBaseToRegular r hrcap s))

/-- The actual open base image, not an assumed coordinate patch. -/
def basePatch : TopologicalSpace.Opens TriangleRegularQuotient :=
  ⟨range (baseCover r hrcap), (baseCover_isLocalDiffeomorph r hrcap).isOpen_range⟩

@[simp] theorem baseCover_mem_basePatch (s : LogBase r) :
    baseCover r hrcap s ∈ basePatch r hrcap := mem_range_self s

/-- The actual inclusion of the regular base into the compactified
triangle orbit space. -/
def compactBase : TriangleRegularQuotient → TriangleCompactifiedOrbitSpace :=
  triangleOpenInclusion ∘ triangleRegularToOrbit

@[simp] theorem compactBase_baseCover (s : LogBase r) :
    compactBase (baseCover r hrcap s) =
      triangleOpenInclusion (triangleOrbitProjection (logBaseToRegular r hrcap s : ℍ)) := rfl

theorem compactBase_baseCover_mem_chart (s : LogBase r) :
    compactBase (baseCover r hrcap s) ∈ (cuspFullChart width le_rfl).source := by
  apply (openInclusion_mem_cuspNeighborhood width _).mpr
  exact ⟨(logBaseToRegular r hrcap s : ℍ),
    logBaseToRegular_mem_horodisc r hrcap s, rfl⟩

/-- The genuine filled cusp chart agrees with the original normalized
exponential on every logarithmic representative. -/
@[simp] theorem cuspFullChart_compactBase_baseCover (s : LogBase r) :
    cuspFullChart width le_rfl (compactBase (baseCover r hrcap s)) = exponential s := by
  rw [compactBase_baseCover]
  exact (cuspFullChart_mk width le_rfl
    ⟨(logBaseToRegular r hrcap s : ℍ), logBaseToRegular_mem_horodisc r hrcap s⟩).trans
      (logBaseToRegular_cuspQ r hrcap s)

/-- Every possible identification between these actual representatives
is an integer power of the original cusp element. -/
theorem logBaseToRegular_return (g : TriangleGroup) (s t : LogBase r)
    (he : g • logBaseToRegular r hrcap t = logBaseToRegular r hrcap s) :
    ∃ k : ℤ, triangleCuspGenerator ^ k = g := by
  apply Subgroup.mem_zpowers_iff.mp
  apply triangle_horodisc_overlap_mem_cusp width le_rfl g
  exact ⟨(logBaseToRegular r hrcap s : ℍ),
    ⟨(logBaseToRegular r hrcap t : ℍ), logBaseToRegular_mem_horodisc r hrcap t,
      congrArg Subtype.val he⟩, logBaseToRegular_mem_horodisc r hrcap s⟩

/-- Exact membership in the full base overlap, expressed in the actual
compactified quotient chart used for gluing. -/
theorem mem_basePatch_iff (q : TriangleRegularQuotient) :
    q ∈ basePatch r hrcap ↔
      compactBase q ∈ (cuspFullChart width le_rfl).source ∧
        ‖cuspFullChart width le_rfl (compactBase q)‖ < r := by
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨compactBase_baseCover_mem_chart r hrcap s, ?_⟩
    rw [cuspFullChart_compactBase_baseCover]
    exact (mem_logBase r s).mp s.property
  · rintro ⟨hsource, hnorm⟩
    have himage : triangleRegularToOrbit q ∈ cuspImage width :=
      (openInclusion_mem_cuspNeighborhood width _).mp hsource
    obtain ⟨z, hz, he⟩ := himage
    have hqz : ‖cuspQ z‖ < r := by
      have hcoord := cuspFullChart_mk width le_rfl (⟨z, hz⟩ : horodisc width)
      change cuspFullChart width le_rfl
        (triangleOpenInclusion (triangleOrbitProjection z)) = cuspQ z at hcoord
      rw [he] at hcoord
      exact hcoord ▸ hnorm
    obtain ⟨s, hs⟩ := (logBaseToUpperHalfPlane_range r hrcap ▸ hqz :
      z ∈ range (logBaseToUpperHalfPlane r hrcap))
    refine ⟨s, triangleRegularToOrbit_injective ?_⟩
    change triangleOrbitProjection (logBaseToUpperHalfPlane r hrcap s) =
      triangleRegularToOrbit q
    rw [hs]
    exact he

theorem basePatch_avoids_cusp (q : basePatch r hrcap) : compactBase q ≠ triangleCuspPoint := by
  exact OnePoint.coe_ne_infty _

end Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap
