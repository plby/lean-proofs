import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientRegularCharts
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientEllipticCharts
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientAtlasCore

/-!
# The complex curve structure on the full actual triangle quotient

The full quotient atlas consists of the regular covering charts and exactly
one power chart at each of the two elliptic orbits.  A critical point belongs
to its own power chart only.  Every transition between distinct charts
therefore has an actual analytic inverse branch upstairs, proving compatibility.

This constructs a complex analytic curve on the original Hausdorff quotient
topology and proves the original projection holomorphic.  No identification
of the quotient with `ℂ`, and no compactified uniformization, is assumed.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

open Triangle

/-- The regular covering charts, together with the two actual branch charts. -/
abbrev TriangleOrbitChartIndex := TriangleRegularQuotient ⊕ Elliptic.Kind

def triangleOrbitChart : TriangleOrbitChartIndex → OpenPartialHomeomorph TriangleOrbitSpace ℂ
  | .inl x => regularFullChart x
  | .inr j => ellipticFullChart j

theorem triangleOrbitChart_cover (x : TriangleOrbitSpace) :
    ∃ i, x ∈ (triangleOrbitChart i).source := by
  by_cases h₁ : x = triangleOrbitCenterOne
  · subst x
    exact ⟨.inr .three, ellipticFullChart_center_mem_source .three⟩
  by_cases h₂ : x = triangleOrbitCenterTwo
  · subst x
    exact ⟨.inr .four, ellipticFullChart_center_mem_source .four⟩
  obtain ⟨r, hr⟩ := exists_regularFullChart x
    ((triangleOrbitRegularDomain_mem_iff x).mpr ⟨h₁, h₂⟩)
  exact ⟨.inl r, hr⟩

/-- Each critical orbit belongs to exactly its own chosen branch chart;
in particular transitions to a different chart avoid its critical value. -/
theorem triangleOrbitChart_center_unique (j : Elliptic.Kind) (i : TriangleOrbitChartIndex)
    (hi : ellipticOrbitCenter j ∈ (triangleOrbitChart i).source) : i = .inr j := by
  cases i with
  | inl x =>
      have h := (triangleOrbitRegularDomain_mem_iff _).mp
        (regularFullChart_source_subset x hi)
      cases j
      · exact (h.1 rfl).elim
      · exact (h.2 rfl).elim
  | inr k =>
      cases j <;> cases k
      · rfl
      · exact (ellipticFullChart_other_not_mem_source .four hi).elim
      · exact (ellipticFullChart_other_not_mem_source .three hi).elim
      · rfl

/-- All topological and analytic inputs of the quotient atlas construction
are discharged for the original triangle action. -/
def triangleOrbitAtlasData :
    BranchedQuotientAtlas.Data (E := ℂ) triangleOrbitProjection TriangleOrbitChartIndex where
  chart := triangleOrbitChart
  cover := triangleOrbitChart_cover
  continuous_project := triangleOrbitProjection_continuous
  pullback_contMDiff i := by
    cases i with
    | inl x => exact regularFullChart_pullback_holomorphic x
    | inr j => exact ellipticFullChart_pullback_holomorphic j
  overlap_lift i j hij z hz := by
    obtain ⟨a, ha⟩ := triangleOrbitProjection_surjective ((triangleOrbitChart i).symm z)
    have hsource : triangleOrbitProjection a ∈ (triangleOrbitChart i).source := by
      rw [ha]
      exact (triangleOrbitChart i).map_target hz.1
    refine ⟨a, ha, ?_⟩
    cases i with
    | inl r => exact regularFullChart_pullback_isLocalDiffeomorphAt r hsource
    | inr k =>
        apply ellipticFullChart_pullback_isLocalDiffeomorphAt k hsource
        intro h
        have hcritical : ellipticOrbitCenter k ∈ (triangleOrbitChart j).source := by
          rw [← h, ha]
          exact hz.2
        exact hij (triangleOrbitChart_center_unique k j hcritical).symm

/-- The complex atlas on the full, actual triangle orbit space. -/
@[instance_reducible] def triangleOrbitChartedSpace : ChartedSpace ℂ TriangleOrbitSpace :=
  triangleOrbitAtlasData.chartedSpace

/-- The quotient is a complex curve, including both elliptic orbits. -/
theorem triangleOrbit_isManifold :
    letI := triangleOrbitChartedSpace
    IsManifold 𝓘(ℂ) ω TriangleOrbitSpace :=
  triangleOrbitAtlasData.isManifold

theorem triangleOrbitChart_mem_atlas (i : TriangleOrbitChartIndex) :
    letI := triangleOrbitChartedSpace
    triangleOrbitChart i ∈ atlas ℂ TriangleOrbitSpace :=
  triangleOrbitAtlasData.chart_mem_atlas i

/-- The actual projection from the upper half-plane is holomorphic for
the constructed full quotient atlas. -/
theorem triangleOrbitProjection_holomorphic :
    letI := triangleOrbitChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleOrbitProjection :=
  triangleOrbitAtlasData.contMDiff_project

end Wikipedia.HopfProblem.SpecialPeriods
