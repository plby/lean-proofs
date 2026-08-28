import Wikipedia.HopfProblem.CuspCircleOrbitGlobalCharts

/-!
# The quotient charts cover the entire original cusp image

Every point of the original cusp quotient has an original toric-chart
representative in the unchanged coordinate domain. Consequently the
proved global quotient charts cover exactly the quotient image of the
original cusp piece, an open subset of the actual global orbit space.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
namespace Global

open ToricCharts ToricFan

local notation "E₃" => CoordinateSpace 3
local notation "CD" => CuspGeometry.data
local notation "Q" => CircleOrbitSpace.OrbitSpace

/-- Every actual cusp point has an original affine toric representative in the native tube. -/
theorem quotientMap_jointly_surjective (x : CuspGeometry.LocalSpace) :
    ∃ a : Triangle, ∃ z : Domain, quotientMap a z = x := by
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective x
  obtain ⟨a, z, hz⟩ := ToricSpace.inclusion_jointly_surjective (y : ToricSpace.Space)
  have hdomain : ‖ToricFan.Triangle.time z‖ < (CD).radius := by
    have hy : ToricSpace.time (y : ToricSpace.Space) ∈ Metric.ball 0 (CD).radius := y.property
    rw [← hz, ToricSpace.time_inclusion] at hy
    simpa only [Metric.mem_ball, dist_zero_right] using hy
  let w : Domain := ⟨z, hdomain⟩
  refine ⟨a, w, ?_⟩
  have ht : tubeMap a w = y := Subtype.ext hz
  change CuspQuotient.quotientMap (CD).correction (CD).radius (tubeMap a w) = _
  rw [ht]
  rfl

/-- The explicit invariant-coordinate maps jointly cover the original cusp quotient image. -/
theorem exists_invariantMap_of_cusp (x : CuspGeometry.LocalSpace) :
    ∃ a : Triangle, ∃ p : orbitDomain,
      invariantMap a p = CircleOrbitSpace.quotientMap (CuspGeometry.inclusion x) := by
  obtain ⟨a, z, hz⟩ := quotientMap_jointly_surjective x
  refine ⟨a, localOrbitProjection z, ?_⟩
  rw [invariantMap_projection]
  change CircleOrbitSpace.quotientMap (CuspGeometry.inclusion (quotientMap a z)) = _
  rw [hz]

/-- The image of the original cusp piece in the actual global circle orbit space. -/
def cuspOrbitImage : Set Q :=
  CircleOrbitSpace.quotientMap '' range CuspGeometry.inclusion

theorem cuspOrbitImage_isOpen : IsOpen cuspOrbitImage :=
  CircleOrbitSpace.quotientMap_isOpenQuotientMap.isOpenMap _
    CuspGeometry.inclusion_openEmbedding.isOpen_range

/-- No abstract replacement of the cusp image is made by the chart cover. -/
theorem iUnion_invariantMap_range :
    (⋃ a : Triangle, range (invariantMap a)) = cuspOrbitImage := by
  ext q
  constructor
  · intro hq
    obtain ⟨a, p, hp⟩ := mem_iUnion.mp hq
    obtain ⟨z, rfl⟩ := localOrbitProjection_surjective p
    rw [invariantMap_projection] at hp
    exact ⟨globalMap a z, ⟨quotientMap a z, rfl⟩, hp⟩
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    obtain ⟨a, p, hp⟩ := exists_invariantMap_of_cusp y
    exact mem_iUnion.mpr ⟨a, p, hp⟩

/-- Every point of the actual cusp orbit image lies in one of the genuine quotient charts. -/
theorem exists_quotientChart_at_cusp (x : CuspGeometry.LocalSpace) :
    ∃ a : Triangle, ∃ p : orbitDomain,
      CircleOrbitSpace.quotientMap (CuspGeometry.inclusion x) ∈ (quotientChart a p).source ∧
      quotientChart a p (CircleOrbitSpace.quotientMap (CuspGeometry.inclusion x)) = p := by
  obtain ⟨a, p, hp⟩ := exists_invariantMap_of_cusp x
  refine ⟨a, p, ?_, ?_⟩
  · rw [← hp]
    exact quotientChart_source_mem a p
  · rw [← hp]
    exact quotientChart_apply_invariantMap a p

end Global
end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
