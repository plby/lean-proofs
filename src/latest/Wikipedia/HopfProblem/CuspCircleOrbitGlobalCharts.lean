import Wikipedia.HopfProblem.CuspCircleOrbitGlobalBase
import Wikipedia.HopfProblem.CuspCircleOrbitGlobalOrbit
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCompactNeighborhood

/-!
# Genuine local charts on the actual global circle quotient

The original coordinate cover is injective on each compact local circle
orbit. Its actual local-homeomorphism property therefore gives an
injective neighborhood of that whole orbit. Properness of the original
local orbit projection shrinks this to a saturated neighborhood. On its
invariant-coordinate image the descended map is injective, hence a local
homeomorphism because it is already continuous and open.

This proves local quotient charts, including at fixed points. It does
not assert injectivity of an entire coordinate cover or classify the
globally glued orbit space.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
namespace Global

open ToricFan
open Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_t2Space

/-- A fibre of the native invariant projection is exactly the original local circle orbit. -/
theorem localOrbitProjection_fibre_eq_range (z : Domain) :
    localOrbitProjection ⁻¹' {localOrbitProjection z} =
      range (fun t : AddCircle (1 : ℝ) => coordinateAction (DeltaSweep.circleParameter t) z) := by
  ext w
  change localOrbitProjection w = localOrbitProjection z ↔
    ∃ t : AddCircle (1 : ℝ), coordinateAction (DeltaSweep.circleParameter t) z = w
  rw [eq_comm]
  exact localOrbitProjection_eq_iff_circle z w

/-- Actual injectivity near the entire compact orbit, not just near one representative. -/
theorem exists_open_globalMap_injOn_fibre (a : Triangle) (z : Domain) :
    ∃ U : Set Domain, IsOpen U ∧
      localOrbitProjection ⁻¹' {localOrbitProjection z} ⊆ U ∧ InjOn (globalMap a) U := by
  have hlocal := (globalMap_isLocalDiffeomorph a).isLocalHomeomorph
  have hcompact : IsCompact (localOrbitProjection ⁻¹' {localOrbitProjection z}) :=
    localOrbitProjection_isProperMap.isCompact_preimage isCompact_singleton
  have hinj : InjOn (globalMap a) (localOrbitProjection ⁻¹' {localOrbitProjection z}) := by
    rw [localOrbitProjection_fibre_eq_range]
    exact globalMap_injOn_coordinateCircleOrbit a z
  exact CuspCircleNormalTrivialization.exists_open_injOn_of_compact
    hlocal.continuous hlocal.isLocallyInjective hcompact hinj

/-- Properness of the actual orbit projection supplies a saturated injective neighborhood. -/
theorem exists_open_invariantMap_injOn (a : Triangle) (p : orbitDomain) :
    ∃ V : Set orbitDomain, IsOpen V ∧ p ∈ V ∧ InjOn (invariantMap a) V := by
  obtain ⟨z, rfl⟩ := localOrbitProjection_surjective p
  obtain ⟨U, hU, hKU, hinj⟩ := exists_open_globalMap_injOn_fibre a z
  let V : Set orbitDomain := (localOrbitProjection '' Uᶜ)ᶜ
  have hV : IsOpen V :=
    (localOrbitProjection_isProperMap.isClosedMap Uᶜ hU.isClosed_compl).isOpen_compl
  have hzV : localOrbitProjection z ∈ V := by
    rintro ⟨w, hw, he⟩
    exact hw (hKU he)
  have hVU : localOrbitProjection ⁻¹' V ⊆ U := by
    intro w hw
    by_contra hwU
    exact hw ⟨w, hwU, rfl⟩
  refine ⟨V, hV, hzV, ?_⟩
  intro p hp q hq he
  obtain ⟨x, rfl⟩ := localOrbitProjection_surjective p
  obtain ⟨y, rfl⟩ := localOrbitProjection_surjective q
  obtain ⟨t, ht⟩ := (invariantMap_projection_eq_iff a a x y).mp he
  have hact : localOrbitProjection (coordinateAction (DeltaSweep.circleParameter t) y) =
      localOrbitProjection y :=
    ((localOrbitProjection_eq_iff_circle y _).mpr ⟨t, rfl⟩).symm
  have hactV : coordinateAction (DeltaSweep.circleParameter t) y ∈
      localOrbitProjection ⁻¹' V := by
    change localOrbitProjection (coordinateAction (DeltaSweep.circleParameter t) y) ∈ V
    rwa [hact]
  have hxy : coordinateAction (DeltaSweep.circleParameter t) y = x :=
    hinj (hVU hactV) (hVU hp) ht
  rw [← hxy, hact]

/-- The native invariant coordinates give a local homeomorphism to the actual global quotient. -/
theorem invariantMap_isLocalHomeomorph (a : Triangle) : IsLocalHomeomorph (invariantMap a) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro p
  obtain ⟨V, hV, hpV, hinj⟩ := exists_open_invariantMap_injOn a p
  refine ⟨V, hV.mem_nhds hpV, ?_⟩
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (invariantMap a).continuous.comp continuous_subtype_val
  · intro x y h
    exact Subtype.ext (hinj x.property y.property h)
  · exact (invariantMap_isOpenMap a).comp hV.isOpenMap_subtype_val

/-- A genuine quotient chart around the image of a given invariant-coordinate point. -/
def quotientChart (a : Triangle) (p : orbitDomain) :
    OpenPartialHomeomorph CircleOrbitSpace.OrbitSpace orbitDomain :=
  (invariantMap_isLocalHomeomorph a).localInverseAt p

theorem quotientChart_source_mem (a : Triangle) (p : orbitDomain) :
    invariantMap a p ∈ (quotientChart a p).source :=
  (invariantMap_isLocalHomeomorph a).apply_self_mem_localInverseAt_source

theorem quotientChart_target_mem (a : Triangle) (p : orbitDomain) :
    p ∈ (quotientChart a p).target :=
  (invariantMap_isLocalHomeomorph a).self_mem_localInverseAt_target

/-- The inverse chart function is exactly the original descended coordinate cover. -/
theorem quotientChart_symm_apply (a : Triangle) (p v : orbitDomain) :
    (quotientChart a p).symm v = invariantMap a v :=
  congrFun ((invariantMap_isLocalHomeomorph a).localInverseAt_symm p) v

theorem quotientChart_apply_invariantMap (a : Triangle) (p : orbitDomain) :
    quotientChart a p (invariantMap a p) = p :=
  (invariantMap_isLocalHomeomorph a).localInverseAt_apply_self

end Global
end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
