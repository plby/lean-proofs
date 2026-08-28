import Wikipedia.HopfProblem.CuspCircleOrbitLocal
import Wikipedia.HopfProblem.ThreefoldCircleOrbitSpace

/-!
# The original cusp coordinate covers descend to the actual global circle quotient

The domain is the explicit local invariant-coordinate domain, and the
target is the original threefold's actual circle orbit space. The map
keeps the original coordinate cover on every representative. It is open
because that cover and the original global orbit projection are open.
No injectivity of an entire coordinate cover is assumed.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
namespace Global

open ToricFan
open Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)
local notation "Q" => CircleOrbitSpace.OrbitSpace

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace
  Threefold.space_isManifold

/-- The actual coordinate cover followed by the actual global circle projection. -/
def coverMap (a : Triangle) : C(Domain, Q) :=
  ⟨CircleOrbitSpace.quotientMap ∘ globalMap a,
    CircleOrbitSpace.quotientMap_continuous.comp
      (globalMap_isLocalDiffeomorph a).contMDiff.continuous⟩

@[simp] theorem coverMap_apply (a : Triangle) (z : Domain) :
    coverMap a z = CircleOrbitSpace.quotientMap (globalMap a z) := rfl

theorem coverMap_coordinateAction (a : Triangle) (t : Circle) (z : Domain) :
    coverMap a (coordinateAction (DeltaSweep.circleParameter t) z) = coverMap a z := by
  rw [coverMap_apply, ← globalMap_circle_coordinateAction,
    CircleOrbitSpace.quotientMap_actionMap, coverMap_apply]

/-- Descending the original cover through the original local circle relation. -/
def orbitMap (a : Triangle) : C(LocalOrbitSpace, Q) where
  toFun := Quotient.lift (coverMap a) (by
    rintro z w ⟨t, rfl⟩
    exact (coverMap_coordinateAction a t z).symm)
  continuous_toFun := continuous_quot_lift _ (coverMap a).continuous

@[simp] theorem orbitMap_class (a : Triangle) (z : Domain) :
    orbitMap a (localOrbitClass z) = coverMap a z := rfl

/-- The genuine global orbit map in the proved invariant-coordinate model. -/
def invariantMap (a : Triangle) : C(orbitDomain, Q) :=
  (orbitMap a).comp
    ⟨localOrbitSpaceHomeomorph.symm, localOrbitSpaceHomeomorph.symm.continuous⟩

/-- The map retains the original covering and orbit projection on every point. -/
@[simp] theorem invariantMap_projection (a : Triangle) (z : Domain) :
    invariantMap a (localOrbitProjection z) =
      CircleOrbitSpace.quotientMap (globalMap a z) := by
  change orbitMap a (localOrbitSpaceEquiv.symm (localOrbitProjection z)) = _
  rw [localOrbitSpaceEquiv_symm_projection, orbitMap_class, coverMap_apply]

theorem invariantMap_comp_projection (a : Triangle) :
    (invariantMap a) ∘ localOrbitProjection = coverMap a :=
  funext (invariantMap_projection a)

theorem coverMap_isOpenMap (a : Triangle) : IsOpenMap (coverMap a) :=
  CircleOrbitSpace.quotientMap_isOpenQuotientMap.isOpenMap.comp
    (globalMap_isLocalDiffeomorph a).isOpenMap

/-- Openness descends from the original coordinate covering and circle projection. -/
theorem invariantMap_isOpenMap (a : Triangle) : IsOpenMap (invariantMap a) := by
  apply IsOpenMap.of_comp localOrbitProjection_continuous localOrbitProjection_surjective
  rw [invariantMap_comp_projection]
  exact coverMap_isOpenMap a

theorem invariantMap_isOpen_range (a : Triangle) : IsOpen (range (invariantMap a)) :=
  (invariantMap_isOpenMap a).isOpen_range

/-- The image is precisely the quotient image of the original coordinate cover. -/
theorem invariantMap_range (a : Triangle) :
    range (invariantMap a) = CircleOrbitSpace.quotientMap '' range (globalMap a) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨z, rfl⟩ := localOrbitProjection_surjective p
    exact ⟨globalMap a z, ⟨z, rfl⟩, (invariantMap_projection a z).symm⟩
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨localOrbitProjection z, invariantMap_projection a z⟩

/-- The original coordinate-cover image is already saturated under the actual circle. -/
theorem quotientMap_preimage_invariantMap_range (a : Triangle) :
    CircleOrbitSpace.quotientMap ⁻¹' range (invariantMap a) = range (globalMap a) := by
  ext x
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨z, rfl⟩ := localOrbitProjection_surjective p
    rw [invariantMap_projection] at hp
    obtain ⟨t, ht⟩ := (CircleOrbitSpace.quotientMap_eq_iff x (globalMap a z)).mp hp.symm
    exact ⟨coordinateAction (DeltaSweep.circleParameter t) z,
      (globalMap_circle_coordinateAction t a z).symm.trans ht⟩
  · rintro ⟨z, rfl⟩
    exact ⟨localOrbitProjection z, invariantMap_projection a z⟩

end Global
end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
