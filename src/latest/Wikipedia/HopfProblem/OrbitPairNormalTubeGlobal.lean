import Wikipedia.HopfProblem.OrbitPairNormalTubeProjection
import Wikipedia.HopfProblem.ThreefoldCircleOrbitSpace

/-!
# A radial product neighborhood in the actual global orbit space

The target is the literal orbit quotient of the original threefold.
The normal product map descends to an open embedding, and its image is
exactly the quotient image of the existing fixed-curve neighborhood.
The fixed curve is exactly the zero section in these coordinates.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold CuspCircleNormalTrivialization

attribute [local instance] Threefold.chartedSpace

local notation "Q" => CircleOrbitSpace.OrbitSpace

/-- A representative used only to define descent; the descended map is independent of it. -/
def normalTubeLift (y : normalOrbitTube) : roundNormalProduct :=
  (normalTubeProjection_surjective y).choose

@[simp] theorem normalTubeProjection_lift (y : normalOrbitTube) :
    normalTubeProjection (normalTubeLift y) = y :=
  (normalTubeProjection_surjective y).choose_spec

theorem quotient_roundProductMap_eq_of_projection_eq {p q : roundNormalProduct}
    (h : normalTubeProjection p = normalTubeProjection q) :
    CircleOrbitSpace.quotientMap (roundProductMap p) =
      CircleOrbitSpace.quotientMap (roundProductMap q) := by
  obtain ⟨t, rfl⟩ := (normalTubeProjection_eq_iff p q).mp h
  rw [← roundProductMap_circleAction, CircleOrbitSpace.quotientMap_actionMap]

/-- The actual normal map descended to its radial orbit coordinates. -/
def normalOrbitTubeMap (y : normalOrbitTube) : Q :=
  CircleOrbitSpace.quotientMap (roundProductMap (normalTubeLift y))

/-- Descent retains the original normal-neighborhood map on every representative. -/
@[simp] theorem normalOrbitTubeMap_projection (p : roundNormalProduct) :
    normalOrbitTubeMap (normalTubeProjection p) =
      CircleOrbitSpace.quotientMap (roundProductMap p) :=
  quotient_roundProductMap_eq_of_projection_eq
    (normalTubeProjection_lift (normalTubeProjection p))

theorem normalOrbitTubeMap_comp_projection :
    normalOrbitTubeMap ∘ normalTubeProjection =
      CircleOrbitSpace.quotientMap ∘ roundProductMap :=
  funext normalOrbitTubeMap_projection

theorem normalOrbitTubeMap_continuous : Continuous normalOrbitTubeMap := by
  apply normalTubeProjection_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
  rw [normalOrbitTubeMap_comp_projection]
  exact CircleOrbitSpace.quotientMap_continuous.comp roundProductMap_contMDiff.continuous

theorem normalOrbitTubeMap_injective : Function.Injective normalOrbitTubeMap := by
  intro y z h
  obtain ⟨p, rfl⟩ := normalTubeProjection_surjective y
  obtain ⟨q, rfl⟩ := normalTubeProjection_surjective z
  rw [normalOrbitTubeMap_projection, normalOrbitTubeMap_projection] at h
  obtain ⟨t, ht⟩ := (CircleOrbitSpace.quotientMap_eq_iff _ _).mp h
  have hp : roundCircleAction t q = p :=
    roundProductMap_injective ((roundProductMap_circleAction t q).symm.trans ht)
  exact ((normalTubeProjection_eq_iff q p).mpr ⟨t, hp⟩).symm

theorem normalOrbitTubeMap_isOpenMap : IsOpenMap normalOrbitTubeMap := by
  apply IsOpenMap.of_comp normalTubeProjection_continuous normalTubeProjection_surjective
  rw [normalOrbitTubeMap_comp_projection]
  exact CircleOrbitSpace.quotientMap_isOpenQuotientMap.isOpenMap.comp
    roundProductMap_isOpenMap

theorem normalOrbitTubeMap_isOpenEmbedding : IsOpenEmbedding normalOrbitTubeMap :=
  .of_continuous_injective_isOpenMap normalOrbitTubeMap_continuous
    normalOrbitTubeMap_injective normalOrbitTubeMap_isOpenMap

/-- The actual open image in the global orbit quotient. -/
def normalOrbitImage : TopologicalSpace.Opens Q :=
  ⟨range normalOrbitTubeMap, normalOrbitTubeMap_isOpenMap.isOpen_range⟩

/-- An explicit radial product homeomorphism onto the actual orbit neighborhood. -/
def normalOrbitTubeHomeomorph : normalOrbitTube ≃ₜ normalOrbitImage :=
  normalOrbitTubeMap_isOpenEmbedding.isEmbedding.toHomeomorph

@[simp] theorem normalOrbitTubeHomeomorph_coe (y : normalOrbitTube) :
    (normalOrbitTubeHomeomorph y : Q) = normalOrbitTubeMap y := rfl

theorem normalOrbitImage_eq :
    (normalOrbitImage : Set Q) =
      CircleOrbitSpace.quotientMap '' (fixedCurveNeighborhood : Set Threefold.Space) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨p, rfl⟩ := normalTubeProjection_surjective z
    exact ⟨roundProductMap p, ⟨p, rfl⟩, (normalOrbitTubeMap_projection p).symm⟩
  · rintro ⟨x, ⟨p, rfl⟩, rfl⟩
    exact ⟨normalTubeProjection p, normalOrbitTubeMap_projection p⟩

/-- No other global orbit enters the chosen invariant normal neighborhood. -/
theorem quotientMap_preimage_normalOrbitImage :
    CircleOrbitSpace.quotientMap ⁻¹' (normalOrbitImage : Set Q) =
      (fixedCurveNeighborhood : Set Threefold.Space) := by
  rw [normalOrbitImage_eq]
  ext x
  constructor
  · rintro ⟨y, hy, hq⟩
    obtain ⟨t, ht⟩ := (CircleOrbitSpace.quotientMap_eq_iff x y).mp hq.symm
    rw [← ht]
    exact actionMap_mem_fixedCurveNeighborhood t hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The entire fixed sphere lies in this single product neighborhood. -/
theorem fixedCurveRange_subset_normalOrbitImage :
    range CircleOrbitSpace.fixedCurveMap ⊆ (normalOrbitImage : Set Q) := by
  rw [normalOrbitImage_eq]
  rintro _ ⟨x, rfl⟩
  exact ⟨x, doubleCurve_subset_fixedCurveNeighborhood x.property, rfl⟩

/-- The actual embedded fixed curve is the literal zero section of the radial coordinates. -/
theorem normalOrbitTubeMap_mem_fixed_iff (y : normalOrbitTube) :
    normalOrbitTubeMap y ∈ range CircleOrbitSpace.fixedCurveMap ↔ y.val.2 = 0 := by
  obtain ⟨p, rfl⟩ := normalTubeProjection_surjective y
  rw [normalOrbitTubeMap_projection, normalTubeProjection_normal_zero_iff]
  change roundProductMap p ∈
    CircleOrbitSpace.quotientMap ⁻¹' range CircleOrbitSpace.fixedCurveMap ↔ p.val.2 = 0
  rw [CircleOrbitSpace.quotientMap_preimage_fixedCurveRange, VerticalAction.D₀_eq_doubleCurve]
  exact roundProductMap_mem_doubleCurve_iff p

end Wikipedia.HopfProblem.OrbitPair
