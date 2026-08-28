import Wikipedia.HopfProblem.ThreefoldCircleActionSemifree
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldConnected
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# The literal orbit space of the constructed circle action

This is the quotient of the original threefold by its original period-one
circle action. It is compact, Hausdorff, second countable and connected.
The original fixed curve embeds as a closed subset of this quotient, and the
original projection to the Riemann sphere descends with connected fibres.

None of these statements identifies the orbit space with a five-sphere or
its fixed-curve complement with a product. Those geometric identifications
remain separate tasks in the unconditional sphere-recognition route.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CircleOrbitSpace

open Homology.DeltaSweep

local notation "Circle" => PeriodTorusHigherHomology.CircleTopology.Circle

attribute [local instance] Threefold.space_compact Threefold.space_t2Space
  Threefold.space_secondCountable Threefold.space_connected

local instance : AddAction Circle Space := circleAction
local instance : ContinuousVAdd Circle Space := circleAction_continuous

/-- Compactness makes the actual circle action proper. -/
theorem circleAction_proper : ProperVAdd Circle Space where
  isProperMap_vadd_pair := (actionMap.continuous.prodMk continuous_snd).isProperMap

/-- The quotient by the original additive-circle orbit relation. -/
abbrev OrbitSpace := Quotient (AddAction.orbitRel Circle Space)

/-- The original orbit projection, with the quotient topology on its target. -/
def quotientMap : Space → OrbitSpace := Quotient.mk (AddAction.orbitRel Circle Space)

theorem quotientMap_isOpenQuotientMap : IsOpenQuotientMap quotientMap :=
  AddAction.isOpenQuotientMap_quotientMk

theorem quotientMap_continuous : Continuous quotientMap :=
  quotientMap_isOpenQuotientMap.continuous

theorem quotientMap_surjective : Function.Surjective quotientMap :=
  quotientMap_isOpenQuotientMap.surjective

instance orbitSpace_compact : CompactSpace OrbitSpace := inferInstance

instance orbitSpace_t2Space : T2Space OrbitSpace := by
  let := circleAction_proper
  infer_instance

instance orbitSpace_secondCountable : SecondCountableTopology OrbitSpace :=
  ContinuousConstVAdd.secondCountableTopology

instance orbitSpace_connected : ConnectedSpace OrbitSpace :=
  quotientMap_surjective.connectedSpace quotientMap_continuous

theorem quotientMap_isProperMap : IsProperMap quotientMap :=
  quotientMap_continuous.isProperMap

/-- Equality in this quotient is exactly the original circle orbit relation. -/
theorem quotientMap_eq_iff (x y : Space) :
    quotientMap x = quotientMap y ↔ ∃ t : Circle, actionMap (t, y) = x := by
  constructor
  · intro h
    exact Quotient.exact h
  · rintro ⟨t, ht⟩
    exact Quotient.sound ⟨t, ht⟩

@[simp] theorem quotientMap_actionMap (t : Circle) (x : Space) :
    quotientMap (actionMap (t, x)) = quotientMap x :=
  Quotient.sound ⟨t, rfl⟩

/-- Projection of the actual fixed curve to the literal orbit quotient. -/
def fixedCurveMap : C(VerticalAction.D₀, OrbitSpace) :=
  ⟨fun x => quotientMap x, quotientMap_continuous.comp continuous_subtype_val⟩

@[simp] theorem fixedCurveMap_apply (x : VerticalAction.D₀) :
    fixedCurveMap x = quotientMap x := rfl

theorem fixedCurveMap_injective : Function.Injective fixedCurveMap := by
  intro x y h
  obtain ⟨t, ht⟩ := (quotientMap_eq_iff x y).mp h
  have hy : actionMap (t, y) = y :=
    (VerticalAction.action_fixed_iff (y : Space)).mpr y.property (circleParameter t)
  exact Subtype.ext (ht.symm.trans hy)

/-- The entire fixed curve, not merely each local chart, embeds in the actual quotient. -/
theorem fixedCurveMap_isClosedEmbedding : IsClosedEmbedding fixedCurveMap := by
  let : CompactSpace VerticalAction.D₀ :=
    isCompact_iff_compactSpace.mp VerticalAction.D₀_isClosed.isCompact
  exact fixedCurveMap.continuous.isClosedEmbedding fixedCurveMap_injective

def fixedCurveHomeomorph : VerticalAction.D₀ ≃ₜ Set.range fixedCurveMap :=
  fixedCurveMap_isClosedEmbedding.isEmbedding.toHomeomorph

@[simp] theorem fixedCurveHomeomorph_apply (x : VerticalAction.D₀) :
    (fixedCurveHomeomorph x : OrbitSpace) = quotientMap x := rfl

theorem fixedCurveRange_isClosed : IsClosed (Set.range fixedCurveMap) :=
  fixedCurveMap_isClosedEmbedding.isClosed_range

/-- No nonfixed orbit projects onto the image of the fixed curve. -/
theorem quotientMap_preimage_fixedCurveRange :
    quotientMap ⁻¹' Set.range fixedCurveMap = VerticalAction.D₀ := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨t, ht⟩ := (quotientMap_eq_iff x y).mp hy.symm
    have hyfix : actionMap (t, y) = y :=
      (VerticalAction.action_fixed_iff (y : Space)).mpr y.property (circleParameter t)
    have he : x = (y : Space) := ht.symm.trans hyfix
    simpa only [he] using y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The same original base map is constant on every genuine circle orbit. -/
theorem projectionSphere_actionMap (t : Circle) (x : Space) :
    projectionSphere (actionMap (t, x)) = projectionSphere x := by
  let := VerticalAction.action
  exact VerticalAction.projectionSphere_action (circleParameter t) x

/-- The original Riemann-sphere projection descends through the actual orbit relation. -/
def baseProjection : OrbitSpace → RiemannSphere :=
  Quotient.lift projectionSphere (by
    intro x y h
    obtain ⟨t, rfl⟩ := h
    exact projectionSphere_actionMap t y)

@[simp] theorem baseProjection_quotientMap (x : Space) :
    baseProjection (quotientMap x) = projectionSphere x := rfl

theorem baseProjection_continuous : Continuous baseProjection :=
  quotientMap_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
    projectionSphere_continuous

theorem baseProjection_surjective : Function.Surjective baseProjection := by
  intro b
  obtain ⟨x, hx⟩ := projectionSphere_surjective b
  exact ⟨quotientMap x, hx⟩

theorem baseProjection_isProperMap : IsProperMap baseProjection :=
  baseProjection_continuous.isProperMap

/-- The descended fibre is exactly the image of the original threefold fibre. -/
theorem baseProjection_fibre_eq (b : RiemannSphere) :
    baseProjection ⁻¹' {b} = quotientMap '' (projectionSphere ⁻¹' {b}) := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := quotientMap_surjective q
    exact ⟨x, hq, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

theorem baseProjection_fibre_isConnected (b : RiemannSphere) :
    IsConnected (baseProjection ⁻¹' {b}) := by
  rw [baseProjection_fibre_eq]
  exact (projectionSphere_fibre_isConnected b).image quotientMap
    quotientMap_continuous.continuousOn

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CircleOrbitSpace
