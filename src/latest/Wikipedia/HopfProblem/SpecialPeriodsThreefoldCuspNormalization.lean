import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspFibreGeometryStrata
import Wikipedia.HopfProblem.CuspComponentImmersion
import Wikipedia.HopfProblem.CuspComponentProper

/-!
# The actual component map onto the global cusp fibre

The original compact toric surface `E₀` maps properly and holomorphically
onto the entire literal sphere fibre at infinity.  Its fibres are finite,
with cardinalities equal to the genuine number of local branches.  These
are statements about the constructed maps and native atlases; no analytic
ring-theoretic normalization property is asserted here.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry

open ToricCharts

attribute [local instance] nativeChartedSpace Threefold.chartedSpace Threefold.space_t2Space

local notation "I₂" => modelWithCornersSelf ℂ (CoordinateSpace 2)
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual component projection followed by the full cusp inclusion. -/
def componentMap : ToricSpace.rayDivisor 0 → Threefold.Space :=
  inclusion ∘ CuspQuotient.componentProjection data.correction data.radius data.radius_pos

@[simp] theorem componentMap_apply (x : ToricSpace.rayDivisor 0) :
    componentMap x = inclusion
      (CuspQuotient.componentProjection data.correction data.radius data.radius_pos x) := rfl

theorem componentMap_continuous : Continuous componentMap :=
  inclusion_continuous.comp
    (CuspQuotient.componentProjection_continuous data.correction data.radius data.radius_pos)

/-- Holomorphy uses the original two-coordinate surface atlas and the
actual glued threefold atlas. -/
theorem componentMap_holomorphic : ContMDiff I₂ IF ω componentMap := by
  let : ChartedSpace (CoordinateSpace 3)
      (CuspQuotient.QuotientSpace data.correction data.radius) := nativeChartedSpace
  have hc : ContMDiff I₂ I₃ ω
      (CuspQuotient.componentProjection data.correction data.radius data.radius_pos :
        ToricSpace.rayDivisor 0 → LocalSpace) :=
    CuspQuotient.componentProjection_holomorphic data.correction data.radius data.radius_pos
      data.radius_lt_one data.holomorphic data.smallDrift
  exact inclusion_holomorphic.comp hc

theorem componentMap_mem_sphereCuspFibre (x : ToricSpace.rayDivisor 0) :
    componentMap x ∈ sphereCuspFibre :=
  (inclusion_mem_sphereCuspFibre_iff _).mpr
    (CuspQuotient.projection_componentProjection data.correction data.radius data.radius_pos x)

@[simp] theorem projectionSphere_componentMap (x : ToricSpace.rayDivisor 0) :
    Threefold.projectionSphere (componentMap x) = (∞ : RiemannSphere) :=
  componentMap_mem_sphereCuspFibre x

/-- Every point of the literal global cusp fibre has a representative on `E₀`. -/
theorem componentMap_range : range componentMap = sphereCuspFibre := by
  have hr : range (CuspQuotient.componentProjection data.correction data.radius
      data.radius_pos : ToricSpace.rayDivisor 0 → LocalSpace) = localCentralFibre :=
    CuspQuotient.componentProjection_range data.correction data.radius data.radius_pos
  exact (Set.range_comp inclusion _).trans
    ((congrArg (Set.image inclusion) hr).trans sphereCuspFibre_eq_image.symm)

theorem componentMap_proper : IsProperMap componentMap := componentMap_continuous.isProperMap

/-- The same map, with codomain the literal global fibre. -/
def componentToFibre : ToricSpace.rayDivisor 0 → sphereCuspFibre :=
  fun x => ⟨componentMap x, componentMap_mem_sphereCuspFibre x⟩

@[simp] theorem componentToFibre_val (x : ToricSpace.rayDivisor 0) :
    (componentToFibre x : Threefold.Space) = componentMap x := rfl

theorem componentToFibre_continuous : Continuous componentToFibre :=
  componentMap_continuous.subtype_mk _

theorem componentToFibre_surjective : Function.Surjective componentToFibre := by
  intro y
  have hy : (y : Threefold.Space) ∈ range componentMap := by
    rw [componentMap_range]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

theorem componentToFibre_proper : IsProperMap componentToFibre :=
  componentToFibre_continuous.isProperMap

/-- The actual inclusion does not identify any additional points of a
native component fibre. -/
theorem componentMap_fibre_eq (x : sphereCuspFibre) :
    componentMap ⁻¹' {(x : Threefold.Space)} =
      CuspQuotient.componentProjection data.correction data.radius data.radius_pos ⁻¹'
        {(centralFibreHomeomorph.symm x : LocalSpace)} := by
  ext y
  change inclusion (CuspQuotient.componentProjection data.correction data.radius
      data.radius_pos y) = (x : Threefold.Space) ↔
    CuspQuotient.componentProjection data.correction data.radius data.radius_pos y =
      (centralFibreHomeomorph.symm x : LocalSpace)
  constructor
  · intro h
    exact inclusion_injective (h.trans (centralFibreHomeomorph_symm_inclusion x).symm)
  · intro h
    exact (congrArg inclusion h).trans (centralFibreHomeomorph_symm_inclusion x)

theorem componentMap_fibre_finite (x : sphereCuspFibre) :
    (componentMap ⁻¹' {(x : Threefold.Space)}).Finite := by
  rw [componentMap_fibre_eq x]
  exact CuspQuotient.componentProjection_fibre_finite data.correction data.radius
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift
    (centralFibreHomeomorph.symm x : LocalSpace)

theorem componentMap_fibre_card (x : sphereCuspFibre) :
    (componentMap ⁻¹' {(x : Threefold.Space)}).ncard = fibreBranchCount x :=
  (congrArg Set.ncard (componentMap_fibre_eq x)).trans
    (CuspQuotient.componentProjection_fibre_card data.correction data.radius data.radius_pos
      data.radius_lt_one data.holomorphic data.smallDrift
      (centralFibreHomeomorph.symm x : LocalSpace))

theorem componentToFibre_fibre_eq (x : sphereCuspFibre) :
    componentToFibre ⁻¹' {x} = componentMap ⁻¹' {(x : Threefold.Space)} := by
  ext y
  change componentToFibre y = x ↔ componentMap y = (x : Threefold.Space)
  exact Subtype.ext_iff

theorem componentToFibre_fibre_finite (x : sphereCuspFibre) :
    (componentToFibre ⁻¹' {x}).Finite := by
  rw [componentToFibre_fibre_eq x]
  exact componentMap_fibre_finite x

theorem componentToFibre_fibre_card (x : sphereCuspFibre) :
    (componentToFibre ⁻¹' {x}).ncard = fibreBranchCount x :=
  (congrArg Set.ncard (componentToFibre_fibre_eq x)).trans (componentMap_fibre_card x)

theorem componentToFibre_fibre_card_pos (x : sphereCuspFibre) :
    0 < (componentToFibre ⁻¹' {x}).ncard := by
  rw [componentToFibre_fibre_card]
  exact fibreBranchCount_pos x

theorem componentToFibre_fibre_card_le_three (x : sphereCuspFibre) :
    (componentToFibre ⁻¹' {x}).ncard ≤ 3 := by
  rw [componentToFibre_fibre_card]
  exact fibreBranchCount_le_three x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry
