import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspNormalization
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCoverCohomology
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativePullbackIso

/-!
# The original normalization surface and its holomorphic map to X

The source is the original zero-ray toric surface with its original
two-coordinate atlas.  The map is the already constructed component
projection followed by the original global cusp inclusion.  Its literal
factorization passes through the existing reduced central-fibre subtype.
The positive holomorphic cohomology of this same surface is already
computed by the actual three-open cover of the original toric charts.
-/

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LineBundleNormalization

attribute [local instance] chartedSpace

local notation "I₂" => modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 2)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The original normalization surface, without any changed topology or atlas. -/
abbrev Surface := ToricSpace.rayDivisor 0

/-- The original reduced cusp space used by the normalization sheaf resolution. -/
abbrev ReducedCusp := CuspNormalization.SheafResolution.CentralSpace
  CuspGeometry.data.correction CuspGeometry.data.radius

/-- Bundle the original holomorphic component map to the original threefold. -/
def normalizationMap : ContMDiffMap I₂ IF Surface Space ω :=
  ⟨CuspGeometry.componentMap, CuspGeometry.componentMap_holomorphic⟩

@[simp] theorem normalizationMap_apply (x : Surface) :
    normalizationMap x = CuspGeometry.componentMap x := rfl

/-- This is the literal original normalization into the reduced cusp,
followed by the original cusp inclusion into the glued threefold. -/
theorem normalizationMap_factorization (x : Surface) :
    normalizationMap x = CuspGeometry.inclusion
      ((CuspNormalization.SheafResolution.normalization
        CuspGeometry.data.correction CuspGeometry.data.radius CuspGeometry.data.radius_pos x :
          ReducedCusp).val) := rfl

/-- The same original map also factors through the literal global cusp fibre. -/
theorem normalizationMap_globalFibre (x : Surface) :
    normalizationMap x = (CuspGeometry.componentToFibre x : Space) := rfl

/-- Genuine Ext-defined first holomorphic cohomology of the original
normalization surface vanishes by the proved original toric cover calculation. -/
theorem surface_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf I₂ Surface) 1) :=
  HolomorphicSheafCohomology.ZeroRayCover.zeroRay_higher_subsingleton 0

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LineBundleNormalization
