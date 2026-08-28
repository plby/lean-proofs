import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspBasic
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationToricSmooth
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealMaps
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationOpenRestriction

/-!
# Native real-analytic normal coordinates through the cusp quotient

The product map uses the original toric tube, the original analytic
covering quotient, and the original cusp inclusion. All three maps are
local diffeomorphisms for the unchanged native atlases. Only the scalar
field of differentiability is restricted from complex to real.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open ToricCharts SpecialPeriods SpecialPeriods.Threefold

local notation "CD" => CuspGeometry.data
local notation "IP" => 𝓘(ℝ, Model)
local notation "I₃" => 𝓘(ℝ, CoordinateSpace 3)
local notation "IX" => 𝓘(ℝ, ℂ × ComplexPlane₂)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

/-- The actual restriction to the toric tube is locally real analytically invertible. -/
theorem toTube_isLocalDiffeomorph : IsLocalDiffeomorph IP I₃ ω toTube :=
  OpenRestriction.isLocalDiffeomorph_restrictOpens IP I₃
    fromProduct_isLocalDiffeomorph smallNormalProduct
    (ToricSpace.tubeOpen (CuspQuotient.disc (CD).radius))
    (fun x hx => (toTube ⟨x, hx⟩).property)

/-- The original covering quotient remains a local diffeomorphism in the real native atlases. -/
theorem nativeQuotientMap_isLocalDiffeomorph :
    IsLocalDiffeomorph (N := CuspGeometry.LocalSpace) I₃ I₃ ω
      (CuspQuotient.quotientMap (CD).correction (CD).radius :
        ToricSpace.Tube (CuspQuotient.disc (CD).radius) → CuspGeometry.LocalSpace) := by
  let := CuspQuotient.chartedSpace (CD).correction (CD).radius (CD).radius_pos
    (CD).radius_lt_one (CD).holomorphic (CD).smallDrift
  let : ChartedSpace (CoordinateSpace 3) CuspGeometry.LocalSpace :=
    CuspGeometry.nativeChartedSpace
  exact isLocalDiffeomorph_real_of_complex
    (CuspUniformization.quotientMap_isLocalDiffeomorph (CD).correction (CD).radius
      (CD).radius_pos (CD).radius_lt_one (CD).holomorphic (CD).smallDrift)

/-- Native real analyticity of the literal small product map into the original threefold. -/
theorem globalProductMap_isLocalDiffeomorph :
    IsLocalDiffeomorph IP IX ω globalProductMap := by
  intro p
  have hq := (toTube_isLocalDiffeomorph p).comp (K := I₃) (P := CuspGeometry.LocalSpace)
    (nativeQuotientMap_isLocalDiffeomorph (toTube p))
  exact hq.comp (K := IX) (P := Threefold.Space)
    (isLocalDiffeomorphAt_real_of_complex
      (CuspGeometry.inclusion_isLocalDiffeomorph
        (CuspQuotient.quotientMap (CD).correction (CD).radius (toTube p))))

theorem globalProductMap_contMDiff : ContMDiff IP IX ω globalProductMap :=
  globalProductMap_isLocalDiffeomorph.contMDiff

theorem globalProductMap_isLocalHomeomorph : IsLocalHomeomorph globalProductMap :=
  globalProductMap_isLocalDiffeomorph.isLocalHomeomorph

theorem globalProductMap_isOpenMap : IsOpenMap globalProductMap :=
  globalProductMap_isLocalHomeomorph.isOpenMap

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
