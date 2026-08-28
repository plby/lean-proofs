import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapConstruction
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapPartial
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapBaseCoordinates

/-!
# Cusp overlap maps for the constructed sphere-normalized periods

The proved period agreement supplies the complete cusp-to-regular-family
biholomorphism and its ambient partial biholomorphism for the constructed
period data. Their atlases remain the native cusp quotient atlas and the
native regular-family quotient atlas. The exact source, full target, and
compact-base formulas are inherited from the actual overlap construction.

The only parameters are a normalized sphere equivalence and a common
positive radius. There is no supplied overlap map or period-agreement
hypothesis. The final chosen-radius specialization can instantiate these
maps with the actual triangle uniformization.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap

open CuspFamily Triangle CuspUniformization ToricCharts

attribute [local instance] triangleCompactifiedChartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))
  (r : ℝ) (hr : 0 < r)
  (hrD : r ≤ (Construction.cuspDataOfSphere π hπ h₀ h₁).radius)
  (hrcap : r ≤ cuspRadius width)

local notation "Cₛ" => sphereCuspData π hπ h₀ h₁ r hr hrD
local notation "Dₛ" => sphereRegularData π hπ h₀ h₁
local notation "Pₛ" => spherePeriod_agreement π hπ h₀ h₁ r hr hrD hrcap

/-- The whole punctured cusp family is biholomorphic to the full regular
family over the common cusp patch, for the constructed period functions. -/
def spherePuncturedBiholomorph :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    Diffeomorph I₃ IF (PuncturedQuotient (Cₛ).correction (Cₛ).radius)
      (familyPatch Cₛ Dₛ hrcap) ω :=
  puncturedBiholomorph Cₛ Dₛ hrcap Pₛ

/-- The ambient cusp filling and the unchanged regular family carry the
actual partial biholomorphism required for gluing. -/
def sphereCuspToRegularPartial :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    PartialDiffeomorph I₃ IF
      (CuspQuotient.QuotientSpace (Cₛ).correction (Cₛ).radius) (Dₛ).Space ω :=
  cuspToRegularPartial Cₛ Dₛ hrcap Pₛ

/-- Exact compact-base compatibility of the whole punctured comparison. -/
theorem spherePuncturedBiholomorph_preserves_base
    (x : PuncturedQuotient (Cₛ).correction (Cₛ).radius) :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    compactProjection Dₛ (spherePuncturedBiholomorph π hπ h₀ h₁ r hr hrD hrcap x) =
      (cuspFullChart width le_rfl).symm
        (CuspQuotient.projection (Cₛ).correction (Cₛ).radius x) :=
  puncturedBiholomorph_preserves_base Cₛ Dₛ hrcap Pₛ x

/-- The actual forward cusp coordinate is unchanged on the entire
punctured-family comparison. -/
theorem spherePuncturedBiholomorph_coordinate
    (x : PuncturedQuotient (Cₛ).correction (Cₛ).radius) :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    cuspFullChart width le_rfl
      (compactProjection Dₛ (spherePuncturedBiholomorph π hπ h₀ h₁ r hr hrD hrcap x)) =
        CuspQuotient.projection (Cₛ).correction (Cₛ).radius x :=
  puncturedBiholomorph_coordinate Cₛ Dₛ hrcap Pₛ x

@[simp] theorem sphereCuspToRegularPartial_source :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap).source =
      (puncturedQuotientOpen (Cₛ).correction (Cₛ).radius : Set _) :=
  cuspToRegularPartial_source Cₛ Dₛ hrcap Pₛ

@[simp] theorem sphereCuspToRegularPartial_target :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap).target =
      (familyPatch Cₛ Dₛ hrcap : Set (Dₛ).Space) :=
  cuspToRegularPartial_target Cₛ Dₛ hrcap Pₛ

/-- The source is exactly the complement of the central cusp fibre. -/
theorem sphereCuspToRegularPartial_source_iff
    (x : CuspQuotient.QuotientSpace (Cₛ).correction (Cₛ).radius) :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    x ∈ (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap).source ↔
      CuspQuotient.projection (Cₛ).correction (Cₛ).radius x ≠ 0 :=
  cuspToRegularPartial_source_iff Cₛ Dₛ hrcap Pₛ x

/-- The target is the whole regular family over the precise round cusp
coordinate patch, not merely a neighborhood of the zero section. -/
theorem sphereCuspToRegularPartial_target_iff (y : (Dₛ).Space) :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    y ∈ (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap).target ↔
      compactProjection Dₛ y ∈ (cuspFullChart width le_rfl).source ∧
        ‖cuspFullChart width le_rfl (compactProjection Dₛ y)‖ < r :=
  cuspToRegularPartial_target_iff Cₛ Dₛ hrcap Pₛ y

theorem sphereCuspToRegularPartial_apply
    (x : CuspQuotient.QuotientSpace (Cₛ).correction (Cₛ).radius)
    (hx : x ∈ puncturedQuotientOpen (Cₛ).correction (Cₛ).radius) :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap x =
      (spherePuncturedBiholomorph π hπ h₀ h₁ r hr hrD hrcap ⟨x, hx⟩ : (Dₛ).Space) :=
  cuspToRegularPartial_apply Cₛ Dₛ hrcap Pₛ x hx

/-- The ambient gluing map preserves the complete compact-base map on
every point of its exact source. -/
theorem sphereCuspToRegularPartial_preserves_base
    (x : CuspQuotient.QuotientSpace (Cₛ).correction (Cₛ).radius)
    (hx : x ∈ puncturedQuotientOpen (Cₛ).correction (Cₛ).radius) :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    compactProjection Dₛ (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap x) =
      (cuspFullChart width le_rfl).symm
        (CuspQuotient.projection (Cₛ).correction (Cₛ).radius x) :=
  cuspToRegularPartial_preserves_base Cₛ Dₛ hrcap Pₛ x hx

theorem sphereCuspToRegularPartial_symm_apply (y : (Dₛ).Space)
    (hy : y ∈ familyPatch Cₛ Dₛ hrcap) :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    (sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap).symm y =
      ((spherePuncturedBiholomorph π hπ h₀ h₁ r hr hrD hrcap).symm ⟨y, hy⟩ :
        CuspQuotient.QuotientSpace (Cₛ).correction (Cₛ).radius) :=
  cuspToRegularPartial_symm_apply Cₛ Dₛ hrcap Pₛ y hy

/-- The inverse ambient gluing map has the matching full base formula. -/
theorem sphereCuspToRegularPartial_symm_preserves_base (y : (Dₛ).Space)
    (hy : y ∈ familyPatch Cₛ Dₛ hrcap) :
    letI := CuspQuotient.chartedSpace (Cₛ).correction (Cₛ).radius (Cₛ).radius_pos
      (Cₛ).radius_lt_one (Cₛ).holomorphic (Cₛ).smallDrift
    letI := (Dₛ).chartedSpace (familyCovering Dₛ)
    CuspQuotient.projection (Cₛ).correction (Cₛ).radius
      ((sphereCuspToRegularPartial π hπ h₀ h₁ r hr hrD hrcap).symm y) =
        cuspFullChart width le_rfl (compactProjection Dₛ y) :=
  cuspToRegularPartial_symm_preserves_base Cₛ Dₛ hrcap Pₛ y hy

end Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap
