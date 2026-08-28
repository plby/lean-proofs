import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspPieceBasic

/-!
# The full cusp piece from the constructed global special periods

A normalized sphere biholomorphism supplies the global period functions,
their analytic cusp data, and the small disjoint filling patches.  The
proved radius bound therefore instantiates the actual full toric cusp
quotient and its proper surjective projection without any extra analytic,
topological, or small-radius hypotheses.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspPiece

open ToricCharts

attribute [local instance] triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))

/-- The actual constructed analytic cusp data, restricted to the
simultaneously chosen disjoint cusp filling radius. -/
def dataOfSphere : CuspFamily.Data :=
  restrictedData (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none).le

@[simp] theorem dataOfSphere_radius :
    (dataOfSphere π hπ h₀ h₁).radius = (baseCoverOfSphere π hπ h₀ h₁).radius none := rfl

@[simp] theorem dataOfSphere_correction :
    (dataOfSphere π hπ h₀ h₁).correction =
      (Construction.cuspDataOfSphere π hπ h₀ h₁).correction := rfl

/-- The full actual cusp piece, including the toric central fibre. -/
abbrev OfSphere : Type := CuspQuotient.QuotientSpace
  (dataOfSphere π hπ h₀ h₁).correction (dataOfSphere π hπ h₀ h₁).radius

/-- The unchanged native quotient atlas of this constructed piece. -/
@[instance_reducible] def nativeChartedSpaceOfSphere :
    ChartedSpace (CoordinateSpace 3) (OfSphere π hπ h₀ h₁) :=
  nativeChartedSpace (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none).le

theorem ofSphere_t2Space : T2Space (OfSphere π hπ h₀ h₁) :=
  space_t2Space (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none).le

theorem ofSphere_secondCountable : SecondCountableTopology (OfSphere π hπ h₀ h₁) :=
  space_secondCountable (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none).le

theorem ofSphere_connected : ConnectedSpace (OfSphere π hπ h₀ h₁) :=
  space_connected (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)

theorem ofSphere_nonempty : Nonempty (OfSphere π hπ h₀ h₁) :=
  space_nonempty (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)

theorem native_isManifoldOfSphere :
    letI := nativeChartedSpaceOfSphere π hπ h₀ h₁
    IsManifold (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (OfSphere π hπ h₀ h₁) :=
  native_isManifold (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none).le

/-- The actual projection to the chosen compact-base cusp patch. -/
def projectionOfSphere : OfSphere π hπ h₀ h₁ →
    (baseCoverOfSphere π hπ h₀ h₁).fillingPatch none :=
  projection (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)

theorem projectionOfSphere_continuous : Continuous (projectionOfSphere π hπ h₀ h₁) :=
  projection_continuous (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)

theorem projectionOfSphere_surjective : Surjective (projectionOfSphere π hπ h₀ h₁) :=
  projection_surjective (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)

theorem projectionOfSphere_proper : IsProperMap (projectionOfSphere π hπ h₀ h₁) :=
  projection_proper (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none).le

theorem projectionOfSphere_holomorphic_native :
    letI := nativeChartedSpaceOfSphere π hπ h₀ h₁
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3)) 𝓘(ℂ) ω
      (projectionOfSphere π hπ h₀ h₁) :=
  projection_holomorphic_native (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none).le

/-- The same actual projection with values in the entire compact base. -/
def projectionToBaseOfSphere : OfSphere π hπ h₀ h₁ → TriangleCompactifiedOrbitSpace :=
  projectionToBase (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)

@[simp] theorem projectionToBaseOfSphere_apply (x : OfSphere π hπ h₀ h₁) :
    projectionToBaseOfSphere π hπ h₀ h₁ x = (punctureChart none).symm
      (CuspQuotient.projection (dataOfSphere π hπ h₀ h₁).correction
        (dataOfSphere π hπ h₀ h₁).radius x) := rfl

theorem range_projectionToBaseOfSphere :
    range (projectionToBaseOfSphere π hπ h₀ h₁) =
      ((baseCoverOfSphere π hπ h₀ h₁).fillingPatch none : Set TriangleCompactifiedOrbitSpace) :=
  range_projectionToBase (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁)

theorem projectionToBaseOfSphere_mem_regular_iff (x : OfSphere π hπ h₀ h₁) :
    projectionToBaseOfSphere π hπ h₀ h₁ x ∈ regularPatch ↔
      CuspQuotient.projection (dataOfSphere π hπ h₀ h₁).correction
        (dataOfSphere π hπ h₀ h₁).radius x ≠ 0 :=
  projectionToBase_mem_regular_iff (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁) x

theorem projectionToBaseOfSphere_eq_cusp_iff (x : OfSphere π hπ h₀ h₁) :
    projectionToBaseOfSphere π hπ h₀ h₁ x = triangleCuspPoint ↔
      CuspQuotient.projection (dataOfSphere π hπ h₀ h₁).correction
        (dataOfSphere π hπ h₀ h₁).radius x = 0 :=
  projectionToBase_eq_cusp_iff (Construction.cuspDataOfSphere π hπ h₀ h₁)
    (baseCoverOfSphere π hπ h₀ h₁) x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspPiece
