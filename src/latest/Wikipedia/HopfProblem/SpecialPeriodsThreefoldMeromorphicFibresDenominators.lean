import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicCoordinateFractions
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularFibreTopology
import Wikipedia.HopfProblem.HolomorphicMeromorphicAdmissiblePullback
import Wikipedia.HopfProblem.HolomorphicMeromorphicFibreBadSlices

/-!
# Countable bad fibres for actual local holomorphic denominators

Local denominators on the original threefold pull back to the original
regular vector cover and its native coordinates. Their fibrewise zero
germs have only countably many parameter values. The native period-vector
quotient compares these germs with restriction to the original period tori.
-/

open Set Filter Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicFibres

open HolomorphicForms.RegularCover MeromorphicRegularCover HolomorphicMeromorphic

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  coverChartedSpace cover_isManifold

/-- The actual torus inclusion, bundled with its native holomorphicity. -/
noncomputable def regularTorusInclusionMap (z : TriangleRegularPoint) :
    ContMDiffMap I₂ IF (RegularTorus z) Threefold.Space ω :=
  ⟨regularTorusInclusion z, regularTorusInclusion_holomorphic z⟩

/-- The original quotient by the actual period lattice. -/
noncomputable def regularTorusQuotientMap (z : TriangleRegularPoint) :
    ContMDiffMap I₂ I₂ ComplexPlane₂ (RegularTorus z) ω :=
  ⟨(specialPeriodMap.point z.val).lattice.mkQ,
    (specialPeriodMap.point z.val).torus_projection_holomorphic⟩

/-- Factoring a vector through its native torus quotient gives exactly
the original regular vector-cover map into the threefold. -/
theorem regularTorusInclusionMap_quotient (z : TriangleRegularPoint) (v : ComplexPlane₂) :
    regularTorusInclusionMap z (regularTorusQuotientMap z v) = toThreefold (z, v) := rfl

theorem sourceBase_eq_regularSphereValue (z : TriangleRegularPoint) :
    sourceBase z = regularSphereValue z := by
  rw [← projectionSphere_toThreefold z (0 : ComplexPlane₂),
    ← regularTorusInclusionMap_quotient]
  exact projectionSphere_regularTorusInclusion z (regularTorusQuotientMap z 0)

/-- A total map used only to take the image of a countable parameter set.
On the actual regular coordinate range it is the original sphere base map. -/
noncomputable def complexParameterSphere (a : ℂ) : RiemannSphere :=
  sourceBase (coordInv (a, (0 : ComplexPlane₂))).1

theorem complexParameterSphere_coe (z : TriangleRegularPoint) :
    complexParameterSphere (z.val : ℂ) = regularSphereValue z := by
  change sourceBase (coordInv (coord (z, (0 : ComplexPlane₂)))).1 = _
  rw [coordInv_coord]
  exact sourceBase_eq_regularSphereValue z

/-- The actual coordinate image of the inverse image of a target open set. -/
noncomputable def denominatorDomain (U : Opens Threefold.Space) : Opens Model :=
  coordOpen (pullbackOpen IF IF toThreefold U)

/-- The native analytic representative of an actual pulled-back denominator. -/
noncomputable def denominatorCoordinates (U : Opens Threefold.Space)
    (q : HolomorphicFunctionSheaf.Section IF Threefold.Space U) : Model → ℂ :=
  sectionCoordinates (pullbackOpen IF IF toThreefold U) (holomorphicPullback IF IF toThreefold U q)

theorem denominatorCoordinates_analyticOnNhd (U : Opens Threefold.Space)
    (q : HolomorphicFunctionSheaf.Section IF Threefold.Space U) :
    AnalyticOnNhd ℂ (denominatorCoordinates U q) (denominatorDomain U) :=
  sectionCoordinates_analyticOnNhd (pullbackOpen IF IF toThreefold U)
    (holomorphicPullback IF IF toThreefold U q)

/-- Ambient nonzero denominator germs remain nonzero in the original
vector-cover coordinates, since the actual cover map is holomorphic and open. -/
theorem denominatorCoordinates_nonzero_germs (U : Opens Threefold.Space)
    (q : HolomorphicFunctionSheaf.Section IF Threefold.Space U)
    (hq : ∀ x : U, holomorphicGerm IF Threefold.Space U x q ≠ 0) :
    ∀ p ∈ denominatorDomain U, ¬ denominatorCoordinates U q =ᶠ[𝓝 p] 0 := by
  rintro _ ⟨x, hx, rfl⟩ hz
  have hqcover := holomorphicPullback_nonzero_germs IF IF toThreefold
    toThreefold_isOpenMap U q hq ⟨x, hx⟩
  apply hqcover
  apply (HolomorphicFunctionSheaf.germ_eq_zero_iff_extend_eventuallyEq_zero IF
    (pullbackOpen IF IF toThreefold U) (holomorphicPullback IF IF toThreefold U q) x hx).mpr
  have he := hz.comp_tendsto (coord_continuous.tendsto x)
  filter_upwards [he] with y hy
  simpa only [denominatorCoordinates, sectionCoordinates, Function.comp_def, coordInv_coord,
    Pi.zero_apply]
    using hy

/-- The actual complex parameters with a locally zero restricted
denominator somewhere in its original coordinate domain. -/
def denominatorBadParameters (U : Opens Threefold.Space)
    (q : HolomorphicFunctionSheaf.Section IF Threefold.Space U) : Set ℂ :=
  {a | ∃ v : ComplexPlane₂, (a, v) ∈ denominatorDomain U ∧
    (fun w => denominatorCoordinates U q (a, w)) =ᶠ[𝓝 v] 0}

theorem denominatorBadParameters_countable (U : Opens Threefold.Space)
    (q : HolomorphicFunctionSheaf.Section IF Threefold.Space U)
    (hq : ∀ x : U, holomorphicGerm IF Threefold.Space U x q ≠ 0) :
    (denominatorBadParameters U q).Countable :=
  HolomorphicMeromorphicFibreBadSlices.countable_bad_slice_parameters
    (denominatorDomain U).isOpen (denominatorCoordinates_analyticOnNhd U q)
    (denominatorCoordinates_nonzero_germs U q hq)

/-- The countable obstruction set is placed in the actual sphere base. -/
def denominatorBadValues (U : Opens Threefold.Space)
    (q : HolomorphicFunctionSheaf.Section IF Threefold.Space U) : Set RiemannSphere :=
  complexParameterSphere '' denominatorBadParameters U q

theorem denominatorBadValues_countable (U : Opens Threefold.Space)
    (q : HolomorphicFunctionSheaf.Section IF Threefold.Space U)
    (hq : ∀ x : U, holomorphicGerm IF Threefold.Space U x q ≠ 0) :
    (denominatorBadValues U q).Countable :=
  (denominatorBadParameters_countable U q hq).image complexParameterSphere

/-- A zero restricted denominator germ on the original torus pulls back
along its actual holomorphic vector quotient to a zero native coordinate slice. -/
theorem denominatorCoordinates_slice_zero_of_torus_germ_zero
    (U : Opens Threefold.Space) (q : HolomorphicFunctionSheaf.Section IF Threefold.Space U)
    (z : TriangleRegularPoint) (v : ComplexPlane₂) (hv : toThreefold (z, v) ∈ U)
    (hzero : holomorphicGerm I₂ (RegularTorus z)
      (pullbackOpen I₂ IF (regularTorusInclusionMap z) U) ⟨regularTorusQuotientMap z v, hv⟩
      (holomorphicPullback I₂ IF (regularTorusInclusionMap z) U q) = 0) :
    (fun w => denominatorCoordinates U q ((z.val : ℂ), w)) =ᶠ[𝓝 v] 0 := by
  let T := pullbackOpen I₂ IF (regularTorusInclusionMap z) U
  let qT := holomorphicPullback I₂ IF (regularTorusInclusionMap z) U q
  let W := pullbackOpen I₂ I₂ (regularTorusQuotientMap z) T
  let qW := holomorphicPullback I₂ I₂ (regularTorusQuotientMap z) T qT
  have hzeroW : holomorphicGerm I₂ ComplexPlane₂ W ⟨v, hv⟩ qW = 0 := by
    have he := congrArg (holomorphicPullbackStalk I₂ I₂ (regularTorusQuotientMap z) v) hzero
    exact (holomorphicPullbackStalk_germ I₂ I₂ (regularTorusQuotientMap z) T v hv qT).symm.trans
      (he.trans (map_zero _))
  have hlocal := (HolomorphicFunctionSheaf.germ_eq_zero_iff_extend_eventuallyEq_zero
    I₂ W qW v hv).mp hzeroW
  filter_upwards [W.isOpen.mem_nhds hv, hlocal] with w hw hz
  calc
    denominatorCoordinates U q ((z.val : ℂ), w) = qW ⟨w, hw⟩ :=
      sectionCoordinates_apply (pullbackOpen IF IF toThreefold U)
        (holomorphicPullback IF IF toThreefold U q) ⟨(z, w), hw⟩
    _ = 0 := (HolomorphicFunctionSheaf.extendManifoldSection_apply I₂ W qW w hw).symm.trans hz

/-- Outside the countable sphere obstruction set, every actual restricted
denominator germ on the native period torus is nonzero. -/
theorem denominatorPullbackGerm_ne_zero (U : Opens Threefold.Space)
    (q : HolomorphicFunctionSheaf.Section IF Threefold.Space U)
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∉ denominatorBadValues U q)
    (t : pullbackOpen I₂ IF (regularTorusInclusionMap z) U) :
    holomorphicGerm I₂ (RegularTorus z)
      (pullbackOpen I₂ IF (regularTorusInclusionMap z) U) t
      (holomorphicPullback I₂ IF (regularTorusInclusionMap z) U q) ≠ 0 := by
  rcases t with ⟨t, ht⟩
  obtain ⟨v, rfl⟩ := (specialPeriodMap.point z.val).lattice.mkQ_surjective t
  intro hzero
  apply hz
  refine ⟨(z.val : ℂ), ?_, complexParameterSphere_coe z⟩
  exact ⟨v, ⟨(z, v), ht, rfl⟩,
    denominatorCoordinates_slice_zero_of_torus_germ_zero U q z v ht hzero⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicFibres
