import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalMeromorphicSection

/-!
# The actual zero and pole orders of the native meromorphic canonical form

The zero set off the cusp is exactly the second elliptic surface.  In
genuine holomorphic nonvanishing frames of the original canonical bundle,
the transverse coefficient has order two at every point of that surface.
At the cusp the native coefficient is the reciprocal of a product of
distinct branch coordinates times an analytic unit, on the actual chart
and generic locus.  All coefficients are read after the proved native
bundle isomorphism; none is assigned a divisor multiplicity by definition.
-/

noncomputable section

open Bundle Set Filter Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalMeromorphicSection

open TrianglePeriodFamily.Canonical
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iκ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)
local notation "E₃" => ToricCharts.CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  CuspGeometry.nativeChartedSpace specialEllipticPieceChartedSpace

/-- A valid genuine holomorphic frame detects the zero of the native section. -/
theorem rawSection_eq_zero_iff_coefficient (i : GlobalPrescribedDivisor.Index)
    {x : Threefold.Space}
    (hi : x ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet i) :
    rawSection x = 0 ↔ coefficient i x = 0 := by
  rw [rawSection_eq_smul_frame i hi, smul_eq_zero]
  exact or_iff_left (frame_ne_zero i hi)

/-- On the finite base chart the native canonical coefficient is exactly
the actual effective-divisor coefficient. -/
theorem coefficient_finite_eq (i : GlobalEllipticDivisor.Index) {x : Threefold.Space}
    (hx : Threefold.projectionSphere x ≠ (∞ : RiemannSphere)) :
    coefficient (false, i) x = GlobalEllipticDivisor.transitions.localCoefficient
      GlobalEllipticDivisor.canonicalSection i x :=
  (coefficient_eq (false, i) x).trans (GlobalPrescribedDivisor.finite_localCoefficient i hx)

/-- Away from the pole fibre, the actual canonical form vanishes exactly
on the actual second elliptic surface. -/
theorem rawSection_eq_zero_iff_of_finite {x : Threefold.Space}
    (hx : Threefold.projectionSphere x ≠ (∞ : RiemannSphere)) :
    rawSection x = 0 ↔ x ∈ GlobalEllipticDivisor.support := by
  let i := GlobalEllipticDivisor.transitions.indexAt x
  have hi : x ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet (false, i) :=
    ⟨(mem_finiteChart _).mpr hx, GlobalEllipticDivisor.transitions.mem_baseSet_at x⟩
  have hc : coefficient (false, i) x =
      id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x) :=
    (coefficient_finite_eq i hx).trans
      (GlobalEllipticDivisor.transitions.localCoefficient_indexAt
        GlobalEllipticDivisor.canonicalSection x)
  calc
    rawSection x = 0 ↔ coefficient (false, i) x = 0 :=
      rawSection_eq_zero_iff_coefficient (false, i) hi
    _ ↔ GlobalEllipticDivisor.canonicalSection x = 0 := by
      change coefficient (false, i) x = 0 ↔
        id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x) = 0
      rw [hc]
    _ ↔ x ∈ GlobalEllipticDivisor.support := GlobalEllipticDivisor.canonicalSection_eq_zero_iff x

theorem rawSection_eq_zero_iff_outside_cusp {x : Threefold.Space}
    (hx : x ∈ GlobalCusp.outside) :
    rawSection x = 0 ↔ Threefold.projectionSphere x = ((1 : ℂ) : RiemannSphere) :=
  rawSection_eq_zero_iff_of_finite hx

/-- The zero-set statement excludes the pole fibre, where no holomorphic
extension of the raw total function is asserted. -/
theorem rawSection_zeroSet_outside_cusp :
    {x : Threefold.Space | x ∈ GlobalCusp.outside ∧ rawSection x = 0} =
      GlobalEllipticDivisor.support := by
  ext x
  constructor
  · rintro ⟨hx, hz⟩
    exact (rawSection_eq_zero_iff_of_finite hx).mp hz
  · intro hx
    have hf := GlobalPrescribedDivisor.fourPatch_projection_ne_infty
      (GlobalEllipticDivisor.support_subset_patch hx)
    exact ⟨hf, (rawSection_eq_zero_iff_of_finite hf).mpr hx⟩

/-- The finite source chart matching the actual transverse elliptic chart. -/
def transverseFrameIndex (y : GlobalEllipticDivisor.patch) : GlobalPrescribedDivisor.Index :=
  (false, some (Sections.patchSectionChart .four y))

/-- This is the coefficient of the native canonical section in its
genuine holomorphic frame, along the actual global inverse-chart line. -/
def transverseCoefficient (y : GlobalEllipticDivisor.patch) (z : ℂ) : ℂ :=
  coefficient (transverseFrameIndex y) (Sections.patchTransversePoint .four y z).val

theorem transverseCoefficient_eq_prescribed (y : GlobalEllipticDivisor.patch) :
    transverseCoefficient y = GlobalPrescribedDivisor.transverseCoefficient y := by
  funext z
  exact coefficient_eq (transverseFrameIndex y) (Sections.patchTransversePoint .four y z).val

theorem transverseFrameMap_holomorphicOn (y : GlobalEllipticDivisor.patch) :
    ContMDiffOn IF Iκ ω (frameMap (transverseFrameIndex y))
      (GlobalPrescribedDivisor.cartier.transitions.baseSet (transverseFrameIndex y)) :=
  frameMap_holomorphicOn (transverseFrameIndex y)

/-- The frame is valid near zero on the actual transverse chart curve,
at every central elliptic point. -/
theorem transverseFrame_valid_eventually (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    ∀ᶠ z in 𝓝 (0 : ℂ), (Sections.patchTransversePoint .four y z).val ∈
      GlobalPrescribedDivisor.cartier.transitions.baseSet (transverseFrameIndex y) := by
  have hc := Sections.nativePatchPoint_chart_first_eq_zero .four y
    (((GlobalEllipticDivisor.mem_support y.val).mp hy).trans EllipticGeometry.sphereValue_four.symm)
  have hs : ∀ᶠ z in 𝓝 (0 : ℂ), (Sections.patchTransversePoint .four y z).val ∈
      (Sections.patchSectionChart .four y).val.source := by
    simpa only [hc] using Sections.patchTransversePoint_mem_source_eventually .four y
  filter_upwards [hs] with z hz
  exact GlobalComparisonElliptic.source_chart_mem (Sections.patchSectionChart .four y)
    (Sections.patchTransversePoint .four y z).property hz

/-- The transverse coefficient represents the actual native section in
the holomorphic nonzero frame throughout a neighborhood of the center. -/
theorem rawSection_transverse_frame_eventually (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      frame (transverseFrameIndex y) (Sections.patchTransversePoint .four y z).val ≠ 0 ∧
      rawSection (Sections.patchTransversePoint .four y z).val =
        transverseCoefficient y z •
          frame (transverseFrameIndex y) (Sections.patchTransversePoint .four y z).val := by
  filter_upwards [transverseFrame_valid_eventually y hy] with z hz
  exact ⟨frame_ne_zero (transverseFrameIndex y) hz,
    rawSection_eq_smul_frame (transverseFrameIndex y) hz⟩

theorem transverseCoefficient_analyticAt (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    AnalyticAt ℂ (transverseCoefficient y) 0 := by
  rw [transverseCoefficient_eq_prescribed]
  exact GlobalPrescribedDivisor.transverseCoefficient_analyticAt y hy

/-- The exact square-times-unit germ is an equality of actual native
canonical coefficients, not a separately specified local equation. -/
theorem transverseCoefficient_factorization (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    transverseCoefficient y =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ => z ^ 2 * SectionsUnit.discExtension (SectionsUnit.specialUnit .four) z) := by
  rw [transverseCoefficient_eq_prescribed]
  exact GlobalPrescribedDivisor.transverseCoefficient_factorization y hy

theorem transverseCoefficient_order_two (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    analyticOrderAt (transverseCoefficient y) 0 = 2 := by
  rw [transverseCoefficient_eq_prescribed]
  exact GlobalPrescribedDivisor.transverseCoefficient_order_two y hy

/-- Every point of the actual second elliptic surface has order two. -/
theorem rawSection_order_two_everywhere (x : Threefold.Space)
    (hx : x ∈ GlobalEllipticDivisor.support) :
    analyticOrderAt (transverseCoefficient
      ⟨x, GlobalEllipticDivisor.support_subset_patch hx⟩) 0 = 2 :=
  transverseCoefficient_order_two ⟨x, GlobalEllipticDivisor.support_subset_patch hx⟩ hx

/-- The cusp frame is valid at every point of the entire original cusp piece. -/
theorem cuspFrame_valid (x : CuspGeometry.LocalSpace) :
    CuspGeometry.inclusion x ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet (true, none) :=
  GlobalPrescribedDivisor.cuspPatch_subset_baseSet
    (CuspGeometry.nativePatchBiholomorph x).property

theorem cuspFrame_ne_zero (x : CuspGeometry.LocalSpace) :
    frame (true, none) (CuspGeometry.inclusion x) ≠ 0 :=
  frame_ne_zero (true, none) (cuspFrame_valid x)

theorem cuspFrameMap_holomorphicAt (x : CuspGeometry.LocalSpace) :
    ContMDiffAt IF Iκ ω (frameMap (true, none)) (CuspGeometry.inclusion x) :=
  (frameMap_holomorphicOn (true, none)).contMDiffAt
    ((GlobalPrescribedDivisor.cartier.transitions.isOpen_baseSet (true, none)).mem_nhds
      (cuspFrame_valid x))

/-- In the actual normal-crossing chart, the genuine canonical
coefficient has one reciprocal factor for each distinct branch and an
analytic unit.  The stated equality is restricted to valid frame points
of the generic locus, and holds in the original canonical fibre itself. -/
theorem cusp_normalCrossing_pole (x : CuspGeometry.LocalSpace)
    (hx : CuspGeometry.parameter x = 0) :
    ∃ J : Finset (Fin 3), ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      J.Nonempty ∧ CuspGeometry.inclusion x ∈ e.source ∧ e (CuspGeometry.inclusion x) = 0 ∧
      AnalyticAt ℂ (GlobalCusp.branchUnit J) 0 ∧ GlobalCusp.branchUnit J 0 ≠ 0 ∧
      ∀ w ∈ e.target,
        e.symm w ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet (true, none) →
        e.symm w ∈ GlobalPrescribedDivisor.cartier.genericSet →
        coefficient (true, none) (e.symm w) =
          (GlobalCusp.branchProduct J w * GlobalCusp.branchUnit J w)⁻¹ ∧
        rawSection (e.symm w) =
          (GlobalCusp.branchProduct J w * GlobalCusp.branchUnit J w)⁻¹ •
            frame (true, none) (e.symm w) ∧
        frame (true, none) (e.symm w) ≠ 0 := by
  obtain ⟨J, e, hJ, hxs, hzero, ha, hu, hfrac⟩ :=
    GlobalPrescribedDivisor.cusp_fraction_normalCrossingChart x hx
  refine ⟨J, e, hJ, hxs, hzero, ha, hu, ?_⟩
  intro w hw hi hg
  have hc := (coefficient_eq_fraction (true, none) hi hg).trans (hfrac w hw)
  refine ⟨hc, ?_, frame_ne_zero (true, none) hi⟩
  rw [rawSection_eq_smul_frame (true, none) hi, hc]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalMeromorphicSection
