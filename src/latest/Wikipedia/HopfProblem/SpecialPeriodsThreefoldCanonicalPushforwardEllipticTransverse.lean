import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersEllipticNativeChart
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalMeromorphicDivisorOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetectionDensity

/-!
# The actual transverse curve at the second elliptic fibre

The curve is the inverse of an original native glued chart.  Its base
coordinate is the actual ramified sphere coordinate, and its punctured
germ lies in the original regular locus.  These identities let arbitrary
native canonical sections be tested against the genuine order-two
canonical coefficient on a holomorphic transverse curve.
-/

noncomputable section

open Bundle Set Filter Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic

open EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  specialEllipticPieceChartedSpace specialFullFillingChartedSpace

local instance pushforwardEllipticSmallManifold :
    IsManifold IF ω (SpecialEllipticPiece .four) := specialEllipticPiece_isManifold .four

local instance pushforwardEllipticFullManifold :
    IsManifold IF ω (SpecialFullFilling .four) :=
  (specialFullFilling_construction .four).2.2.1

abbrev transversePoint (y : GlobalEllipticDivisor.patch) : ℂ → GlobalEllipticDivisor.patch :=
  Sections.patchTransversePoint .four y

theorem nativeChart_first_zero (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    (chartAt Model (Sections.nativePatchPoint .four y)
      (Sections.nativePatchPoint .four y)).1 = 0 :=
  Sections.nativePatchPoint_chart_first_eq_zero .four y
    (((GlobalEllipticDivisor.mem_support y.val).mp hy).trans
      EllipticGeometry.sphereValue_four.symm)

theorem transversePoint_zero (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) : transversePoint y 0 = y := by
  have h := Sections.patchTransversePoint_center .four y
  have hc : ((Sections.patchSectionChart .four y).val y.val).1 = 0 :=
    (congrArg Prod.fst (Sections.patchSectionChart_center .four y)).trans
      (nativeChart_first_zero y hy)
  rw [hc] at h
  exact h

/-- The actual inverse-chart curve is holomorphic at every central point. -/
theorem transversePoint_holomorphicAt (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    ContMDiffAt 𝓘(ℂ) IF ω (transversePoint y) 0 := by
  let a := Sections.nativePatchPoint .four y
  have hz : (chartAt Model a a).1 = 0 := nativeChart_first_zero y hy
  have ht : ((0 : ℂ), (chartAt Model a a).2) ∈ (chartAt Model a).target := by
    simpa only [← hz, Prod.mk.eta] using mem_chart_target Model a
  have hi : ContMDiffAt IF IF ω (chartAt Model a).symm
      ((0 : ℂ), (chartAt Model a a).2) :=
    contMDiffOn_chart_symm.contMDiffAt ((chartAt Model a).open_target.mem_nhds ht)
  have hc : ContMDiffAt 𝓘(ℂ) IF ω
      (fun z : ℂ => (z, (chartAt Model a a).2)) 0 :=
    (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  exact ((EllipticGeometry.nativePatchBiholomorph .four).contMDiff _).comp 0 (hi.comp 0 hc)

theorem transversePoint_val_continuousAt (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    ContinuousAt (fun z => (transversePoint y z).val) 0 :=
  continuous_subtype_val.continuousAt.comp (transversePoint_holomorphicAt y hy).continuousAt

theorem transverse_mem_target_eventually (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      (z, (chartAt Model (Sections.nativePatchPoint .four y)
        (Sections.nativePatchPoint .four y)).2) ∈
      (chartAt Model (Sections.nativePatchPoint .four y)).target := by
  simpa only [nativeChart_first_zero y hy] using
    Sections.native_transverse_mem_target_eventually .four y

/-- On each actual native chart target the root base is exactly its
first coordinate, including the central value. -/
theorem smallChartBase_inverse (a : SpecialEllipticPiece .four) {z : ℂ}
    (hz : (z, (chartAt Model a a).2) ∈ (chartAt Model a).target) :
    (PowersElliptic.smallChartBase a
      ⟨(chartAt Model a).symm (z, (chartAt Model a a).2),
        (chartAt Model a).map_target hz⟩ : ℂ) = z := by
  rw [PowersElliptic.smallChartBase, Sections.fullChartBase_coe]
  exact congrArg Prod.fst (Threefold.Canonical.Elliptic.pieceInclusion_chart_expression
    .four a hz)

/-- The literal finite sphere coordinate of the actual curve agrees
as a germ with the independently proved order-four base coordinate. -/
theorem transverseBase_eventuallyEq (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    (fun z => CanonicalGlobal.BaseTwist.finiteCoordinate
      (Threefold.projectionSphere (transversePoint y z).val)) =ᶠ[𝓝 (0 : ℂ)]
        GlobalEllipticComparison.discCoordinateExtension .four := by
  filter_upwards [transverse_mem_target_eventually y hy] with z hz
  let a := Sections.nativePatchPoint .four y
  let x : PowersElliptic.SmallChart a :=
    ⟨(chartAt Model a).symm (z, (chartAt Model a a).2), (chartAt Model a).map_target hz⟩
  calc
    _ = GlobalEllipticComparison.discCoordinate .four (PowersElliptic.smallChartBase a x) :=
      PowersElliptic.finiteCoordinate_inclusion a x
    _ = GlobalEllipticComparison.discCoordinateExtension .four
        (PowersElliptic.smallChartBase a x : ℂ) :=
      (GlobalEllipticComparison.discCoordinateExtension_coe .four _).symm
    _ = GlobalEllipticComparison.discCoordinateExtension .four z :=
      congrArg (GlobalEllipticComparison.discCoordinateExtension .four)
        (smallChartBase_inverse a hz)

/-- Nonzero transverse roots lie in the actual regular locus; no
assumed density or abstract ramification model is used. -/
theorem transversePoint_regular_eventually (y : GlobalEllipticDivisor.patch)
    (hy : y.val ∈ GlobalEllipticDivisor.support) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), (transversePoint y z).val ∈ Threefold.regularLocus := by
  filter_upwards [(transverse_mem_target_eventually y hy).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hn
  let a := Sections.nativePatchPoint .four y
  let x : PowersElliptic.SmallChart a :=
    ⟨(chartAt Model a).symm (z, (chartAt Model a a).2), (chartAt Model a).map_target hz⟩
  apply (HolomorphicForms.DetectionDensity.elliptic_inclusion_mem_regular_iff .four x.val).mpr
  rw [PowersElliptic.smallChartBase_parameter a x, smallChartBase_inverse a hz]
  exact pow_ne_zero 4 hn

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic
