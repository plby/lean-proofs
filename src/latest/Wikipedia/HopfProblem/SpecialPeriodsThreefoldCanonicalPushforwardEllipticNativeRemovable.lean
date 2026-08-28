import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardEllipticSectionGerm
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardEllipticRemovable

/-!
# Removability forced by arbitrary native canonical sections

If the coefficient of an arbitrary holomorphic canonical section
relative to the actual normalized form descends on the regular locus,
then its possible singularity at the second elliptic value is removable.
The proof derives the ramified equation from the genuine local frame
and the actual transverse chart; it does not assume a pole bound or a
formal divisor description of the arbitrary section.
-/

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  specialEllipticPieceChartedSpace

variable (V : Opens Threefold.Space)
  (s : NativeBundleSections.Section Threefold.Canonical.bundle IF V)
  (y : GlobalEllipticDivisor.patch) (hy : y.val ∈ GlobalEllipticDivisor.support)
  (hyV : y.val ∈ V) (F : ℂ → ℂ)
  (heq : ∀ x : V, x.val ∈ Threefold.regularLocus →
    s x = F (CanonicalGlobal.BaseTwist.finiteCoordinate (Threefold.projectionSphere x.val)) •
      GlobalMeromorphicSection.rawSection x.val)

include hy hyV heq

/-- The actual section equation gives the actual native transverse
coefficient, including its proved square-times-unit factor. -/
theorem transverseSectionCoefficient_ratio_eventually :
    transverseSectionCoefficient V s y hyV =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => F (GlobalEllipticComparison.discCoordinateExtension .four z) *
        (z ^ 2 * periodUnitExtension z)) := by
  filter_upwards [
    (transverseInto_val_eventuallyEq V y hy hyV).filter_mono nhdsWithin_le_nhds,
    transversePoint_regular_eventually y hy,
    (GlobalMeromorphicSection.transverseFrame_valid_eventually y hy).filter_mono
      nhdsWithin_le_nhds,
    (GlobalMeromorphicSection.transverseCoefficient_factorization y hy).filter_mono
      nhdsWithin_le_nhds,
    (transverseBase_eventuallyEq y hy).filter_mono nhdsWithin_le_nhds]
      with z hval hreg hi hfactor hbase
  let x := transverseInto V y hyV z
  let i := GlobalMeromorphicSection.transverseFrameIndex y
  have hreg' : x.val ∈ Threefold.regularLocus := by
    rw [show x.val = (transversePoint y z).val from hval]
    exact hreg
  have hi' : x.val ∈ GlobalPrescribedDivisor.cartier.transitions.baseSet i := by
    rw [show x.val = (transversePoint y z).val from hval]
    exact hi
  have hc := congrArg (fiberCoefficient i x.val) (heq x hreg')
  rw [fiberCoefficient_smul i hi', fiberCoefficient_rawSection] at hc
  change transverseSectionCoefficient V s y hyV z =
    F (CanonicalGlobal.BaseTwist.finiteCoordinate (Threefold.projectionSphere x.val)) *
      GlobalMeromorphicSection.coefficient i x.val at hc
  rw [show x.val = (transversePoint y z).val from hval] at hc
  change GlobalMeromorphicSection.coefficient i (transversePoint y z).val =
    z ^ 2 * periodUnitExtension z at hfactor
  rw [hbase, hfactor] at hc
  exact hc

/-- Only the nonzero period unit is divided out.  The order-two zero
itself is retained in the exact ramified equation. -/
theorem normalizedTransverseCoefficient_eventuallyEq :
    normalizedTransverseCoefficient V s y hyV =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => z ^ 2 * F (GlobalEllipticComparison.discCoordinateExtension .four z)) := by
  have hu : ∀ᶠ z in 𝓝 (0 : ℂ), periodUnitExtension z ≠ 0 :=
    periodUnitExtension_analyticAt.continuousAt.eventually_ne periodUnitExtension_zero_ne_zero
  filter_upwards [transverseSectionCoefficient_ratio_eventually V s y hy hyV F heq,
    hu.filter_mono nhdsWithin_le_nhds] with z hz hunit
  change transverseSectionCoefficient V s y hyV z / periodUnitExtension z = _
  apply (div_eq_iff hunit).mpr
  rw [hz]
  ring

/-- The actual order four in the base is larger than the actual order
two of the canonical form.  Thus even a simple downstairs pole is excluded. -/
theorem sub_one_mul_baseCoefficient_tendsto_zero :
    Tendsto (fun q => (q - 1) * F q) (𝓝[≠] (1 : ℂ)) (𝓝 0) :=
  CanonicalPushforwardEllipticRemovable.sub_mul_tendsto_zero_of_ramified_pullback
    (GlobalEllipticComparison.discCoordinateExtension_analyticAt .four)
    (GlobalEllipticComparison.discCoordinateExtension_zero .four)
    GlobalEllipticComparison.discCoordinateExtension_sub_one_order_four (by decide : 2 < 4)
    (normalizedTransverseCoefficient_analyticAt V s y hy hyV).continuousAt
    (normalizedTransverseCoefficient_eventuallyEq V s y hy hyV F heq)

variable (hF : ∀ᶠ q in 𝓝[≠] (1 : ℂ), AnalyticAt ℂ F q)

include hF

/-- The value of the extension is the actual finite punctured limit. -/
theorem baseCoefficient_tendsto_limUnder :
    Tendsto F (𝓝[≠] (1 : ℂ)) (𝓝 (limUnder (𝓝[≠] (1 : ℂ)) F)) :=
  TriangleHolomorphicDifferentialsRemovable.tendsto_limUnder_of_sub_mul_tendsto_zero hF
    (sub_one_mul_baseCoefficient_tendsto_zero V s y hy hyV F heq)

theorem baseCoefficient_update_analyticAt :
    AnalyticAt ℂ (Function.update F 1 (limUnder (𝓝[≠] (1 : ℂ)) F)) 1 :=
  TriangleHolomorphicDifferentialsRemovable.analyticAt_update_limUnder_of_sub_mul_tendsto_zero hF
    (sub_one_mul_baseCoefficient_tendsto_zero V s y hy hyV F heq)

/-- A genuine analytic coefficient on a neighborhood of the second
elliptic value, agreeing with the arbitrary descended coefficient off it. -/
theorem exists_analytic_baseCoefficient_extension :
    ∃ Fext : ℂ → ℂ, AnalyticAt ℂ Fext 1 ∧
      Fext =ᶠ[𝓝[≠] (1 : ℂ)] F ∧ Fext 1 = limUnder (𝓝[≠] (1 : ℂ)) F :=
  TriangleHolomorphicDifferentialsRemovable.exists_analytic_extension_of_sub_mul_tendsto_zero hF
    (sub_one_mul_baseCoefficient_tendsto_zero V s y hy hyV F heq)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Elliptic
