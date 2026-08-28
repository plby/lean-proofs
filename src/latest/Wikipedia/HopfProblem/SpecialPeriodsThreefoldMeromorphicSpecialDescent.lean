import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicSpecialPowerComparison
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicConnectedDescent
import Wikipedia.HopfProblem.HolomorphicMeromorphicPowerModelSections
import Wikipedia.HopfProblem.HolomorphicMeromorphicPartialDiffeomorphExtension

/-!
# Genuine meromorphic descent at all three special fibres

The arbitrary global section, expressed in the proved native power chart,
supplies its own local holomorphic numerator and denominator. A nonzero
transverse denominator slice proves meromorphic extension of the actual
regular-base section through the chart origin. Its native inverse-chart
extension agrees with the regular descent at an actual overlapping germ.
Connectedness of the full inverse image extends that equality to every
point over the special-value neighborhood.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open HolomorphicMeromorphic HolomorphicMeromorphic.PartialBiholomorph

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

namespace SpecialBasePowerChart

variable {b : RiemannSphere} (D : SpecialBasePowerChart b)

/-- The actual regular descent has a meromorphic extension at the origin
of every proved native special-value chart. -/
theorem baseSection_meromorphicAt_zero
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (MeromorphicRegularCover.constantRegularFibres g).Countable)
    (hb : b ∉ sphereRegularPatch) :
    MeromorphicAt (scalarValue (D.baseSection (regularSphereDescent g hg))) 0 :=
  HolomorphicMeromorphicPowerModelSections.meromorphicAt_scalarValue_of_section_power_model
    (D.modelSection g) (D.chart D.point).2 D.center_mem_modelDomain
    (D.baseSection (regularSphereDescent g hg)) D.degree_pos
    (D.eventually_modelSection_power_germ g hg hb)

/-- The proved scalar extension is a genuine local sphere section and
its actual projection pullback is the original global section everywhere
over the special-value neighborhood. -/
theorem meromorphicallyDescendsNear (D : SpecialBasePowerChart b)
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (MeromorphicRegularCover.constantRegularFibres g).Countable)
    (hb : b ∉ sphereRegularPatch) : Threefold.MeromorphicallyDescendsNear g b := by
  have hdomain : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      t ∈ D.baseChart.target ∧ D.baseChart.symm t ∈ sphereRegularPatch := by
    filter_upwards [nhdsWithin_le_nhds (D.eventually_base_regular_iff hb),
      self_mem_nhdsWithin] with t ht htzero
    exact ⟨ht.1, ht.2.mpr htzero⟩
  obtain ⟨W, hbW, hW, _, a, y, hyW, hyR, he⟩ :=
    exists_connected_extension_of_scalar_meromorphicAt I₁ D.baseChart sphereRegularPatch
      (regularSphereDescent g hg) b D.base_mem_source D.base_value hdomain
      (D.baseSection_meromorphicAt_zero g hg hb)
  exact meromorphicallyDescendsNear_of_regular_overlap g hg b W hbW hW a y hyW hyR he

end SpecialBasePowerChart

/-- Genuine local descent at every exceptional value, using the actual
elliptic or cusp chart rather than assuming extension data. -/
theorem meromorphicallyDescendsNear_special
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (hg : ¬ (MeromorphicRegularCover.constantRegularFibres g).Countable)
    (b : RiemannSphere) (hb : b ∉ sphereRegularPatch) :
    MeromorphicallyDescendsNear g b :=
  (specialBasePowerChart b hb).meromorphicallyDescendsNear g hg hb

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
