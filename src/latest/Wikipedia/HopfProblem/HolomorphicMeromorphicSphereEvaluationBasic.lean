import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereRepresentative
import Wikipedia.HopfProblem.HolomorphicMeromorphicRegular

/-!
# Punctured regularity of genuine meromorphic sphere functions

Every native meromorphic function is regular away from the center on a
sufficiently small punctured neighborhood in either actual sphere chart.
A nonzero native function is also nonzero there.  Both assertions follow
from its original local numerator and denominator and the one-variable
isolated-zero theorem; neither is a hypothesis on the native function.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereEvaluation

open SphereRepresentative

local instance sphereDomain_preconnected : PreconnectedSpace (⊤ : Opens RiemannSphere) :=
  Subtype.preconnectedSpace isPreconnected_univ

/-- A native meromorphic section is genuinely holomorphic at all points
of a sufficiently small punctured chart neighborhood. -/
theorem chartValue_eventually_regularAt (s : SphereFunction) (b : Bool) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, RegularAt 𝓘(ℂ) RiemannSphere s
      ⟨RiemannSphere.standardCharts.affineMap b w, by trivial⟩ := by
  obtain ⟨U, _, hz, p, q, hq, hs⟩ := local_representation 𝓘(ℂ) RiemannSphere s
    ⟨RiemannSphere.standardCharts.affineMap b z, by trivial⟩
  have hU : ∀ᶠ w in 𝓝 z, RiemannSphere.standardCharts.affineMap b w ∈ U :=
    (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).continuous.continuousAt.eventually
      (U.isOpen.mem_nhds hz)
  filter_upwards [hU.filter_mono nhdsWithin_le_nhds,
    chartCoefficient_eventually_ne_zero U q b z hz (hq ⟨_, hz⟩)] with w hw hqw
  have hqw' : q ⟨RiemannSphere.standardCharts.affineMap b w, hw⟩ ≠ 0 := by
    rwa [chartCoefficient_apply U q b w hw] at hqw
  exact regularAt_of_local_fraction 𝓘(ℂ) RiemannSphere s p q
    (RiemannSphere.standardCharts.affineMap b w) (by trivial) hw (hs ⟨_, hw⟩) hqw'

/-- A nonzero native meromorphic function has nonzero ordinary values
on a sufficiently small punctured neighborhood in either chart. -/
theorem chartValue_eventually_ne_zero (s : SphereFunction) (hsne : s ≠ 0)
    (b : Bool) (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, chartValue s b w ≠ 0 := by
  obtain ⟨U, _, hz, p, q, hq, hs⟩ := local_representation 𝓘(ℂ) RiemannSphere s
    ⟨RiemannSphere.standardCharts.affineMap b z, by trivial⟩
  have hp : holomorphicGerm 𝓘(ℂ) RiemannSphere U
      ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ p ≠ 0 := by
    intro hpzero
    apply section_ne_zero_at_of_ne_zero 𝓘(ℂ) RiemannSphere s hsne
      ⟨RiemannSphere.standardCharts.affineMap b z, by trivial⟩
    rw [hs ⟨_, hz⟩]
    change sectionGerm 𝓘(ℂ) RiemannSphere U ⟨_, hz⟩ p /
      sectionGerm 𝓘(ℂ) RiemannSphere U ⟨_, hz⟩ q = 0
    rw [(sectionGerm_eq_zero_iff 𝓘(ℂ) RiemannSphere U ⟨_, hz⟩ p).mpr hpzero, zero_div]
  filter_upwards [chartValue_eventuallyEq_local_fraction s U p q b z hz (hq ⟨_, hz⟩) hs,
    chartCoefficient_eventually_ne_zero U p b z hz hp,
    chartCoefficient_eventually_ne_zero U q b z hz (hq ⟨_, hz⟩)] with w hw hpw hqw
  rw [hw]
  exact div_ne_zero hpw hqw

/-- The finite-chart specialization of actual punctured regularity. -/
theorem finiteValue_eventually_regularAt (s : SphereFunction) (z : ℂ) :
    ∀ᶠ (w : ℂ) in 𝓝[≠] z,
      RegularAt 𝓘(ℂ) RiemannSphere s ⟨(w : RiemannSphere), by trivial⟩ :=
  chartValue_eventually_regularAt s false z

/-- Nonzero native functions have nonzero finite-chart values off the center nearby. -/
theorem finiteValue_eventually_ne_zero (s : SphereFunction) (hs : s ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, finiteValue s w ≠ 0 :=
  chartValue_eventually_ne_zero s hs false z

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereEvaluation
