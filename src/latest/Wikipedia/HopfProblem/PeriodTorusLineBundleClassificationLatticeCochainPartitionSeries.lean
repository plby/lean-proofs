import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochainPartitionGeometry
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Smooth locally finite sums

The sums used to average a lattice cocycle have locally finite supports.
They are therefore genuine convergent sums, and are locally equal to a
finite sum of smooth functions.  No convergence or smoothness of the
resulting infinite sum is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain

variable {ι F : Type*} [NormedAddCommGroup F]

theorem summable_of_locallyFinite_support {f : ι → ComplexPlane₂ → F}
    (hfin : LocallyFinite fun i => Function.support (f i)) (z : ComplexPlane₂) :
    Summable fun i => f i z :=
  summable_of_hasFiniteSupport (hfin.point_finite z)

/-- The actual sum of a locally finite family of smooth functions is smooth. -/
theorem contDiff_tsum_of_locallyFinite_support [NormedSpace ℝ F]
    {f : ι → ComplexPlane₂ → F}
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hfin : LocallyFinite fun i => Function.support (f i)) :
    ContDiff ℝ ∞ (fun z => ∑' i, f i z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨s, hs⟩ := finsum_eventually_eq_sum hfin z
  have hsum : ContDiff ℝ ∞ (fun y => ∑ i ∈ s, f i y) :=
    ContDiff.sum fun i _ => hf i
  apply hsum.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  exact (tsum_eq_finsum (hfin.point_finite y)).trans hy

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain
