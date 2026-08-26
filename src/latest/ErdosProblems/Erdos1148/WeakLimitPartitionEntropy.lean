import ErdosProblems.Erdos1148.FinitePartitionEntropy
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Entropy continuity for finite families of continuity sets -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

theorem finitePartitionEntropy_tendsto_of_weak_limit {X ι κ : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] [Fintype κ] {l : Filter ι}
    {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hlim : Tendsto μ l (𝓝 ν)) (s : κ → Set X)
    (hboundary : ∀ k, (ν : Measure X) (frontier (s k)) = 0) :
    Tendsto (fun i => finitePartitionEntropy (μ i : Measure X) s) l
      (𝓝 (finitePartitionEntropy (ν : Measure X) s)) := by
  have hmass (k : κ) : Tendsto (fun i => (μ i : Measure X).real (s k)) l
      (𝓝 ((ν : Measure X).real (s k))) :=
    (ENNReal.continuousAt_toReal (measure_ne_top _ _)).tendsto.comp
      (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlim (hboundary k))
  exact continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hmass)

end Erdos1148.DukeArithmetic
