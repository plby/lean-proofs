import ErdosProblems.Erdos1148.FiniteOrbitEntropy
import ErdosProblems.Erdos1148.WeakLimitPartitionEntropy
import ErdosProblems.Erdos1148.NullBoundaryOperations

/-! # Passing finite orbit entropy inequalities to weak limits -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

namespace FiniteMeasurablePartition

variable {X ι κ : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem measure_frontier_orbitAtom_eq_zero (P : FiniteMeasurablePartition X κ)
    (μ : Measure X) {f : X → X} (hf : Continuous f) (hinv : Measure.map f μ = μ)
    (hboundary : ∀ k, μ (frontier (P.atom k)) = 0) (n : ℕ) (w : Fin n → κ) :
    μ (frontier (P.orbitAtom f n w)) = 0 := by
  rw [P.orbitAtom_eq_iInter]
  apply measure_frontier_finite_iInter_eq_zero
  intro j
  have hpres : MeasurePreserving f μ μ := ⟨hf.measurable, hinv⟩
  exact measure_frontier_preimage_eq_zero μ (hf.iterate j.val)
    (hpres.iterate j.val).map_eq (hboundary (w j))

theorem orbitEntropy_tendsto_of_weak_limit [HasOuterApproxClosed X] [Fintype κ]
    (P : FiniteMeasurablePartition X κ) {l : Filter ι}
    {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hlim : Tendsto μ l (𝓝 ν)) {f : X → X} (hf : Continuous f)
    (hinv : Measure.map f (ν : Measure X) = ν)
    (hboundary : ∀ k, (ν : Measure X) (frontier (P.atom k)) = 0) (n : ℕ) :
    Tendsto (fun i => P.orbitEntropy (μ i : Measure X) f n) l
      (𝓝 (P.orbitEntropy (ν : Measure X) f n)) :=
  finitePartitionEntropy_tendsto_of_weak_limit hlim (P.orbitAtom f n)
    (P.measure_frontier_orbitAtom_eq_zero _ hf hinv hboundary n)

theorem orbitEntropy_fixed_block_lower_of_long_blocks [HasOuterApproxClosed X] [Fintype κ]
    (P : FiniteMeasurablePartition X κ) {l : Filter ι} [l.NeBot]
    {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hlim : Tendsto μ l (𝓝 ν)) {f : X → X} (hf : Continuous f)
    (hμinv : ∀ i, Measure.map f (μ i : Measure X) = μ i)
    (hνinv : Measure.map f (ν : Measure X) = ν)
    (hboundary : ∀ k, (ν : Measure X) (frontier (P.atom k)) = 0)
    (N : ι → ℕ) (hN : Tendsto N l atTop) {a : ℝ}
    (hlower : ∀ᶠ i in l, a ≤ P.orbitEntropy (μ i : Measure X) f (N i) / N i)
    {k : ℕ} (hk : 0 < k) : a ≤ P.orbitEntropy (ν : Measure X) f k / k := by
  have hC : 0 ≤ Real.log (Fintype.card κ) := Real.log_natCast_nonneg _
  exact subadditive_fixed_block_lower_of_long_blocks
    (fun i => P.orbitEntropy (μ i : Measure X) f)
    (P.orbitEntropy (ν : Measure X) f) N
    (fun i => P.orbitEntropy_subadditive _ hf.measurable (hμinv i))
    (fun i => P.orbitEntropy_nonneg _ hf.measurable) hC
    (fun i => P.orbitEntropy_le_linear _ hf.measurable) hN
    (P.orbitEntropy_tendsto_of_weak_limit hlim hf hνinv hboundary) hlower hk

end FiniteMeasurablePartition

end Erdos1148.DukeArithmetic
