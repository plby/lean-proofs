import Mathlib.Topology.MetricSpace.Pseudo.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos426.UniqueSubgraphs.fSeq :
    Nat → Real
  := by
  sorry

theorem Erdos426.UniqueSubgraphs.f_tendsto_zero :
    @Filter.Tendsto.{0, 0} Nat Real Erdos426.UniqueSubgraphs.fSeq
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@nhds.{0} Real
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  := by
  sorry
