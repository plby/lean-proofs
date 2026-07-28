import Mathlib.Topology.MetricSpace.Pseudo.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos419.u :
    Nat → Real
  := by
  sorry

noncomputable def Erdos419.S :
    Set.{0} Real
  := by
  sorry

theorem Erdos419.erdos_419 :
    @Eq.{1} (Set.{0} Real)
      (@setOf.{0} Real fun (x : Real) ↦
        @MapClusterPt.{0, 0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          Nat x (@Filter.atTop.{0} Nat Nat.instPreorder) Erdos419.u)
      Erdos419.S
  := by
  sorry
