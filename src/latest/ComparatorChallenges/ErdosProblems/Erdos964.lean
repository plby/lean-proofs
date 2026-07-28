import Mathlib.Topology.MetricSpace.Pseudo.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos964.divisor_ratios :
    Set.{0} Rat
  := by
  sorry

noncomputable def Erdos964.GoldstonGrahamPintzYildirimStatement :
    Prop
  := by
  sorry

theorem Erdos964.ErdosProblem964 :
    Erdos964.GoldstonGrahamPintzYildirimStatement →
      @LE.le.{0} (Set.{0} Real) (@Set.instLE.{0} Real)
        (@Set.Ioi.{0} Real Real.instPreorder
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (@closure.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@Set.image.{0, 0} Rat Real (fun (q : Rat) ↦ @Rat.cast.{0} Real Real.instRatCast q)
            Erdos964.divisor_ratios))
  := by
  sorry
