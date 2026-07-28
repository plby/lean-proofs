import Mathlib.Topology.MetricSpace.Pseudo.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos268.harmonicSubseriesSet :
    Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
  := by
  sorry

theorem Erdos268.harmonicSubseriesSet_interior_nonempty :
    @Set.Nonempty.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
      (@interior.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) ↦ Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) ↦
          @UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        Erdos268.harmonicSubseriesSet)
  := by
  sorry
