import Mathlib.Topology.MetricSpace.Pseudo.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos1000.cesaroPhi :
    (Nat → Nat) → Nat → Real
  := by
  sorry

theorem Erdos1000.erdos_1000_true :
    @Exists.{1} (Nat → Nat) fun (n : Nat → Nat) ↦
      And (@StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder n)
        (And
          (∀ (k : Nat),
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (n k))
          (@Filter.Tendsto.{0, 0} Nat Real (Erdos1000.cesaroPhi n)
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (@nhds.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))
  := by
  sorry
