import Mathlib.Topology.MetricSpace.Pseudo.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Ramsey.ramseyNumber :
    Nat → Nat → Nat
  := by
  sorry

theorem Erdos1014.erdos1014 :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k →
        @Filter.Tendsto.{0, 0} Nat Real
          (fun (l : Nat) ↦
            @HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Nat.cast.{0} Real Real.instNatCast
                (Ramsey.ramseyNumber k
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Nat.cast.{0} Real Real.instNatCast (Ramsey.ramseyNumber k l)))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@nhds.{0} Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  := by
  sorry
