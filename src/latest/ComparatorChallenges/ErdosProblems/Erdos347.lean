import Mathlib.Topology.MetricSpace.Pseudo.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos347.has_asymptotic_density_one :
    Set.{0} Nat → Prop
  := by
  sorry

noncomputable def Erdos347.subset_sums_of_set :
    Set.{0} Nat → Set.{0} Nat
  := by
  sorry

theorem Erdos347.answer_is_yes :
    @Exists.{1} (Nat → Nat) fun (A : Nat → Nat) ↦
      And (@Monotone.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder A)
        (And
          (@Filter.Tendsto.{0, 0} Nat Real
            (fun (n : Nat) ↦
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast
                  (A
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Nat.cast.{0} Real Real.instNatCast (A n)))
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (@nhds.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
          (∀ (S : Set.{0} Nat),
            And (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat) S (@Set.range.{0, 1} Nat Nat A))
                (@Set.Finite.{0} Nat
                  (@SDiff.sdiff.{0} (Set.{0} Nat) (@Set.instSDiff.{0} Nat) (@Set.range.{0, 1} Nat Nat A)
                    S)) →
              Erdos347.has_asymptotic_density_one (Erdos347.subset_sums_of_set S)))
  := by
  sorry
