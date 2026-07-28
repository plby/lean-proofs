import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

attribute [local instance] Classical.propDecidable

theorem Erdos264b.main_theorem :
    @Exists.{1} (Nat → Nat) fun (b : Nat → Nat) ↦
      And
        (∀ (k : Nat),
          @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
            (@Insert.insert.{0, 0} Nat (Set.{0} Nat) (@Set.instInsert.{0} Nat)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Insert.insert.{0, 0} Nat (Set.{0} Nat) (@Set.instInsert.{0} Nat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Insert.insert.{0, 0} Nat (Set.{0} Nat) (@Set.instInsert.{0} Nat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Insert.insert.{0, 0} Nat (Set.{0} Nat) (@Set.instInsert.{0} Nat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Singleton.singleton.{0, 0} Nat (Set.{0} Nat) (@Set.instSingletonSet.{0} Nat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))))
            (b k))
        (@Exists.{1} Rat fun (q : Rat) ↦
          @Eq.{1} Real
            (@tsum.{0, 0} Real Nat Real.instAddCommMonoid
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (fun (k : Nat) ↦
                @HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat
                        (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Nat.cast.{0} Real Real.instNatCast
                      (b
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
              (SummationFilter.unconditional.{0} Nat))
            (@Rat.cast.{0} Real Real.instRatCast q))
  := by
  sorry

noncomputable def Erdos264b.IsIrrationalitySequence :
    (Nat → Nat) → Prop
  := by
  sorry

theorem Erdos264b.erdos_264.parts.i :
    Not
      (Erdos264b.IsIrrationalitySequence fun (x : Nat) ↦
        @HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x)
  := by
  sorry
