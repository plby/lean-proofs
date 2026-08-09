import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

attribute [local instance] Classical.propDecidable

theorem Erdos124b.erdos_124 :
    ∀ (k : Nat) (d : Fin k → Nat),
      (∀ (i : Fin k),
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (d i)) →
        @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@Finset.sum.{0, 0} (Fin k) Rat Rat.addCommMonoid (@Finset.univ.{0} (Fin k) (Fin.fintype k))
              fun (i : Fin k) ↦
              @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                  (@Nat.cast.{0} Rat Rat.instNatCast (d i))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) →
          ∀ (n : Nat),
            @Exists.{1} (Fin k → Nat) fun (a : Fin k → Nat) ↦
              ∀ (i : Fin k),
                And
                  (@LE.le.{0} (Finset.{0} Nat)
                    (@Preorder.toLE.{0} (Finset.{0} Nat)
                      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                        (@Finset.instPartialOrder.{0} Nat)))
                    (@List.toFinset.{0} Nat instDecidableEqNat ((d i).digits (a i)))
                    (@Insert.insert.{0, 0} Nat (Finset.{0} Nat)
                      (@Finset.instInsert.{0} Nat instDecidableEqNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@Eq.{1} Nat n
                    (@Finset.sum.{0, 0} (Fin k) Nat Nat.instAddCommMonoid
                      (@Finset.univ.{0} (Fin k) (Fin.fintype k)) fun (i : Fin k) ↦ a i))
  := by
  sorry

theorem Erdos124b.formal_conjectures_erdos_124_corrected :
    Iff
      (∀ (k : Nat) (d : Fin k → Nat),
        (∀ (i : Fin k),
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (d i)) →
          @StrictMono.{0, 0} (Fin k) Nat
              (@PartialOrder.toPreorder.{0} (Fin k) (@Fin.instPartialOrder k)) Nat.instPreorder d →
            @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                (@Finset.sum.{0, 0} (Fin k) Rat Rat.addCommMonoid
                  (@Finset.univ.{0} (Fin k) (Fin.fintype k)) fun (i : Fin k) ↦
                  @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                    (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                      (@Nat.cast.{0} Rat Rat.instNatCast (d i))
                      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) →
              @Filter.Eventually.{0} Nat
                (fun (n : Nat) ↦
                  @Exists.{1} (Fin k → Nat) fun (c : Fin k → Nat) ↦
                    @Exists.{1} (Fin k → Nat) fun (a : Fin k → Nat) ↦
                      ∀ (i : Fin k),
                        And
                          (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                              (@Finset.instSetLike.{0} Nat))
                            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat)
                              (@Finset.instInsert.{0} Nat instDecidableEqNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat)
                                (@Finset.instSingleton.{0} Nat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (c i))
                          (∀ (i : Fin k),
                            And
                              (@LE.le.{0} (Finset.{0} Nat)
                                (@Preorder.toLE.{0} (Finset.{0} Nat)
                                  (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                                    (@Finset.instPartialOrder.{0} Nat)))
                                (@List.toFinset.{0} Nat instDecidableEqNat ((d i).digits (a i)))
                                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat)
                                  (@Finset.instInsert.{0} Nat instDecidableEqNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat)
                                    (@Finset.instSingleton.{0} Nat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (@Eq.{1} Nat n
                                (@Finset.sum.{0, 0} (Fin k) Nat Nat.instAddCommMonoid
                                  (@Finset.univ.{0} (Fin k) (Fin.fintype k)) fun (i : Fin k) ↦
                                  @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (c i)
                                    (a i)))))
                (@Filter.atTop.{0} Nat Nat.instPreorder))
      (@Eq.{1} Bool Bool.true Bool.true)
  := by
  sorry
