import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

attribute [local instance] Classical.propDecidable

universe u_1

noncomputable def Erdos42.SymmetricFinset :
    {α : Type u_1} → [Neg.{u_1} α] → Finset.{u_1} α → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos42.CliqueInCayley :
    {p : Nat} → Finset.{0} (ZMod p) → Finset.{0} (ZMod p) → Prop
  := by
  sorry

noncomputable def Erdos42.AvoidsNonzeroDiff :
    {α : Type u_1} →
      [DecidableEq.{u_1 + 1} α] →
        [Zero.{u_1} α] → [Sub.{u_1} α] → Finset.{u_1} α → Finset.{u_1} α → Prop
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos42.IsSidonInt :
    Finset.{0} Int → Prop
  := by
  sorry

noncomputable def Erdos42.FourierUpperIndicator :
    {p : Nat} →
      [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) p] →
        Finset.{0} (ZMod p) → Real → Prop
  := by
  sorry

theorem Erdos42.CompactCayley.compact_cayley_clique :
    ∀ (ℓ : Nat) (η : Real),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) ℓ →
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) η →
          @Exists.{1} Real fun (ε : Real) ↦
            And
              (@LT.lt.{0} Real Real.instLT
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
              (@Exists.{1} Nat fun (p₀ : Nat) ↦
                ∀ (p : Nat) [inst : Fact (Nat.Prime p)],
                  @LT.lt.{0} Nat instLTNat p₀ p →
                    ∀ (T : Finset.{0} (ZMod p)),
                      @Erdos42.SymmetricFinset.{0} (ZMod p)
                          (@NegZeroClass.toNeg.{0} (ZMod p)
                            (@SubNegZeroMonoid.toNegZeroClass.{0} (ZMod p)
                              (@SubtractionMonoid.toSubNegZeroMonoid.{0} (ZMod p)
                                (@SubtractionCommMonoid.toSubtractionMonoid.{0} (ZMod p)
                                  (@AddCommGroup.toDivisionAddCommMonoid.{0} (ZMod p)
                                    (@Ring.toAddCommGroup.{0} (ZMod p)
                                      (@DivisionRing.toRing.{0} (ZMod p)
                                        (@Field.toDivisionRing.{0} (ZMod p)
                                          (@ZMod.instField p inst)))))))))
                          T →
                        Not
                            (@Membership.mem.{0, 0} (ZMod p) (Finset.{0} (ZMod p))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (ZMod p)) (ZMod p)
                                (@Finset.instSetLike.{0} (ZMod p)))
                              T
                              (@OfNat.ofNat.{0} (ZMod p) (nat_lit 0)
                                (@Zero.toOfNat0.{0} (ZMod p)
                                  (@MulZeroClass.toZero.{0} (ZMod p)
                                    (@instMulZeroClassOfSemiring.{0} (ZMod p)
                                      (@DivisionSemiring.toSemiring.{0} (ZMod p)
                                        (@Semifield.toDivisionSemiring.{0} (ZMod p)
                                          (@Field.toSemifield.{0} (ZMod p)
                                            (@ZMod.instField p inst))))))))) →
                          @LE.le.{0} Real Real.instLE
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) η
                                (@Nat.cast.{0} Real Real.instNatCast p))
                              (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} (ZMod p) T)) →
                            @Erdos42.FourierUpperIndicator p
                                (@NeZero.of_gt'.{0} Nat p
                                  (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) Nat.instPreorder
                                  (@LinearOrderedCommMonoidWithZero.toIsBotZeroClass.{0} Nat
                                    Nat.instLinearOrderedCommMonoidWithZero)
                                  Nat.instOne (@Nat.Prime.one_lt' p inst))
                                T ε →
                              @Exists.{1} (Finset.{0} (ZMod p)) fun (C : Finset.{0} (ZMod p)) ↦
                                And (@Eq.{1} Nat (@Finset.card.{0} (ZMod p) C) ℓ)
                                  (@Erdos42.CliqueInCayley p T C))
  := by
  sorry

noncomputable def Erdos42.IsSidon :
    Set.{0} Nat → Prop
  := by
  sorry

theorem Erdos42.CompactCayley.theorem_1_1_from_compact_cayley :
    ∀ (M : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
        @Exists.{1} Nat fun (N₀ : Nat) ↦
          ∀ (N : Nat),
            @LE.le.{0} Nat instLENat N₀ N →
              ∀ (A : Finset.{0} Int),
                (∀ (a : Int),
                    @Membership.mem.{0, 0} Int (Finset.{0} Int)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int
                          (@Finset.instSetLike.{0} Int))
                        A a →
                      And
                        (@LE.le.{0} Int Int.instLEInt
                          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) a)
                        (@LE.le.{0} Int Int.instLEInt a (@Nat.cast.{0} Int instNatCastInt N))) →
                  Erdos42.IsSidonInt A →
                    @Finset.Nonempty.{0} Int A →
                      @Exists.{1} (Finset.{0} Int) fun (B : Finset.{0} Int) ↦
                        And
                          (∀ (b : Int),
                            @Membership.mem.{0, 0} Int (Finset.{0} Int)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Int) Int
                                  (@Finset.instSetLike.{0} Int))
                                B b →
                              And
                                (@LE.le.{0} Int Int.instLEInt
                                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) b)
                                (@LE.le.{0} Int Int.instLEInt b (@Nat.cast.{0} Int instNatCastInt N)))
                          (And (Erdos42.IsSidonInt B)
                            (And (@Eq.{1} Nat (@Finset.card.{0} Int B) M)
                              (@Erdos42.AvoidsNonzeroDiff.{0} Int Int.instDecidableEq
                                (@MulZeroClass.toZero.{0} Int
                                  (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
                                Int.instSub A B)))
  := by
  sorry

noncomputable def Erdos42.IsMaximalSidonSetIn :
    Set.{0} Nat → Nat → Prop
  := by
  sorry

theorem Erdos42.theorem_1_1_via_cayley :
    ∀ (M : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
        @Exists.{1} Nat fun (N₀ : Nat) ↦
          ∀ (N : Nat),
            @LE.le.{0} Nat instLENat N₀ N →
              ∀ (A : Set.{0} Nat),
                @LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat) A
                    (@Set.Icc.{0} Nat Nat.instPreorder
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N) →
                  Erdos42.IsSidon A →
                    @Set.Nonempty.{0} Nat A →
                      @Exists.{1} (Set.{0} Nat) fun (B : Set.{0} Nat) ↦
                        And
                          (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat) B
                            (@Set.Icc.{0} Nat Nat.instPreorder
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N))
                          (And (Erdos42.IsSidon B)
                            (And (@Eq.{1} Nat (@Set.ncard.{0} Nat B) M)
                              (@Eq.{1} (Set.{0} Nat)
                                (@Inter.inter.{0} (Set.{0} Nat) (@Set.instInter.{0} Nat)
                                  (@HSub.hSub.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                                    (@instHSub.{0} (Set.{0} Nat) (@Set.sub.{0} Nat instSubNat)) A A)
                                  (@HSub.hSub.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                                    (@instHSub.{0} (Set.{0} Nat) (@Set.sub.{0} Nat instSubNat)) B B))
                                (@Singleton.singleton.{0, 0} Nat (Set.{0} Nat)
                                  (@Set.instSingletonSet.{0} Nat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
  := by
  sorry

theorem Erdos42.erdos_42_via_cayley :
    Iff True
      (∀ (M : Nat),
        @GE.ge.{0} Nat instLENat M (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Filter.Eventually.{0} Nat
            (fun (N : Nat) ↦
              ∀ (A : Set.{0} Nat),
                Erdos42.IsMaximalSidonSetIn A N →
                  @Exists.{1} (Set.{0} Nat) fun (B : Set.{0} Nat) ↦
                    And
                      (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat) B
                        (@Set.Icc.{0} Nat Nat.instPreorder
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N))
                      (And (Erdos42.IsSidon B)
                        (And (@Eq.{1} Nat (@Set.ncard.{0} Nat B) M)
                          (@Eq.{1} (Set.{0} Nat)
                            (@Inter.inter.{0} (Set.{0} Nat) (@Set.instInter.{0} Nat)
                              (@HSub.hSub.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                                (@instHSub.{0} (Set.{0} Nat) (@Set.sub.{0} Nat instSubNat)) A A)
                              (@HSub.hSub.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                                (@instHSub.{0} (Set.{0} Nat) (@Set.sub.{0} Nat instSubNat)) B B))
                            (@Singleton.singleton.{0, 0} Nat (Set.{0} Nat)
                              (@Set.instSingletonSet.{0} Nat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@Filter.atTop.{0} Nat Nat.instPreorder))
  := by
  sorry

noncomputable def Erdos42.FormalConjecturesShape.erdos42RHS :
    Prop
  := by
  sorry

theorem Erdos42.FormalConjecturesShape.erdos_42_via_cayley :
    Iff True Erdos42.FormalConjecturesShape.erdos42RHS
  := by
  sorry
