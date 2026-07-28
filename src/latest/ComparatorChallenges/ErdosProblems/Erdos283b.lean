import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Finset.Lattice.Fold

attribute [local instance] Classical.propDecidable

noncomputable def Erdos283b.sumPow :
    Finset.{0} Nat → Nat → Int
  := by
  sorry

noncomputable def Erdos283b.sumRecip :
    Finset.{0} Nat → Rat
  := by
  sorry

noncomputable def Erdos283b.sumF :
    Int → Int → Nat → Finset.{0} Nat → Int
  := by
  sorry

noncomputable def Erdos283b.n₀ :
    (Nat → Int) → Rat → WithTop.{0} Int
  := by
  sorry

noncomputable def Erdos283b.mFinset :
    Nat → Finset.{0} Nat → Finset.{0} Nat
  := by
  sorry

theorem Erdos283b.meta_theorem :
    ∀ (a : Int),
      @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) a →
        ∀ (b : Int) (d : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d →
            ∀ (m : Nat),
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
                @Eq.{1} Nat (a.gcd (@Nat.cast.{0} Int instNatCastInt m))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  ∀ (s : Nat),
                    @Dvd.dvd.{0} Int Int.instDvd a (@Nat.cast.{0} Int instNatCastInt s) →
                      ∀ (S : Set.{0} Rat) (Q : Finset.{0} Nat → Prop)
                        (getβ :
                          Rat →
                            Fin
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  m d) →
                              Rat)
                        (getA :
                          Rat →
                            Fin
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  m d) →
                              Finset.{0} Nat),
                        (∀ (α : Rat),
                            @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat) S α →
                              ∀
                                (i :
                                  Fin
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      m d))
                                (x : Nat),
                                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                      (@Finset.instSetLike.{0} Nat))
                                    (getA α i) x →
                                  @LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x) →
                          (∀ (α : Rat),
                              @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat) S
                                  α →
                                ∀
                                  (i :
                                    Fin
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        m d)),
                                  @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat)
                                    S (getβ α i)) →
                            (∀ (α : Rat),
                                @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat) S
                                    α →
                                  ∀
                                    (i :
                                      Fin
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat
                                              (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          m d)),
                                    @Eq.{1} Int
                                      (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
                                        (Erdos283b.sumPow (getA α i) d)
                                        (@HPow.hPow.{0, 0, 0} Int Nat Int
                                          (@instHPow.{0, 0} Int Nat
                                            (@NPow.toPow.{0} Int
                                              (@Monoid.toNPow.{0} Int Int.instMonoid)))
                                          (@Nat.cast.{0} Int instNatCastInt m) d))
                                      (@Nat.cast.{0} Int instNatCastInt
                                        (@Fin.val
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat
                                                (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            m d)
                                          i))) →
                              (∀ (α : Rat),
                                  @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat)
                                      S α →
                                    ∀
                                      (i :
                                        Fin
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat
                                                (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            m d)),
                                      @Eq.{1} Nat (@Finset.card.{0} Nat (getA α i)) s) →
                                (∀ (α : Rat),
                                    @Membership.mem.{0, 0} Rat (Set.{0} Rat)
                                        (@Set.instMembership.{0} Rat) S α →
                                      ∀
                                        (i :
                                          Fin
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat
                                                  (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              m d)),
                                        @Eq.{1} Rat α
                                          (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat
                                            (@instHAdd.{0} Rat Rat.instAdd)
                                            (Erdos283b.sumRecip (getA α i))
                                            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat
                                              (@instHDiv.{0} Rat Rat.instDiv) (getβ α i)
                                              (@Nat.cast.{0} Rat Rat.instNatCast m)))) →
                                  (∀ (α : Rat),
                                      @Membership.mem.{0, 0} Rat (Set.{0} Rat)
                                          (@Set.instMembership.{0} Rat) S α →
                                        ∀
                                          (i :
                                            Fin
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat
                                                    (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                m d))
                                          (B : Finset.{0} Nat),
                                          Q B →
                                            @Disjoint.{0} (Finset.{0} Nat)
                                              (@Finset.instPartialOrder.{0} Nat)
                                              (@Finset.instOrderBot.{0} Nat) (getA α i)
                                              (Erdos283b.mFinset m B)) →
                                    (∀ (α : Rat),
                                        @Membership.mem.{0, 0} Rat (Set.{0} Rat)
                                            (@Set.instMembership.{0} Rat) S α →
                                          ∀
                                            (i :
                                              Fin
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat
                                                      (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  m d))
                                            (B : Finset.{0} Nat),
                                            Q B →
                                              Q
                                                (@Union.union.{0} (Finset.{0} Nat)
                                                  (@Finset.instUnion.{0} Nat instDecidableEqNat)
                                                  (getA α i) (Erdos283b.mFinset m B))) →
                                      ∀ (L : Int),
                                        (∀ (α : Rat),
                                            @Membership.mem.{0, 0} Rat (Set.{0} Rat)
                                                (@Set.instMembership.{0} Rat) S α →
                                              ∀
                                                (i :
                                                  Fin
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat
                                                          (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      m d)),
                                                @LE.le.{0} Int Int.instLEInt L
                                                  (Erdos283b.sumPow (getA α i) d)) →
                                          ∀ (M : Int),
                                            (∀ (α : Rat),
                                                @Membership.mem.{0, 0} Rat (Set.{0} Rat)
                                                    (@Set.instMembership.{0} Rat) S α →
                                                  ∀
                                                    (i :
                                                      Fin
                                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                          (@instHPow.{0, 0} Nat Nat
                                                            (@NPow.toPow.{0} Nat
                                                              (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                          m d)),
                                                    @LE.le.{0} Int Int.instLEInt
                                                      (Erdos283b.sumPow (getA α i) d) M) →
                                              ∀ (T : Int),
                                                @LE.le.{0} Int Int.instLEInt
                                                    (@HSub.hSub.{0, 0, 0} Int Int Int
                                                      (@instHSub.{0} Int Int.instSub)
                                                      (@Int.ceil.{0} Rat
                                                        (@DivisionRing.toRing.{0} Rat
                                                          Rat.instDivisionRing)
                                                        Rat.linearOrder Rat.instFloorRing
                                                        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat
                                                          (@instHDiv.{0} Rat Rat.instDiv)
                                                          (@HMul.hMul.{0, 0, 0} Rat Rat Rat
                                                            (@instHMul.{0} Rat Rat.instMul)
                                                            (@Int.cast.{0} Rat Rat.instIntCast a)
                                                            (@HSub.hSub.{0, 0, 0} Rat Rat Rat
                                                              (@instHSub.{0} Rat Rat.instSub)
                                                              (@Int.cast.{0} Rat Rat.instIntCast M)
                                                              (@Int.cast.{0} Rat Rat.instIntCast L)))
                                                          (@HSub.hSub.{0, 0, 0} Rat Rat Rat
                                                            (@instHSub.{0} Rat Rat.instSub)
                                                            (@HPow.hPow.{0, 0, 0} Rat Nat Rat
                                                              (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                                                              (@Nat.cast.{0} Rat Rat.instNatCast m) d)
                                                            (@OfNat.ofNat.{0} Rat (nat_lit 1)
                                                              (@Rat.instOfNat (nat_lit 1))))))
                                                      (@OfNat.ofNat.{0} Int (nat_lit 1)
                                                        (@instOfNat (nat_lit 1))))
                                                    T →
                                                  ∀ (r : Nat) (X : Int),
                                                    @LE.le.{0} Int Int.instLEInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 0)
                                                          (@instOfNat (nat_lit 0)))
                                                        X →
                                                      @LE.le.{0} Int Int.instLEInt
                                                          (@OfNat.ofNat.{0} Int (nat_lit 0)
                                                            (@instOfNat (nat_lit 0)))
                                                          (@HAdd.hAdd.{0, 0, 0} Int Int Int
                                                            (@instHAdd.{0} Int Int.instAdd)
                                                            (@HSub.hSub.{0, 0, 0} Int Int Int
                                                              (@instHSub.{0} Int Int.instSub)
                                                              (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                (@instHMul.{0} Int Int.instMul)
                                                                (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                  (@instHMul.{0} Int Int.instMul) b
                                                                  (@Nat.cast.{0} Int instNatCastInt r))
                                                                (@HSub.hSub.{0, 0, 0} Int Int Int
                                                                  (@instHSub.{0} Int Int.instSub)
                                                                  (@HPow.hPow.{0, 0, 0} Int Nat Int
                                                                    (@instHPow.{0, 0} Int Nat
                                                                      (@NPow.toPow.{0} Int
                                                                        (@Monoid.toNPow.{0} Int
                                                                          Int.instMonoid)))
                                                                    (@Nat.cast.{0} Int instNatCastInt m)
                                                                    d)
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 1)
                                                                    (@instOfNat (nat_lit 1)))))
                                                              (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                (@instHMul.{0} Int Int.instMul) b
                                                                (@Nat.cast.{0} Int instNatCastInt s)))
                                                            (@HMul.hMul.{0, 0, 0} Int Int Int
                                                              (@instHMul.{0} Int Int.instMul) a
                                                              (@HSub.hSub.{0, 0, 0} Int Int Int
                                                                (@instHSub.{0} Int Int.instSub) M L))) →
                                                        @LE.le.{0} Int Int.instLEInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 0)
                                                              (@instOfNat (nat_lit 0)))
                                                            (@HAdd.hAdd.{0, 0, 0} Int Int Int
                                                              (@instHAdd.{0} Int Int.instAdd)
                                                              (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                (@instHMul.{0} Int Int.instMul)
                                                                (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                  (@instHMul.{0} Int Int.instMul) b
                                                                  (@Nat.cast.{0} Int instNatCastInt s))
                                                                (@HSub.hSub.{0, 0, 0} Int Int Int
                                                                  (@instHSub.{0} Int Int.instSub)
                                                                  (@HPow.hPow.{0, 0, 0} Int Nat Int
                                                                    (@instHPow.{0, 0} Int Nat
                                                                      (@NPow.toPow.{0} Int
                                                                        (@Monoid.toNPow.{0} Int
                                                                          Int.instMonoid)))
                                                                    (@Nat.cast.{0} Int instNatCastInt m)
                                                                    d)
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 1)
                                                                    (@instOfNat (nat_lit 1)))))
                                                              (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                (@instHMul.{0} Int Int.instMul) a
                                                                (@HSub.hSub.{0, 0, 0} Int Int Int
                                                                  (@instHSub.{0} Int Int.instSub) M
                                                                  L))) →
                                                          (∀ (α : Rat),
                                                              @Membership.mem.{0, 0} Rat (Set.{0} Rat)
                                                                  (@Set.instMembership.{0} Rat) S α →
                                                                ∀ (n : Int),
                                                                  @LE.le.{0} Int Int.instLEInt
                                                                      (@HSub.hSub.{0, 0, 0} Int Int Int
                                                                        (@instHSub.{0} Int Int.instSub)
                                                                        X T)
                                                                      n →
                                                                    @LE.le.{0} Int Int.instLEInt n
                                                                        (@HAdd.hAdd.{0, 0, 0} Int Int
                                                                          Int
                                                                          (@instHAdd.{0} Int
                                                                            Int.instAdd)
                                                                          (@HAdd.hAdd.{0, 0, 0} Int Int
                                                                            Int
                                                                            (@instHAdd.{0} Int
                                                                              Int.instAdd)
                                                                            (@HMul.hMul.{0, 0, 0} Int
                                                                              Int Int
                                                                              (@instHMul.{0} Int
                                                                                Int.instMul)
                                                                              (@HPow.hPow.{0, 0, 0} Int
                                                                                Nat Int
                                                                                (@instHPow.{0, 0} Int
                                                                                  Nat
                                                                                  (@NPow.toPow.{0} Int
                                                                                    (@Monoid.toNPow.{0}
                                                                                      Int
                                                                                      Int.instMonoid)))
                                                                                (@Nat.cast.{0} Int
                                                                                  instNatCastInt m)
                                                                                d)
                                                                              X)
                                                                            (@HMul.hMul.{0, 0, 0} Int
                                                                              Int Int
                                                                              (@instHMul.{0} Int
                                                                                Int.instMul)
                                                                              a M))
                                                                          T) →
                                                                      @Dvd.dvd.{0} Int Int.instDvd a
                                                                          (@HSub.hSub.{0, 0, 0} Int Int
                                                                            Int
                                                                            (@instHSub.{0} Int
                                                                              Int.instSub)
                                                                            n
                                                                            (@HMul.hMul.{0, 0, 0} Int
                                                                              Int Int
                                                                              (@instHMul.{0} Int
                                                                                Int.instMul)
                                                                              b
                                                                              (@Nat.cast.{0} Int
                                                                                instNatCastInt r))) →
                                                                        @Exists.{1} (Finset.{0} Nat)
                                                                          fun (A : Finset.{0} Nat) ↦
                                                                          And (Q A)
                                                                            (And
                                                                              (∀ (x : Nat),
                                                                                @Membership.mem.{0, 0}
                                                                                    Nat (Finset.{0} Nat)
                                                                                    (@SetLike.instMembership.{0,
                                                                                          0}
                                                                                      (Finset.{0} Nat)
                                                                                      Nat
                                                                                      (@Finset.instSetLike.{0}
                                                                                        Nat))
                                                                                    A x →
                                                                                  @LT.lt.{0} Nat
                                                                                    instLTNat
                                                                                    (@OfNat.ofNat.{0}
                                                                                      Nat (nat_lit 0)
                                                                                      (instOfNatNat
                                                                                        (nat_lit 0)))
                                                                                    x)
                                                                              (And
                                                                                (@Eq.{1} Nat
                                                                                  (@Finset.card.{0} Nat
                                                                                    A)
                                                                                  r)
                                                                                (And
                                                                                  (@Eq.{1} Int
                                                                                    (Erdos283b.sumF a b
                                                                                      d A)
                                                                                    n)
                                                                                  (@Eq.{1} Rat
                                                                                    (Erdos283b.sumRecip
                                                                                      A)
                                                                                    α))))) →
                                                            ∀ (α : Rat),
                                                              @Membership.mem.{0, 0} Rat (Set.{0} Rat)
                                                                  (@Set.instMembership.{0} Rat) S α →
                                                                ∀ (n : Int),
                                                                  @LE.le.{0} Int Int.instLEInt
                                                                      (@HSub.hSub.{0, 0, 0} Int Int Int
                                                                        (@instHSub.{0} Int Int.instSub)
                                                                        X T)
                                                                      n →
                                                                    @Dvd.dvd.{0} Int Int.instDvd a
                                                                        (@HSub.hSub.{0, 0, 0} Int Int
                                                                          Int
                                                                          (@instHSub.{0} Int
                                                                            Int.instSub)
                                                                          n
                                                                          (@HMul.hMul.{0, 0, 0} Int Int
                                                                            Int
                                                                            (@instHMul.{0} Int
                                                                              Int.instMul)
                                                                            b
                                                                            (@Nat.cast.{0} Int
                                                                              instNatCastInt r))) →
                                                                      @Exists.{1} (Finset.{0} Nat)
                                                                        fun (A : Finset.{0} Nat) ↦
                                                                        And (Q A)
                                                                          (And
                                                                            (∀ (x : Nat),
                                                                              @Membership.mem.{0, 0} Nat
                                                                                  (Finset.{0} Nat)
                                                                                  (@SetLike.instMembership.{0,
                                                                                        0}
                                                                                    (Finset.{0} Nat) Nat
                                                                                    (@Finset.instSetLike.{0}
                                                                                      Nat))
                                                                                  A x →
                                                                                @LT.lt.{0} Nat instLTNat
                                                                                  (@OfNat.ofNat.{0} Nat
                                                                                    (nat_lit 0)
                                                                                    (instOfNatNat
                                                                                      (nat_lit 0)))
                                                                                  x)
                                                                            (And
                                                                              (@Eq.{1} Int
                                                                                (Erdos283b.sumF a b d A)
                                                                                n)
                                                                              (@Eq.{1} Rat
                                                                                (Erdos283b.sumRecip A)
                                                                                α)))
  := by
  sorry

theorem Erdos283b.general_theorem :
    ∀ (a : Int)
      (ha : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) a)
      (b : Int) (d : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d →
        ∀ (m : Nat),
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
            @Eq.{1} Nat (a.gcd (@Nat.cast.{0} Int instNatCastInt m))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              ∀ (s : Nat),
                @Dvd.dvd.{0} Int Int.instDvd a (@Nat.cast.{0} Int instNatCastInt s) →
                  ∀ (S : Set.{0} Rat) (Q : Finset.{0} Nat → Prop)
                    (getβ :
                      Rat →
                        Fin
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat
                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                              m d) →
                          Rat)
                    (getA :
                      Rat →
                        Fin
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat
                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                              m d) →
                          Finset.{0} Nat),
                    (∀ (α : Rat),
                        @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat) S α →
                          ∀
                            (i :
                              Fin
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  m d))
                            (x : Nat),
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat
                                  (@Finset.instSetLike.{0} Nat))
                                (getA α i) x →
                              @LT.lt.{0} Nat instLTNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x) →
                      (∀ (α : Rat),
                          @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat) S α →
                            ∀
                              (i :
                                Fin
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    m d)),
                              @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat) S
                                (getβ α i)) →
                        (∀ (α : Rat),
                            @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat) S α →
                              ∀
                                (i :
                                  Fin
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      m d)),
                                @Eq.{1} Int
                                  (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
                                    (Erdos283b.sumPow (getA α i) d)
                                    (@HPow.hPow.{0, 0, 0} Int Nat Int
                                      (@instHPow.{0, 0} Int Nat
                                        (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                                      (@Nat.cast.{0} Int instNatCastInt m) d))
                                  (@Nat.cast.{0} Int instNatCastInt
                                    (@Fin.val
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        m d)
                                      i))) →
                          (∀ (α : Rat),
                              @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat) S
                                  α →
                                ∀
                                  (i :
                                    Fin
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        m d)),
                                  @Eq.{1} Nat (@Finset.card.{0} Nat (getA α i)) s) →
                            (∀ (α : Rat),
                                @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat) S
                                    α →
                                  ∀
                                    (i :
                                      Fin
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat
                                              (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          m d)),
                                    @Eq.{1} Rat α
                                      (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
                                        (Erdos283b.sumRecip (getA α i))
                                        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat
                                          (@instHDiv.{0} Rat Rat.instDiv) (getβ α i)
                                          (@Nat.cast.{0} Rat Rat.instNatCast m)))) →
                              (∀ (α : Rat),
                                  @Membership.mem.{0, 0} Rat (Set.{0} Rat) (@Set.instMembership.{0} Rat)
                                      S α →
                                    ∀
                                      (i :
                                        Fin
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat
                                                (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            m d))
                                      (B : Finset.{0} Nat),
                                      Q B →
                                        @Disjoint.{0} (Finset.{0} Nat)
                                          (@Finset.instPartialOrder.{0} Nat)
                                          (@Finset.instOrderBot.{0} Nat) (getA α i)
                                          (Erdos283b.mFinset m B)) →
                                (∀ (α : Rat),
                                    @Membership.mem.{0, 0} Rat (Set.{0} Rat)
                                        (@Set.instMembership.{0} Rat) S α →
                                      ∀
                                        (i :
                                          Fin
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat
                                                  (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              m d))
                                        (B : Finset.{0} Nat),
                                        Q B →
                                          Q
                                            (@Union.union.{0} (Finset.{0} Nat)
                                              (@Finset.instUnion.{0} Nat instDecidableEqNat) (getA α i)
                                              (Erdos283b.mFinset m B))) →
                                  ∀ (L : Int),
                                    (∀ (α : Rat),
                                        @Membership.mem.{0, 0} Rat (Set.{0} Rat)
                                            (@Set.instMembership.{0} Rat) S α →
                                          ∀
                                            (i :
                                              Fin
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat
                                                      (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  m d)),
                                            @LE.le.{0} Int Int.instLEInt L
                                              (Erdos283b.sumPow (getA α i) d)) →
                                      ∀ (M : Int),
                                        (∀ (α : Rat),
                                            @Membership.mem.{0, 0} Rat (Set.{0} Rat)
                                                (@Set.instMembership.{0} Rat) S α →
                                              ∀
                                                (i :
                                                  Fin
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat
                                                          (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      m d)),
                                                @LE.le.{0} Int Int.instLEInt
                                                  (Erdos283b.sumPow (getA α i) d) M) →
                                          ∀ (T : Int),
                                            @LE.le.{0} Int Int.instLEInt
                                                (@HSub.hSub.{0, 0, 0} Int Int Int
                                                  (@instHSub.{0} Int Int.instSub)
                                                  (@Int.ceil.{0} Rat
                                                    (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
                                                    Rat.linearOrder Rat.instFloorRing
                                                    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat
                                                      (@instHDiv.{0} Rat Rat.instDiv)
                                                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat
                                                        (@instHMul.{0} Rat Rat.instMul)
                                                        (@Int.cast.{0} Rat Rat.instIntCast a)
                                                        (@HSub.hSub.{0, 0, 0} Rat Rat Rat
                                                          (@instHSub.{0} Rat Rat.instSub)
                                                          (@Int.cast.{0} Rat Rat.instIntCast M)
                                                          (@Int.cast.{0} Rat Rat.instIntCast L)))
                                                      (@HSub.hSub.{0, 0, 0} Rat Rat Rat
                                                        (@instHSub.{0} Rat Rat.instSub)
                                                        (@HPow.hPow.{0, 0, 0} Rat Nat Rat
                                                          (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
                                                          (@Nat.cast.{0} Rat Rat.instNatCast m) d)
                                                        (@OfNat.ofNat.{0} Rat (nat_lit 1)
                                                          (@Rat.instOfNat (nat_lit 1))))))
                                                  (@OfNat.ofNat.{0} Int (nat_lit 1)
                                                    (@instOfNat (nat_lit 1))))
                                                T →
                                              ∀ (l₁ l₂ : Int),
                                                @LE.le.{0} Int Int.instLEInt l₁
                                                    (@OfNat.ofNat.{0} Int (nat_lit 0)
                                                      (@instOfNat (nat_lit 0))) →
                                                  @LE.le.{0} Int Int.instLEInt
                                                      (@OfNat.ofNat.{0} Int (nat_lit 0)
                                                        (@instOfNat (nat_lit 0)))
                                                      l₂ →
                                                    ∀ (r_w : Fin a.natAbs → Nat),
                                                      (∀ (w : Fin a.natAbs),
                                                          @Dvd.dvd.{0} Int Int.instDvd a
                                                            (@HSub.hSub.{0, 0, 0} Int Int Int
                                                              (@instHSub.{0} Int Int.instSub)
                                                              (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                (@instHMul.{0} Int Int.instMul) b
                                                                (@Nat.cast.{0} Int instNatCastInt
                                                                  (r_w w)))
                                                              (@Nat.cast.{0} Int instNatCastInt
                                                                (@Fin.val a.natAbs w)))) →
                                                        ∀ (X_w : Fin a.natAbs → Int),
                                                          (∀ (w : Fin a.natAbs),
                                                              @LE.le.{0} Int Int.instLEInt
                                                                (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                  (@instHMul.{0} Int Int.instMul)
                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                    l₁.natAbs)
                                                                  (@Nat.cast.{0} Int instNatCastInt
                                                                    (r_w w)))
                                                                (X_w w)) →
                                                            (∀ (w : Fin a.natAbs),
                                                                @LE.le.{0} Int Int.instLEInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 0)
                                                                    (@instOfNat (nat_lit 0)))
                                                                  (@HAdd.hAdd.{0, 0, 0} Int Int Int
                                                                    (@instHAdd.{0} Int Int.instAdd)
                                                                    (@HSub.hSub.{0, 0, 0} Int Int Int
                                                                      (@instHSub.{0} Int Int.instSub)
                                                                      (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                        (@instHMul.{0} Int Int.instMul)
                                                                        (@HMul.hMul.{0, 0, 0} Int Int
                                                                          Int
                                                                          (@instHMul.{0} Int
                                                                            Int.instMul)
                                                                          (@HAdd.hAdd.{0, 0, 0} Int Int
                                                                            Int
                                                                            (@instHAdd.{0} Int
                                                                              Int.instAdd)
                                                                            b l₁)
                                                                          (@Nat.cast.{0} Int
                                                                            instNatCastInt (r_w w)))
                                                                        (@HSub.hSub.{0, 0, 0} Int Int
                                                                          Int
                                                                          (@instHSub.{0} Int
                                                                            Int.instSub)
                                                                          (@HPow.hPow.{0, 0, 0} Int Nat
                                                                            Int
                                                                            (@instHPow.{0, 0} Int Nat
                                                                              (@NPow.toPow.{0} Int
                                                                                (@Monoid.toNPow.{0} Int
                                                                                  Int.instMonoid)))
                                                                            (@Nat.cast.{0} Int
                                                                              instNatCastInt m)
                                                                            d)
                                                                          (@OfNat.ofNat.{0} Int
                                                                            (nat_lit 1)
                                                                            (@instOfNat (nat_lit 1)))))
                                                                      (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                        (@instHMul.{0} Int Int.instMul)
                                                                        (@HAdd.hAdd.{0, 0, 0} Int Int
                                                                          Int
                                                                          (@instHAdd.{0} Int
                                                                            Int.instAdd)
                                                                          b l₁)
                                                                        (@Nat.cast.{0} Int
                                                                          instNatCastInt s)))
                                                                    (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                      (@instHMul.{0} Int Int.instMul) a
                                                                      (@HSub.hSub.{0, 0, 0} Int Int Int
                                                                        (@instHSub.{0} Int Int.instSub)
                                                                        M L)))) →
                                                              (∀ (w : Fin a.natAbs),
                                                                  @LE.le.{0} Int Int.instLEInt
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 0)
                                                                      (@instOfNat (nat_lit 0)))
                                                                    (@HAdd.hAdd.{0, 0, 0} Int Int Int
                                                                      (@instHAdd.{0} Int Int.instAdd)
                                                                      (@HSub.hSub.{0, 0, 0} Int Int Int
                                                                        (@instHSub.{0} Int Int.instSub)
                                                                        (@HMul.hMul.{0, 0, 0} Int Int
                                                                          Int
                                                                          (@instHMul.{0} Int
                                                                            Int.instMul)
                                                                          (@HMul.hMul.{0, 0, 0} Int Int
                                                                            Int
                                                                            (@instHMul.{0} Int
                                                                              Int.instMul)
                                                                            (@HAdd.hAdd.{0, 0, 0} Int
                                                                              Int Int
                                                                              (@instHAdd.{0} Int
                                                                                Int.instAdd)
                                                                              b l₂)
                                                                            (@Nat.cast.{0} Int
                                                                              instNatCastInt (r_w w)))
                                                                          (@HSub.hSub.{0, 0, 0} Int Int
                                                                            Int
                                                                            (@instHSub.{0} Int
                                                                              Int.instSub)
                                                                            (@HPow.hPow.{0, 0, 0} Int
                                                                              Nat Int
                                                                              (@instHPow.{0, 0} Int Nat
                                                                                (@NPow.toPow.{0} Int
                                                                                  (@Monoid.toNPow.{0}
                                                                                    Int
                                                                                    Int.instMonoid)))
                                                                              (@Nat.cast.{0} Int
                                                                                instNatCastInt m)
                                                                              d)
                                                                            (@OfNat.ofNat.{0} Int
                                                                              (nat_lit 1)
                                                                              (@instOfNat
                                                                                (nat_lit 1)))))
                                                                        (@HMul.hMul.{0, 0, 0} Int Int
                                                                          Int
                                                                          (@instHMul.{0} Int
                                                                            Int.instMul)
                                                                          (@HAdd.hAdd.{0, 0, 0} Int Int
                                                                            Int
                                                                            (@instHAdd.{0} Int
                                                                              Int.instAdd)
                                                                            b l₂)
                                                                          (@Nat.cast.{0} Int
                                                                            instNatCastInt s)))
                                                                      (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                        (@instHMul.{0} Int Int.instMul)
                                                                        a
                                                                        (@HSub.hSub.{0, 0, 0} Int Int
                                                                          Int
                                                                          (@instHSub.{0} Int
                                                                            Int.instSub)
                                                                          M L)))) →
                                                                @LE.le.{0} Int Int.instLEInt
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 0)
                                                                      (@instOfNat (nat_lit 0)))
                                                                    (@HAdd.hAdd.{0, 0, 0} Int Int Int
                                                                      (@instHAdd.{0} Int Int.instAdd)
                                                                      (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                        (@instHMul.{0} Int Int.instMul)
                                                                        (@HMul.hMul.{0, 0, 0} Int Int
                                                                          Int
                                                                          (@instHMul.{0} Int
                                                                            Int.instMul)
                                                                          (@HAdd.hAdd.{0, 0, 0} Int Int
                                                                            Int
                                                                            (@instHAdd.{0} Int
                                                                              Int.instAdd)
                                                                            b l₁)
                                                                          (@Nat.cast.{0} Int
                                                                            instNatCastInt s))
                                                                        (@HSub.hSub.{0, 0, 0} Int Int
                                                                          Int
                                                                          (@instHSub.{0} Int
                                                                            Int.instSub)
                                                                          (@HPow.hPow.{0, 0, 0} Int Nat
                                                                            Int
                                                                            (@instHPow.{0, 0} Int Nat
                                                                              (@NPow.toPow.{0} Int
                                                                                (@Monoid.toNPow.{0} Int
                                                                                  Int.instMonoid)))
                                                                            (@Nat.cast.{0} Int
                                                                              instNatCastInt m)
                                                                            d)
                                                                          (@OfNat.ofNat.{0} Int
                                                                            (nat_lit 1)
                                                                            (@instOfNat (nat_lit 1)))))
                                                                      (@HMul.hMul.{0, 0, 0} Int Int Int
                                                                        (@instHMul.{0} Int Int.instMul)
                                                                        a
                                                                        (@HSub.hSub.{0, 0, 0} Int Int
                                                                          Int
                                                                          (@instHSub.{0} Int
                                                                            Int.instSub)
                                                                          M L))) →
                                                                  (∀ (w : Fin a.natAbs) (α : Rat),
                                                                      @Membership.mem.{0, 0} Rat
                                                                          (Set.{0} Rat)
                                                                          (@Set.instMembership.{0} Rat)
                                                                          S α →
                                                                        ∀ (n : Int),
                                                                          @LE.le.{0} Int Int.instLEInt
                                                                              (@HSub.hSub.{0, 0, 0} Int
                                                                                Int Int
                                                                                (@instHSub.{0} Int
                                                                                  Int.instSub)
                                                                                (@HAdd.hAdd.{0, 0, 0}
                                                                                  Int Int Int
                                                                                  (@instHAdd.{0} Int
                                                                                    Int.instAdd)
                                                                                  (X_w w)
                                                                                  (@HMul.hMul.{0, 0, 0}
                                                                                    Int Int Int
                                                                                    (@instHMul.{0} Int
                                                                                      Int.instMul)
                                                                                    l₁
                                                                                    (@Nat.cast.{0} Int
                                                                                      instNatCastInt
                                                                                      (r_w w))))
                                                                                T)
                                                                              n →
                                                                            @LE.le.{0} Int Int.instLEInt
                                                                                n
                                                                                (@HAdd.hAdd.{0, 0, 0}
                                                                                  Int Int Int
                                                                                  (@instHAdd.{0} Int
                                                                                    Int.instAdd)
                                                                                  (@HAdd.hAdd.{0, 0, 0}
                                                                                    Int Int Int
                                                                                    (@instHAdd.{0} Int
                                                                                      Int.instAdd)
                                                                                    (@HMul.hMul.{0, 0,
                                                                                          0}
                                                                                      Int Int Int
                                                                                      (@instHMul.{0} Int
                                                                                        Int.instMul)
                                                                                      (@HPow.hPow.{0, 0,
                                                                                            0}
                                                                                        Int Nat Int
                                                                                        (@instHPow.{0,
                                                                                              0}
                                                                                          Int Nat
                                                                                          (@NPow.toPow.{0}
                                                                                            Int
                                                                                            (@Monoid.toNPow.{0}
                                                                                              Int
                                                                                              Int.instMonoid)))
                                                                                        (@Nat.cast.{0}
                                                                                          Int
                                                                                          instNatCastInt
                                                                                          m)
                                                                                        d)
                                                                                      (@HAdd.hAdd.{0, 0,
                                                                                            0}
                                                                                        Int Int Int
                                                                                        (@instHAdd.{0}
                                                                                          Int
                                                                                          Int.instAdd)
                                                                                        (X_w w)
                                                                                        (@HMul.hMul.{0,
                                                                                              0, 0}
                                                                                          Int Int Int
                                                                                          (@instHMul.{0}
                                                                                            Int
                                                                                            Int.instMul)
                                                                                          l₂
                                                                                          (@Nat.cast.{0}
                                                                                            Int
                                                                                            instNatCastInt
                                                                                            (r_w w)))))
                                                                                    (@HMul.hMul.{0, 0,
                                                                                          0}
                                                                                      Int Int Int
                                                                                      (@instHMul.{0} Int
                                                                                        Int.instMul)
                                                                                      a M))
                                                                                  T) →
                                                                              @Dvd.dvd.{0} Int
                                                                                  Int.instDvd a
                                                                                  (@HSub.hSub.{0, 0, 0}
                                                                                    Int Int Int
                                                                                    (@instHSub.{0} Int
                                                                                      Int.instSub)
                                                                                    n
                                                                                    (@Nat.cast.{0} Int
                                                                                      instNatCastInt
                                                                                      (@Fin.val a.natAbs
                                                                                        w))) →
                                                                                @Exists.{1}
                                                                                  (Finset.{0} Nat)
                                                                                  fun
                                                                                    (A :
                                                                                      Finset.{0} Nat) ↦
                                                                                  And (Q A)
                                                                                    (And
                                                                                      (∀ (x : Nat),
                                                                                        @Membership.mem.{0,
                                                                                                0}
                                                                                            Nat
                                                                                            (Finset.{0}
                                                                                              Nat)
                                                                                            (@SetLike.instMembership.{0,
                                                                                                  0}
                                                                                              (Finset.{0}
                                                                                                Nat)
                                                                                              Nat
                                                                                              (@Finset.instSetLike.{0}
                                                                                                Nat))
                                                                                            A x →
                                                                                          @LT.lt.{0} Nat
                                                                                            instLTNat
                                                                                            (@OfNat.ofNat.{0}
                                                                                              Nat
                                                                                              (nat_lit
                                                                                                0)
                                                                                              (instOfNatNat
                                                                                                (nat_lit
                                                                                                  0)))
                                                                                            x)
                                                                                      (And
                                                                                        (@Eq.{1} Nat
                                                                                          (@Finset.card.{0}
                                                                                            Nat A)
                                                                                          (r_w w))
                                                                                        (And
                                                                                          (@Eq.{1} Int
                                                                                            (Erdos283b.sumF
                                                                                              a b d A)
                                                                                            n)
                                                                                          (@Eq.{1} Rat
                                                                                            (Erdos283b.sumRecip
                                                                                              A)
                                                                                            α))))) →
                                                                    ∀ (j : Int),
                                                                      @LE.le.{0} Int Int.instLEInt l₁
                                                                          j →
                                                                        @LE.le.{0} Int Int.instLEInt j
                                                                            l₂ →
                                                                          @Eq.{1} Nat
                                                                              ((@HAdd.hAdd.{0, 0, 0} Int
                                                                                    Int Int
                                                                                    (@instHAdd.{0} Int
                                                                                      Int.instAdd)
                                                                                    b j).gcd
                                                                                a)
                                                                              (@OfNat.ofNat.{0} Nat
                                                                                (nat_lit 1)
                                                                                (instOfNatNat
                                                                                  (nat_lit 1))) →
                                                                            ∀ (α : Rat),
                                                                              @Membership.mem.{0, 0} Rat
                                                                                  (Set.{0} Rat)
                                                                                  (@Set.instMembership.{0}
                                                                                    Rat)
                                                                                  S α →
                                                                                @LE.le.{0}
                                                                                  (WithTop.{0} Int)
                                                                                  (@Preorder.toLE.{0}
                                                                                    (WithTop.{0} Int)
                                                                                    (@WithTop.instPreorder.{0}
                                                                                      Int
                                                                                      (@PartialOrder.toPreorder.{0}
                                                                                        Int
                                                                                        (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0}
                                                                                          Int
                                                                                          (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
                                                                                            Int
                                                                                            (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
                                                                                              Int
                                                                                              (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0}
                                                                                                Int
                                                                                                Int.instConditionallyCompleteLinearOrder)))))))
                                                                                  (Erdos283b.n₀
                                                                                    (fun (x : Nat) ↦
                                                                                      @HAdd.hAdd.{0, 0,
                                                                                            0}
                                                                                        Int Int Int
                                                                                        (@instHAdd.{0}
                                                                                          Int
                                                                                          Int.instAdd)
                                                                                        (@HMul.hMul.{0,
                                                                                              0, 0}
                                                                                          Int Int Int
                                                                                          (@instHMul.{0}
                                                                                            Int
                                                                                            Int.instMul)
                                                                                          a
                                                                                          (@HPow.hPow.{0,
                                                                                                0, 0}
                                                                                            Int Nat Int
                                                                                            (@instHPow.{0,
                                                                                                  0}
                                                                                              Int Nat
                                                                                              (@NPow.toPow.{0}
                                                                                                Int
                                                                                                (@Monoid.toNPow.{0}
                                                                                                  Int
                                                                                                  Int.instMonoid)))
                                                                                            (@Nat.cast.{0}
                                                                                              Int
                                                                                              instNatCastInt
                                                                                              x)
                                                                                            d))
                                                                                        (@HAdd.hAdd.{0,
                                                                                              0, 0}
                                                                                          Int Int Int
                                                                                          (@instHAdd.{0}
                                                                                            Int
                                                                                            Int.instAdd)
                                                                                          b j))
                                                                                    α)
                                                                                  (@WithTop.some.{0} Int
                                                                                    (@Finset.sup'.{0, 0}
                                                                                      Int (Fin a.natAbs)
                                                                                      (@Lattice.toSemilatticeSup.{0}
                                                                                        Int
                                                                                        instLatticeInt)
                                                                                      (@Finset.univ.{0}
                                                                                        (Fin a.natAbs)
                                                                                        (Fin.fintype
                                                                                          a.natAbs))
                                                                                      (@Exists.intro.{1}
                                                                                        (Fin a.natAbs)
                                                                                        (fun
                                                                                            (x :
                                                                                              Fin
                                                                                                a.natAbs) ↦
                                                                                          @Membership.mem.{0,
                                                                                                0}
                                                                                            (Fin
                                                                                              a.natAbs)
                                                                                            (Finset.{0}
                                                                                              (Fin
                                                                                                a.natAbs))
                                                                                            (@SetLike.instMembership.{0,
                                                                                                  0}
                                                                                              (Finset.{0}
                                                                                                (Fin
                                                                                                  a.natAbs))
                                                                                              (Fin
                                                                                                a.natAbs)
                                                                                              (@Finset.instSetLike.{0}
                                                                                                (Fin
                                                                                                  a.natAbs)))
                                                                                            (@Finset.univ.{0}
                                                                                              (Fin
                                                                                                a.natAbs)
                                                                                              (Fin.fintype
                                                                                                a.natAbs))
                                                                                            x)
                                                                                        (@Fin.mk
                                                                                          a.natAbs
                                                                                          (@OfNat.ofNat.{0}
                                                                                            Nat
                                                                                            (nat_lit 0)
                                                                                            (instOfNatNat
                                                                                              (nat_lit
                                                                                                0)))
                                                                                          (@Iff.mpr
                                                                                            (@LT.lt.{0}
                                                                                              Nat
                                                                                              instLTNat
                                                                                              (@OfNat.ofNat.{0}
                                                                                                Nat
                                                                                                (nat_lit
                                                                                                  0)
                                                                                                (instOfNatNat
                                                                                                  (nat_lit
                                                                                                    0)))
                                                                                              a.natAbs)
                                                                                            (@Ne.{1} Int
                                                                                              a
                                                                                              (@OfNat.ofNat.{0}
                                                                                                Int
                                                                                                (nat_lit
                                                                                                  0)
                                                                                                (@instOfNat
                                                                                                  (nat_lit
                                                                                                    0))))
                                                                                            (@Int.natAbs_pos
                                                                                              a)
                                                                                            (@LT.lt.ne'.{0}
                                                                                              Int
                                                                                              (@PartialOrder.toPreorder.{0}
                                                                                                Int
                                                                                                (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0}
                                                                                                  Int
                                                                                                  (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
                                                                                                    Int
                                                                                                    (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
                                                                                                      Int
                                                                                                      (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0}
                                                                                                        Int
                                                                                                        Int.instConditionallyCompleteLinearOrder)))))
                                                                                              a
                                                                                              (@OfNat.ofNat.{0}
                                                                                                Int
                                                                                                (nat_lit
                                                                                                  0)
                                                                                                (@instOfNat
                                                                                                  (nat_lit
                                                                                                    0)))
                                                                                              ha)))
                                                                                        (@Finset.mem_univ.{0}
                                                                                          (Fin a.natAbs)
                                                                                          (Fin.fintype
                                                                                            a.natAbs)
                                                                                          (@Fin.mk
                                                                                            a.natAbs
                                                                                            (@OfNat.ofNat.{0}
                                                                                              Nat
                                                                                              (nat_lit
                                                                                                0)
                                                                                              (instOfNatNat
                                                                                                (nat_lit
                                                                                                  0)))
                                                                                            (@Iff.mpr
                                                                                              (@LT.lt.{0}
                                                                                                Nat
                                                                                                instLTNat
                                                                                                (@OfNat.ofNat.{0}
                                                                                                  Nat
                                                                                                  (nat_lit
                                                                                                    0)
                                                                                                  (instOfNatNat
                                                                                                    (nat_lit
                                                                                                      0)))
                                                                                                a.natAbs)
                                                                                              (@Ne.{1}
                                                                                                Int a
                                                                                                (@OfNat.ofNat.{0}
                                                                                                  Int
                                                                                                  (nat_lit
                                                                                                    0)
                                                                                                  (@instOfNat
                                                                                                    (nat_lit
                                                                                                      0))))
                                                                                              (@Int.natAbs_pos
                                                                                                a)
                                                                                              (@LT.lt.ne'.{0}
                                                                                                Int
                                                                                                (@PartialOrder.toPreorder.{0}
                                                                                                  Int
                                                                                                  (@ConditionallyCompletePartialOrderSup.toPartialOrder.{0}
                                                                                                    Int
                                                                                                    (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{0}
                                                                                                      Int
                                                                                                      (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{0}
                                                                                                        Int
                                                                                                        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0}
                                                                                                          Int
                                                                                                          Int.instConditionallyCompleteLinearOrder)))))
                                                                                                a
                                                                                                (@OfNat.ofNat.{0}
                                                                                                  Int
                                                                                                  (nat_lit
                                                                                                    0)
                                                                                                  (@instOfNat
                                                                                                    (nat_lit
                                                                                                      0)))
                                                                                                ha)))))
                                                                                      fun
                                                                                        (w :
                                                                                          Fin
                                                                                            a.natAbs) ↦
                                                                                      @HSub.hSub.{0, 0,
                                                                                            0}
                                                                                        Int Int Int
                                                                                        (@instHSub.{0}
                                                                                          Int
                                                                                          Int.instSub)
                                                                                        (@HAdd.hAdd.{0,
                                                                                              0, 0}
                                                                                          Int Int Int
                                                                                          (@instHAdd.{0}
                                                                                            Int
                                                                                            Int.instAdd)
                                                                                          (X_w w)
                                                                                          (@HMul.hMul.{0,
                                                                                                0, 0}
                                                                                            Int Int Int
                                                                                            (@instHMul.{0}
                                                                                              Int
                                                                                              Int.instMul)
                                                                                            j
                                                                                            (@Nat.cast.{0}
                                                                                              Int
                                                                                              instNatCastInt
                                                                                              (r_w w))))
                                                                                        T))
  := by
  sorry
