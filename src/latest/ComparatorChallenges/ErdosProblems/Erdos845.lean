import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

attribute [local instance] Classical.propDecidable

universe u_1 u_2

noncomputable abbrev Erdos845.main_theorem_consequence.match_1 :
    (motive : Prod.{0, 0} Nat Nat → Sort u_1) →
      (x : Prod.{0, 0} Nat Nat) → ((k l : Nat) → motive (@Prod.mk.{0, 0} Nat Nat k l)) → motive x
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

noncomputable def Erdos845.HasDensity :
    {β : Type u_2} →
      [inst : Preorder.{u_2} β] →
        [@LocallyFiniteOrderBot.{u_2} β inst] →
          Set.{u_2} β → Real → optParam.{u_2 + 1} (Set.{u_2} β) (@Set.univ.{u_2} β) → Prop
  := by
  let _ := ULift.{u_2, 0} PUnit
  sorry

theorem Erdos845.erdos_845 :
    Iff (@Eq.{1} Bool Bool.false Bool.true)
      (∀ (C : Real),
        @LT.lt.{0} Real Real.instLT
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
          have f := fun (x : Prod.{0, 0} Nat Nat) ↦
            Erdos845.main_theorem_consequence.match_1.{1} (fun (x : Prod.{0, 0} Nat Nat) ↦ Nat) x
              fun (k l : Nat) ↦
              @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat
                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat
                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) l);
          @Erdos845.HasDensity.{0} Nat Nat.instPreorder
            (@LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat Nat.instPreorder
              Nat.instLocallyFiniteOrder Nat.instOrderBot)
            (@setOf.{0} Nat fun (x : Nat) ↦
              @Exists.{1} (Finset.{0} (Prod.{0, 0} Nat Nat))
                fun (B : Finset.{0} (Prod.{0, 0} Nat Nat)) ↦
                @Exists.{0} (@Finset.Nonempty.{0} (Prod.{0, 0} Nat Nat) B)
                  fun (h : @Finset.Nonempty.{0} (Prod.{0, 0} Nat Nat) B) ↦
                  @Exists.{0}
                    (@LE.le.{0} Real Real.instLE
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Finset.sup.{0, 0} Nat (Prod.{0, 0} Nat Nat)
                          (@Lattice.toSemilatticeSup.{0} Nat Nat.instLattice) Nat.instOrderBot B f))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.inf'.{0, 0} Nat (Prod.{0, 0} Nat Nat)
                            (@Lattice.toSemilatticeInf.{0} Nat Nat.instLattice) B h f))))
                    fun
                      (hB :
                        @LE.le.{0} Real Real.instLE
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@Finset.sup.{0, 0} Nat (Prod.{0, 0} Nat Nat)
                              (@Lattice.toSemilatticeSup.{0} Nat Nat.instLattice) Nat.instOrderBot B f))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                            (@Nat.cast.{0} Real Real.instNatCast
                              (@Finset.inf'.{0, 0} Nat (Prod.{0, 0} Nat Nat)
                                (@Lattice.toSemilatticeInf.{0} Nat Nat.instLattice) B h f)))) ↦
                    @Eq.{1} Nat
                      (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Nat Nat.instAddCommMonoid B
                        fun (x : Prod.{0, 0} Nat Nat) ↦ f x)
                      x)
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@Set.univ.{0} Nat))
  := by
  sorry

theorem Erdos845.van_doorn_everts_asymptotic_inexact :
    have f := fun (x : Prod.{0, 0} Nat Nat) ↦
      Erdos845.main_theorem_consequence.match_1.{1} (fun (x : Prod.{0, 0} Nat Nat) ↦ Nat) x
        fun (k l : Nat) ↦
        @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) l);
    @Exists.{1} Nat fun (C : Nat) ↦
      ∀ (n : Nat),
        @Exists.{1} (Finset.{0} (Prod.{0, 0} Nat Nat)) fun (B : Finset.{0} (Prod.{0, 0} Nat Nat)) ↦
          And
            (Not
              (@Exists.{1} (Prod.{0, 0} Nat Nat) fun (b : Prod.{0, 0} Nat Nat) ↦
                And
                  (@Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                      (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                    B b)
                  (@Exists.{1} (Prod.{0, 0} Nat Nat) fun (b' : Prod.{0, 0} Nat Nat) ↦
                    And
                      (@Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat))
                          (Prod.{0, 0} Nat Nat) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat Nat)))
                        B b')
                      (@GT.gt.{0} Nat instLTNat (f b')
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) C (f b))))))
            (@Eq.{1} Nat n
              (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Nat Nat.instAddCommMonoid B
                fun (x : Prod.{0, 0} Nat Nat) ↦ f x))
  := by
  sorry
