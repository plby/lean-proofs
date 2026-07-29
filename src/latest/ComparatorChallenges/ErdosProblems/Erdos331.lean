import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos331

set_option linter.style.longLine false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Nat Filter
open scoped Asymptotics

set_option relaxedAutoImplicit false
set_option autoImplicit false

@[implicit_reducible] def erdos_331.match_1.{u} :
    (motive : ℕ × ℕ × ℕ × ℕ → Sort u) →
      (s : ℕ × ℕ × ℕ × ℕ) →
        ((a₁ a₂ b₁ b₂ : ℕ) → motive (a₁, a₂, b₁, b₂)) → motive s :=
  fun motive s h ↦
    Prod.casesOn s fun a₁ t ↦
      Prod.casesOn t fun a₂ t ↦
        Prod.casesOn t fun b₁ b₂ ↦ h a₁ a₂ b₁ b₂
end Erdos331

open Erdos331

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos331.main_theorem :
    @Exists.{1} (Set.{0} Nat) fun (A' : Set.{0} Nat) ↦
      @Exists.{1} (Set.{0} Nat) fun (B' : Set.{0} Nat) ↦
        And
          (∀ (x : Nat),
            @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A' x →
              @GT.gt.{0} Nat instLTNat x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (And
            (∀ (x : Nat),
              @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) B' x →
                @GT.gt.{0} Nat instLTNat x
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (And
              (@Exists.{1} Nat fun (N₀ : Nat) ↦
                ∀ (N : Nat),
                  @GE.ge.{0} Nat instLENat N N₀ →
                    And
                      (@GE.ge.{0} Real Real.instLE
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0} Nat
                            (@Finset.filter.{0} Nat
                              (fun (x : Nat) ↦
                                @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                                  A' x)
                              (fun (a : Nat) ↦
                                Classical.propDecidable
                                  (@Membership.mem.{0, 0} Nat (Set.{0} Nat)
                                    (@Set.instMembership.{0} Nat) A' a))
                              (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@OfNat.ofNat.{0} Real (nat_lit 4)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                          (@Nat.cast.{0} Real Real.instNatCast N).sqrt))
                      (@GE.ge.{0} Real Real.instLE
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0} Nat
                            (@Finset.filter.{0} Nat
                              (fun (x : Nat) ↦
                                @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                                  B' x)
                              (fun (a : Nat) ↦
                                Classical.propDecidable
                                  (@Membership.mem.{0, 0} Nat (Set.{0} Nat)
                                    (@Set.instMembership.{0} Nat) B' a))
                              (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@OfNat.ofNat.{0} Real (nat_lit 4)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                          (@Nat.cast.{0} Real Real.instNatCast N).sqrt)))
              (∀ (a₁ : Nat),
                @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A' a₁ →
                  ∀ (a₂ : Nat),
                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A' a₂ →
                      ∀ (b₁ : Nat),
                        @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) B' b₁ →
                          ∀ (b₂ : Nat),
                            @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) B'
                                b₂ →
                              @Ne.{1} Nat a₁ a₂ →
                                @Ne.{1} Int
                                  (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                                    (@Nat.cast.{0} Int instNatCastInt a₁)
                                    (@Nat.cast.{0} Int instNatCastInt a₂))
                                  (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                                    (@Nat.cast.{0} Int instNatCastInt b₁)
                                    (@Nat.cast.{0} Int instNatCastInt b₂)))))
  := by
  sorry
theorem Erdos331.erdos_331 :
    Not
      (∀ (A B : Set.{0} Nat),
        (@Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (fun (n : Nat) ↦
              @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                (@Nat.cast.{0} Real Real.instNatCast n)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
            fun (n : Nat) ↦
            @Nat.cast.{0} Real Real.instNatCast
              (@Nat.count A (fun (a : Nat) ↦ Classical.propDecidable (A a)) n)) →
          (@Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm
              (@Filter.atTop.{0} Nat Nat.instPreorder)
              (fun (n : Nat) ↦
                @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                  (@Nat.cast.{0} Real Real.instNatCast n)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
              fun (n : Nat) ↦
              @Nat.cast.{0} Real Real.instNatCast
                (@Nat.count B (fun (a : Nat) ↦ Classical.propDecidable (B a)) n)) →
            @Set.Infinite.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
              (@setOf.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
                fun (s : Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))) ↦
                Erdos331.erdos_331.match_1.{1}
                  (fun (s : Prod.{0, 0} Nat (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))) ↦ Prop) s
                  fun (a₁ a₂ b₁ b₂ : Nat) ↦
                  And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A a₁)
                    (And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) A a₂)
                      (And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) B b₁)
                        (And
                          (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) B b₂)
                          (And (@Ne.{1} Nat a₁ a₂)
                            (@Eq.{1} Nat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a₁ b₂)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a₂
                                b₁))))))))
  := by
  sorry
