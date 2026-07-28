import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Data.Nat.Prime.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos435.target :
    Nat → Int
  := by
  sorry

noncomputable def Erdos435.Representable :
    Nat → @AddSubmonoid.{0} Int (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid)
  := by
  sorry

theorem Erdos435.erdos_435 :
    ∀ (n : Nat),
      @Ne.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        (∀ (p k : Nat),
            Nat.Prime p →
              @Ne.{1} Nat n
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat
                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  p k)) →
          And
            (Not
              (@Membership.mem.{0, 0} Int
                (@AddSubmonoid.{0} Int (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
                (@SetLike.instMembership.{0, 0}
                  (@AddSubmonoid.{0} Int (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid)) Int
                  (@AddSubmonoid.instSetLike.{0} Int
                    (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid)))
                (Erdos435.Representable n) (Erdos435.target n)))
            (∀ (x : Int),
              @GT.gt.{0} Int Int.instLTInt x (Erdos435.target n) →
                @Membership.mem.{0, 0} Int
                  (@AddSubmonoid.{0} Int (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
                  (@SetLike.instMembership.{0, 0}
                    (@AddSubmonoid.{0} Int (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid)) Int
                    (@AddSubmonoid.instSetLike.{0} Int
                      (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid)))
                  (Erdos435.Representable n) x)
  := by
  sorry
