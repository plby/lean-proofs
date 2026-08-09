import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Order.Interval.Finset.Nat

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

namespace Erdos435

def generators (n : ℕ) : Set ℕ :=
  { m | ∃ i, 1 ≤ i ∧ i < n ∧ m = Nat.choose n i }
noncomputable def target (n : ℕ) : ℤ :=
  (Finset.sum n.factorization.support fun p =>
    (Finset.sum (Finset.Icc 1 (n.factorization p)) fun d =>
      (Nat.choose n (p ^ d) : ℤ)) * (p - 1)) - n
def generators_int (n : ℕ) : Set ℤ :=
  Int.ofNat '' (generators n)
def Representable (n : ℕ) : AddSubmonoid ℤ :=
  AddSubmonoid.closure (generators_int n)
end Erdos435

attribute [local instance] Classical.propDecidable

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
