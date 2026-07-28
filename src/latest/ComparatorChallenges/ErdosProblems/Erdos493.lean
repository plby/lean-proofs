import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

attribute [local instance] Classical.propDecidable

theorem Erdos493.erdos_493_aristotle :
    @Exists.{1} Nat fun (k : Nat) ↦
      @Exists.{1} Int fun (N : Int) ↦
        ∀ (n : Int),
          @LE.le.{0} Int Int.instLEInt N n →
            @Exists.{1} (Fin k → Int) fun (a : Fin k → Int) ↦
              And
                (∀ (i : Fin k),
                  @LE.le.{0} Int Int.instLEInt
                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) (a i))
                (@Eq.{1} Int
                  (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                    (@Finset.prod.{0, 0} (Fin k) Int Int.instCommMonoid
                      (@Finset.univ.{0} (Fin k) (Fin.fintype k)) fun (i : Fin k) ↦ a i)
                    (@Finset.sum.{0, 0} (Fin k) Int Int.instAddCommMonoid
                      (@Finset.univ.{0} (Fin k) (Fin.fintype k)) fun (i : Fin k) ↦ a i))
                  n)
  := by
  sorry
