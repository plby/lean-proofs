import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos1100b

set_option linter.style.longLine false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

open Nat

noncomputable def tau_perp (n : ℕ) : ℕ :=
  let l := (divisors n).sort (· ≤ ·)
  (l.zip l.tail).countP (fun (a, b) => Nat.gcd a b = 1)
noncomputable def n_val_Ioc (x : ℝ) : ℕ :=
  ((Finset.Ioc (Nat.floor x) (Nat.floor (2 * x))).filter Nat.Prime).prod (fun p => p)
def PNT_statement : Prop :=
  Filter.Tendsto (fun x => Real.log (n_val_Ioc x) / x) Filter.atTop (nhds 1)
noncomputable def bound (n : ℕ) (ε : ℝ) : ℝ :=
  Real.exp ( (1 / 2 - ε) * (Real.log (Real.log n))^2 / Real.log (Real.log (Real.log n)) )
end Erdos1100b

attribute [local instance] Classical.propDecidable

theorem Erdos1100b.main_theorem :
    Erdos1100b.PNT_statement →
      ∀ (ε : Real),
        @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
            (@Set.Ioo.{0} Real Real.instPreorder
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
            ε →
          ∀ (N : Nat),
            @Exists.{1} Nat fun (n : Nat) ↦
              And (@GE.ge.{0} Nat instLENat n N)
                (@GT.gt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast (Erdos1100b.tau_perp n)) (Erdos1100b.bound n ε))
  := by
  sorry
