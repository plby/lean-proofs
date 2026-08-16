import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos205

open Real Filter Asymptotics

def Omega (n : ℕ) : ℕ := n.primeFactorsList.length
noncomputable def pntRate (n : ℕ) : ℝ :=
  Real.sqrt (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))
def is_counterexample (c : ℝ) (n : ℕ) : Prop :=
  ∀ k, 2^k ≤ n → (Omega (n - 2^k) : ℝ) ≥ c * pntRate n
end Erdos205

attribute [local instance] Classical.propDecidable

theorem Erdos205.infinitely_many_counterexamples :
    @Exists.{1} Real fun (c : Real) ↦
      And
        (@LT.lt.{0} Real Real.instLT
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
        (@Set.Infinite.{0} Nat (@Set.ofPred.{0} Nat fun (n : Nat) ↦ Erdos205.is_counterexample c n))
  := by
  sorry
