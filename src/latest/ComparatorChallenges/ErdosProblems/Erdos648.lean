import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos648

open Asymptotics Filter Nat Real

def P (n : ℕ) : ℕ := (n.primeFactors.max).getD 1
def is_valid_seq (n : ℕ) (l : List ℕ) : Prop :=
  l.IsChain (· < ·) ∧ (∀ m ∈ l, m ∈ Set.Ioc 0 n) ∧ (l.map P).IsChain (· > ·)
noncomputable def g (n : ℕ) : ℕ :=
  sSup { k | ∃ l, is_valid_seq n l ∧ l.length = k }
end Erdos648

attribute [local instance] Classical.propDecidable

theorem Erdos648.erdos_648 :
    @Asymptotics.IsTheta.{0, 0, 0} Nat Real Real Real.norm Real.norm
      (@Filter.atTop.{0} Nat Nat.instPreorder)
      (fun (n : Nat) ↦ @Nat.cast.{0} Real Real.instNatCast (Erdos648.g n)) fun (n : Nat) ↦
      (@HDiv.hDiv.{0, 0, 0} Real Real Real
          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast n)
          (Real.log (@Nat.cast.{0} Real Real.instNatCast n))).sqrt
  := by
  sorry
