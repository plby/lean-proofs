import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

open Nat Finset Real Filter Asymptotics Topology
open scoped Pointwise

def Admissible (B : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (Finset.image (· % (p : ℤ)) B).card < p

axiom maynard_tao (m : ℕ) (hm : 2 ≤ m) (B : Finset ℤ)
    (hB : Admissible B) (hk : exp (8 * m + 4) < B.card * Real.log B.card) :
    ∀ N : ℕ, ∃ n : ℤ, N < n ∧
      m ≤ (B.filter (fun b ↦ (n + b).natAbs.Prime)).card
namespace BinQuadForm

end BinQuadForm

namespace Erdos237

open Nat Set Finset Real

noncomputable def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {a ∈ A | a ≤ n ∧ (n - a).Prime}
end Erdos237

attribute [local instance] Classical.propDecidable

theorem Erdos237.erdos_237 :
    ∀ (A : Set.{0} Nat),
      @Set.Infinite.{0} Nat A →
        ∀ (C : Nat), @Exists.{1} Nat fun (n : Nat) ↦ @LT.lt.{0} Nat instLTNat C (Erdos237.repCount A n)
  := by
  sorry
