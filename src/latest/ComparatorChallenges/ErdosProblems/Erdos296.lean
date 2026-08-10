import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos296

open Finset Filter

noncomputable section

def recipSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / n

def HasDisjointUnitDecomps (N k : ℕ) : Prop :=
  ∃ f : Fin k → Finset ℕ,
    (∀ i, f i ⊆ Icc 1 N) ∧
    (∀ i, recipSum (f i) = 1) ∧
    (∀ i j : Fin k, i ≠ j → Disjoint (f i) (f j))
end
end Erdos296

attribute [local instance] Classical.propDecidable

theorem Erdos296.erdos296 :
    @Exists.{1} Real fun (c : Real) ↦
      And
        (@GT.gt.{0} Real Real.instLT c
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (@Filter.Eventually.{0} Nat
          (fun (N : Nat) ↦
            Erdos296.HasDisjointUnitDecomps N
              (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c
                  (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))))
          (@Filter.atTop.{0} Nat Nat.instPreorder))
  := by
  sorry
