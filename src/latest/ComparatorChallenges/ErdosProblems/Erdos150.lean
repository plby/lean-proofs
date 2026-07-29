import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos150

open Finset Fintype Real SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsSeparator (G : SimpleGraph V) (u v : V) (T : Finset V) : Prop :=
  u ∉ T ∧ v ∉ T ∧ ∀ w : G.Walk u v, ∃ x ∈ w.support, x ∈ T

def IsMinSeparator (G : SimpleGraph V) (u v : V) (T : Finset V) : Prop :=
  IsSeparator G u v T ∧ ∀ T' : Finset V, T' ⊂ T → ¬IsSeparator G u v T'
section BradacFull

def IsMinCut (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ IsMinSeparator G u v T

def minCutSet (G : SimpleGraph V) : Set (Finset V) :=
  {T | IsMinCut G T}

noncomputable def numMinCuts (G : SimpleGraph V) : ℕ :=
  (minCutSet G).ncard

noncomputable def c (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), numMinCuts G = k}
end BradacFull

section LimitAndBound

open Filter Topology Real

end LimitAndBound

end Erdos150

attribute [local instance] Classical.propDecidable

theorem Erdos150.limit_alpha_exists_and_lt_two :
    @Exists.{1} Real fun (α : Real) ↦
      And
        (@Filter.Tendsto.{0, 0} Nat Real
          (fun (n : Nat) ↦
            @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast (Erdos150.c n))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@Nat.cast.{0} Real Real.instNatCast n)))
          (@Filter.atTop.{0} Nat Nat.instPreorder)
          (@nhds.{0} Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            α))
        (@LT.lt.{0} Real Real.instLT α
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
  := by
  sorry
