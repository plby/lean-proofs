import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Erdos741b

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000
noncomputable section

def countIn (S : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range N).filter (· ∈ S) |>.card

def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (countIn S N : ℝ) / N) Filter.atTop

def HasNatDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N => (countIn S (N + 1) : ℝ) / (N + 1)) Filter.atTop (nhds d)

structure BiPartition (A : Set ℕ) where
  left : Set ℕ
  right : Set ℕ
  disj : Disjoint left right
  cover : left ∪ right = A
end

end Erdos741b

open scoped Pointwise

attribute [local instance] Classical.propDecidable

namespace Erdos741b

end Erdos741b

theorem Erdos741b.erdos741_upper_density :
    ∀ (A : Set.{0} Nat),
      @GT.gt.{0} Real Real.instLT
          (Erdos741b.upperDensity
            (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
              (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat)) A A))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Exists.{1} (Erdos741b.BiPartition A) fun (P : Erdos741b.BiPartition A) ↦
          And
            (@GT.gt.{0} Real Real.instLT
              (Erdos741b.upperDensity
                (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                  (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat))
                  (@Erdos741b.BiPartition.left A P) (@Erdos741b.BiPartition.left A P)))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
            (@GT.gt.{0} Real Real.instLT
              (Erdos741b.upperDensity
                (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                  (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat))
                  (@Erdos741b.BiPartition.right A P) (@Erdos741b.BiPartition.right A P)))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  := by
  sorry
theorem Erdos741b.erdos741_strict_density_counterexample :
    @Exists.{1} (Set.{0} Nat) fun (A : Set.{0} Nat) ↦
      And
        (Erdos741b.HasNatDensity
          (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
            (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat)) A A)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (∀ (P : Erdos741b.BiPartition A),
          Not
            (@Exists.{1} Real fun (d₁ : Real) ↦
              And
                (@GT.gt.{0} Real Real.instLT d₁
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                (@Exists.{1} Real fun (d₂ : Real) ↦
                  And
                    (@GT.gt.{0} Real Real.instLT d₂
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                    (And
                      (Erdos741b.HasNatDensity
                        (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                          (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat))
                          (@Erdos741b.BiPartition.left A P) (@Erdos741b.BiPartition.left A P))
                        d₁)
                      (Erdos741b.HasNatDensity
                        (@HAdd.hAdd.{0, 0, 0} (Set.{0} Nat) (Set.{0} Nat) (Set.{0} Nat)
                          (@instHAdd.{0} (Set.{0} Nat) (@Set.add.{0} Nat instAddNat))
                          (@Erdos741b.BiPartition.right A P) (@Erdos741b.BiPartition.right A P))
                        d₂)))))
  := by
  sorry
