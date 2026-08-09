import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace Set

variable {α : Type*} {r : α → α → α → Prop} {s t : Set α} {x y z : α}

protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s →
    x ≠ y → y ≠ z → x ≠ z → r x y z
end Set

def NonTrilinear (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})
open EuclideanGeometry

namespace Erdos846

section Prelims

def NonTrilinearFor (A : Set ℝ²) (ε : ℝ) : Prop :=
  ∀ (B : Finset ℝ²), (B : Set ℝ²) ⊆ A → ∃ C ⊆ B,
    ε * B.card ≤ C.card ∧ NonTrilinear (C : Set ℝ²)

def WeaklyNonTrilinear (A : Set ℝ²) : Prop :=
  ∃ B : Finset (Set ℝ²), A = sSup B ∧ ∀ b ∈ B, NonTrilinear b
end Prelims

open MeasureTheory
open Polynomial
open scoped BigOperators
open scoped ENNReal
open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped intervalIntegral
open scoped List
open scoped Matrix
open scoped Nat
open scoped NNReal
open scoped Pointwise
open scoped ProbabilityTheory
open scoped Real
open scoped symmDiff
open scoped Topology

end Erdos846

attribute [local instance] Classical.propDecidable

theorem Erdos846.erdos_846 :
    Iff False
      (∀
        (A :
          Set.{0}
            (EuclideanSpace.{0, 0} Real
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (ε : Real),
        @GT.gt.{0} Real Real.instLT ε
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Set.Infinite.{0}
              (EuclideanSpace.{0, 0} Real
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              A →
            Erdos846.NonTrilinearFor A ε → Erdos846.WeaklyNonTrilinear A)
  := by
  sorry
