import Mathlib

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


open EuclideanGeometry
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

namespace Erdos846

open scoped Classical in
theorem erdos_846 : (False) ↔ ∀ᵉ (A : Set ℝ²) (ε > 0),
    A.Infinite → NonTrilinearFor A ε → WeaklyNonTrilinear A := by
  sorry

end Erdos846
