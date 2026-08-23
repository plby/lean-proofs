/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

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

set_option maxHeartbeats 800000
noncomputable section

open scoped Classical in
def countIn (S : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range N).filter (· ∈ S) |>.card

open scoped Classical in
def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (countIn S N : ℝ) / N) Filter.atTop

open scoped Classical in
def HasNatDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N => (countIn S (N + 1) : ℝ) / (N + 1)) Filter.atTop (nhds d)

open scoped Classical in
structure BiPartition (A : Set ℕ) where
  left : Set ℕ
  right : Set ℕ
  disj : Disjoint left right
  cover : left ∪ right = A
end

end Erdos741b

open scoped Pointwise


namespace Erdos741b

end Erdos741b

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos741b

open scoped Classical in
theorem erdos741_upper_density (A : Set ℕ) (hA : upperDensity (A + A) > 0) :
    ∃ P : BiPartition A,
      upperDensity (P.left + P.left) > 0 ∧ upperDensity (P.right + P.right) > 0 := by
  sorry


open scoped Classical in
theorem erdos741_strict_density_counterexample :
    ∃ A : Set ℕ, HasNatDensity (A + A) 1 ∧
      ∀ P : BiPartition A, ¬(∃ d₁ > 0, ∃ d₂ > 0,
        HasNatDensity (P.left + P.left) d₁ ∧ HasNatDensity (P.right + P.right) d₂) := by
  sorry

end Erdos741b
