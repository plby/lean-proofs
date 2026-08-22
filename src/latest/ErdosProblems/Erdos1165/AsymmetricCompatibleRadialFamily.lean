/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.AsymmetricActualFarPairData
import ErdosProblems.Erdos1165.AsymmetricSplitLevelSplice

/-!
# Scanner-compatible asymmetric radial rows

This module is the direct two-stage adapter for the split-level splice.  A
retained code carries one literal complementary word and a dependent finite
family of erased `y` return words.  Those return words are restricted by the
checked `ScanCompatible` predicate at the separation level.  Fixed-word
cylinder factorization proves the atom mass exactly; the only analytic field
is a uniform upper bound on the product of the unrestricted return kernels.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricCompatibleRadialFamily

open AsymmetricActualFarPairData AsymmetricPairTwoStageMass
open AsymmetricSplitLevelSplice MarkedBridgeFactorization

noncomputable section

/-- Literal retained-code family for the post-separation `y` continuation.
The bridge predicate may depend on the complete retained code, so it can
record the incoming `x` scanner state at the problematic split level. -/
structure CompatibleRadialFamily
    (successful retained : Set StepPath) (radialTail : ℝ) : Type 2 where
  RetainedCode : Type
  retainedCode_countable : Countable RetainedCode
  coordinateCount : RetainedCode → ℕ
  Bridge : (r : RetainedCode) → Fin (coordinateCount r) → Type
  bridge_countable : ∀ r j, Countable (Bridge r j)
  atom : (r : RetainedCode) → ComplementarySkeletonAtom
    (coordinateCount r) Unit (Bridge r)
  admissible : (r : RetainedCode) → (j : Fin (coordinateCount r)) →
    Bridge r j → Prop
  successful_subset : successful ⊆ ⋃ r,
    (restrictBridges (atom r) (admissible r)).event
  retained_eq : retained = ⋃ r,
    stoppedWordCylinder ((atom r).complementWord Unit.unit)
  retained_prefixFree : PrefixFree fun r ↦
    (atom r).complementWord Unit.unit
  row_le : ∀ r,
    ∏ j, (restrictBridges (atom r) (admissible r)).kernel j ≤
      ENNReal.ofReal radialTail

attribute [instance] CompatibleRadialFamily.retainedCode_countable
attribute [instance] CompatibleRadialFamily.bridge_countable

def CompatibleRadialFamily.retainedAtom
    {successful retained : Set StepPath} {radialTail : ℝ}
    (family : CompatibleRadialFamily successful retained radialTail)
    (r : family.RetainedCode) : Set StepPath :=
  stoppedWordCylinder ((family.atom r).complementWord Unit.unit)

def CompatibleRadialFamily.tailAtom
    {successful retained : Set StepPath} {radialTail : ℝ}
    (family : CompatibleRadialFamily successful retained radialTail)
    (r : family.RetainedCode) (_ : Unit) : Set StepPath :=
  (restrictBridges (family.atom r) (family.admissible r)).event

def CompatibleRadialFamily.tailWeight
    {successful retained : Set StepPath} {radialTail : ℝ}
    (family : CompatibleRadialFamily successful retained radialTail)
    (r : family.RetainedCode) (_ : Unit) : ℝ≥0∞ :=
  ∏ j, (restrictBridges (family.atom r) (family.admissible r)).kernel j

theorem CompatibleRadialFamily.retainedAtom_measurable
    {successful retained : Set StepPath} {radialTail : ℝ}
    (family : CompatibleRadialFamily successful retained radialTail)
    (r : family.RetainedCode) :
    MeasurableSet (family.retainedAtom r) :=
  measurableSet_stoppedWordCylinder _

theorem CompatibleRadialFamily.retainedAtom_pairwise
    {successful retained : Set StepPath} {radialTail : ℝ}
    (family : CompatibleRadialFamily successful retained radialTail) :
    Pairwise fun r s : family.RetainedCode ↦
      Disjoint (family.retainedAtom r) (family.retainedAtom s) :=
  family.retained_prefixFree

/-- Exact fixed-retained-word factorization of every compatible row. -/
theorem CompatibleRadialFamily.tailAtom_mass
    {successful retained : Set StepPath} {radialTail : ℝ}
    (family : CompatibleRadialFamily successful retained radialTail)
    (r : family.RetainedCode) (u : Unit) :
    fairSteps (family.tailAtom r u) =
      family.tailWeight r u * fairSteps (family.retainedAtom r) := by
  rw [tailAtom, tailWeight, retainedAtom,
    fairSteps_restrictBridges, fairSteps_stoppedWordCylinder]
  unfold ComplementarySkeletonAtom.weight
  simp [mul_comm]

theorem CompatibleRadialFamily.successful_subset_doubleUnion
    {successful retained : Set StepPath} {radialTail : ℝ}
    (family : CompatibleRadialFamily successful retained radialTail) :
    successful ⊆ ⋃ r, ⋃ u : Unit, family.tailAtom r u := by
  intro omega homega
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (family.successful_subset homega)
  exact Set.mem_iUnion.mpr ⟨r,
    Set.mem_iUnion.mpr ⟨Unit.unit, hr⟩⟩

theorem CompatibleRadialFamily.tailWeight_tsum_le
    {successful retained : Set StepPath} {radialTail : ℝ}
    (family : CompatibleRadialFamily successful retained radialTail)
    (r : family.RetainedCode) :
    ∑' u : Unit, family.tailWeight r u ≤ ENNReal.ofReal radialTail := by
  simpa [tailWeight] using family.row_le r

/-- The frozen split-level compatible-word construction supplies the exact
two-stage successful-mass inequality consumed by
`ActualMarkedFarPairData`. -/
theorem CompatibleRadialFamily.successful_le
    {successful retained : Set StepPath} {radialTail : ℝ}
    (family : CompatibleRadialFamily successful retained radialTail)
    (hradial0 : 0 ≤ radialTail) :
    fairSteps.real successful ≤ radialTail * fairSteps.real retained := by
  exact fairSteps_real_le_radialTail_mul_retained_of_atom_weights
    (fun _ : family.RetainedCode ↦ Unit) successful retained
    family.retainedAtom family.tailAtom family.tailWeight radialTail hradial0
    family.successful_subset_doubleUnion family.retained_eq
    family.retainedAtom_measurable family.retainedAtom_pairwise
    family.tailAtom_mass family.tailWeight_tsum_le

end

end Erdos1165.AsymmetricCompatibleRadialFamily
