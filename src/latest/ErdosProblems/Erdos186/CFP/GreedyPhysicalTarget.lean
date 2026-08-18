/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GreedyBookkeeping

/-!
# Greedy reserves at a prescribed physical subset-sum target

The random-color argument runs the greedy process independently in every
color.  The stopping level and the approximation rank may therefore vary
with the color.  What is common is the physical cardinality which every
selected reserve must reach.  This file packages that source-shaped first
crossing without introducing a common dyadic level or coordinate rank.
-/

namespace Erdos186.CFP.Greedy

noncomputable section

set_option autoImplicit false

/-- The first greedy step, bounded by `cap`, whose physical subset-sum set
has cardinality at least `target`. -/
def physicalTargetStep (S : Finset ℤ) (cap target : ℕ) : ℕ :=
  firstCrossing (fun j ↦ (sums S j).card) cap target

theorem physicalTargetStep_le (S : Finset ℤ) (cap target : ℕ) :
    physicalTargetStep S cap target ≤ cap := by
  exact firstCrossing_le (fun j ↦ (sums S j).card) cap target

/-- If the target is reached at the allowed endpoint, it is reached at the
canonical first crossing as well.  This includes the case in which the first
crossing is the endpoint itself. -/
theorem target_le_card_sums_physicalTargetStep
    {S : Finset ℤ} {cap target : ℕ}
    (hend : target ≤ (sums S cap).card) :
    target ≤ (sums S (physicalTargetStep S cap target)).card := by
  rcases firstCrossing_spec (fun j ↦ (sums S j).card) cap target with
      hcap | htarget
  · simpa only [physicalTargetStep, hcap] using hend
  · simpa only [physicalTargetStep] using htarget

/-- A target strictly above the initial singleton subset-sum set is reached
only after a positive number of greedy selections. -/
theorem physicalTargetStep_pos
    {S : Finset ℤ} {cap target : ℕ}
    (hend : target ≤ (sums S cap).card)
    (hinitial : (sums S 0).card < target) :
    0 < physicalTargetStep S cap target := by
  have htarget := target_le_card_sums_physicalTargetStep hend
  by_contra hnot
  have hzero : physicalTargetStep S cap target = 0 := by omega
  rw [hzero] at htarget
  omega

/-- All finite bookkeeping associated with a physical first crossing. -/
structure PhysicalTargetRun (S : Finset ℤ) (cap target : ℕ) where
  steps : ℕ
  steps_eq : steps = physicalTargetStep S cap target
  steps_le_cap : steps ≤ cap
  selected_subset : selected S steps ⊆ S
  selected_card : (selected S steps).card = steps
  target_le_subsetSums :
    target ≤ (subsetSums (selected S steps)).card

/-- Construct the canonical physical-target reserve.  The sole population
condition is that the permitted cap does not exceed the color size. -/
def physicalTargetRun
    (S : Finset ℤ) (cap target : ℕ)
    (hcap : cap ≤ S.card)
    (hend : target ≤ (sums S cap).card) :
    PhysicalTargetRun S cap target where
  steps := physicalTargetStep S cap target
  steps_eq := rfl
  steps_le_cap := physicalTargetStep_le S cap target
  selected_subset := selected_subset S _
  selected_card := card_selected_eq
    ((physicalTargetStep_le S cap target).trans hcap)
  target_le_subsetSums := by
    simpa only [sums] using target_le_card_sums_physicalTargetStep hend

namespace PhysicalTargetRun

variable {S : Finset ℤ} {cap target : ℕ}

theorem steps_le_card (R : PhysicalTargetRun S cap target)
    (hcap : cap ≤ S.card) :
    R.steps ≤ S.card :=
  R.steps_le_cap.trans hcap

theorem steps_pos (R : PhysicalTargetRun S cap target)
    (hend : target ≤ (sums S cap).card)
    (hinitial : (sums S 0).card < target) :
    0 < R.steps := by
  rw [R.steps_eq]
  exact physicalTargetStep_pos hend hinitial

end PhysicalTargetRun

end

end Erdos186.CFP.Greedy

#print axioms Erdos186.CFP.Greedy.target_le_card_sums_physicalTargetStep
#print axioms Erdos186.CFP.Greedy.physicalTargetRun
