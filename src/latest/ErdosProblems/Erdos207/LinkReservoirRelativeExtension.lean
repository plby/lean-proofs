/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkReservoirPointWeight
import ErdosProblems.Erdos207.RelativeExtensionMonotonicity

/-!
# Relative extension control for one link reservoir

The weighted joint-inclusion law of a Bernoulli link reservoir is fed into
the abstract relative-extension estimate.  The result is the precise extra
bad-event probability that can be added to the robust Hall union bound.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem independentBits_probability_linkReservoir_badExtension_le
    {A B V I : Type*} [Fintype A] [Fintype B] [Fintype V] [Fintype I]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (F : I → TripleSystemOn V) (P : TripleSystemOn V)
    (futureWeight : TripleOn V → ℝ≥0) (d : ℕ)
    (hcard : ∀ i, (F i \ P).card ≤ d)
    (kappa kappaOut : ℝ≥0)
    (hkappa : HasExtensionBound (fun i ↦ F i \ P)
      (fun T ↦ linkReservoirPointWeight center left right hcenterLeft
        hcenterRight hleftRight sampleProbability T + futureWeight T)
      kappa)
    (hkappaOut : 0 < kappaOut) :
    (FiniteLaw.independentBits (fun _ : A × B ↦ sampleProbability)
      (fun _ ↦ hprob)).probability (fun omega ↦
        ¬ HasExtensionBound
          (fun i ↦ (F i \ P) \
            linkReservoirTriangles center left right hcenterLeft
              hcenterRight hleftRight (FiniteLaw.selectedByBits omega))
          futureWeight kappaOut) ≤
      (configurationRoots (fun i ↦ F i \ P)).card *
        (kappa / kappaOut) := by
  let L := FiniteLaw.independentBits
    (fun _ : A × B ↦ sampleProbability) (fun _ ↦ hprob)
  let R : (A × B → Bool) → TripleSystemOn V := fun omega ↦
    linkReservoirTriangles center left right hcenterLeft hcenterRight
      hleftRight (FiniteLaw.selectedByBits omega)
  have hjoint : ∀ S : TripleSystemOn V, S.card ≤ d →
      L.probability (fun omega ↦ S ⊆ R omega) ≤
        (1 : ℝ≥0) * setWeight
          (linkReservoirPointWeight center left right hcenterLeft
            hcenterRight hleftRight sampleProbability) S := by
    intro S _hS
    simpa only [L, R, one_mul] using
      independentBits_probability_subset_linkReservoir_le_weight
        center left right hcenterLeft hcenterRight hleftRight
          sampleProbability hprob S
  simpa only [L, R, one_mul] using
    L.probability_not_relativeExtensionBound_le_of_joint R
      (fun i ↦ F i \ P)
      (linkReservoirPointWeight center left right hcenterLeft
        hcenterRight hleftRight sampleProbability)
      futureWeight 1 d hcard hjoint kappa kappaOut hkappa hkappaOut

/-- The same estimate when the available invariant is stated using a larger
point weight, for example the sum of all not-yet-processed center weights. -/
theorem independentBits_probability_linkReservoir_badExtension_le_of_weight
    {A B V I : Type*} [Fintype A] [Fintype B] [Fintype V] [Fintype I]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (F : I → TripleSystemOn V) (P : TripleSystemOn V)
    (futureWeight totalWeight : TripleOn V → ℝ≥0) (d : ℕ)
    (hcard : ∀ i, (F i \ P).card ≤ d)
    (hweight : ∀ T,
      linkReservoirPointWeight center left right hcenterLeft
          hcenterRight hleftRight sampleProbability T + futureWeight T ≤
        totalWeight T)
    (kappa kappaOut : ℝ≥0)
    (hkappa : HasExtensionBound (fun i ↦ F i \ P) totalWeight kappa)
    (hkappaOut : 0 < kappaOut) :
    (FiniteLaw.independentBits (fun _ : A × B ↦ sampleProbability)
      (fun _ ↦ hprob)).probability (fun omega ↦
        ¬ HasExtensionBound
          (fun i ↦ (F i \ P) \
            linkReservoirTriangles center left right hcenterLeft
              hcenterRight hleftRight (FiniteLaw.selectedByBits omega))
          futureWeight kappaOut) ≤
      (configurationRoots (fun i ↦ F i \ P)).card *
        (kappa / kappaOut) := by
  apply independentBits_probability_linkReservoir_badExtension_le
    center left right hcenterLeft hcenterRight hleftRight
      sampleProbability hprob F P futureWeight d hcard kappa kappaOut
  · exact hkappa.mono_weight hweight
  · exact hkappaOut

end

end Erdos207
