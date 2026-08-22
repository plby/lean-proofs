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

import ErdosProblems.Erdos1165.AnnularProfileMarkedSkeleton
import ErdosProblems.Erdos1165.MarkedSkeletonPartition

/-!
# Countable full-skeleton partitions for fixed Appendix-A profiles

This file constructs `ProfileMarkedStoppedDecomposition` from literal
singleton fibers of two countable codes.  The unmarked code retains the
complete complementary skeleton and both bridge endpoints.  The marked code
additionally retains a `ProfileGapChain`, so its source event already realizes
the prescribed negative-binomial profile.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularProfileMarkedPartition

noncomputable section

open AppendixFirstMoment ProfileGapChain AnnularProfileMarkedSkeleton
  MarkedSkeletonPartition

abbrev ProfileSkeletonIndex (Data Entrance Exit : Type*) :=
  Data × (Entrance × Exit)

abbrev MarkedProfileIndex (Data Entrance Exit : Type*) {n : ℕ}
    (m : Profile n) :=
  Data × (Entrance × (Exit × GapChain (profileList m)))

private theorem tsum_three
    {A B C : Type*} (f : A → B → C → ℝ≥0∞) :
    (∑' i : A × (B × C), f i.1 i.2.1 i.2.2) =
      ∑' a, ∑' b, ∑' c, f a b c := by
  calc
    (∑' i : A × (B × C), f i.1 i.2.1 i.2.2) =
        ∑' a, ∑' bc : B × C, f a bc.1 bc.2 :=
      ENNReal.tsum_prod
        (f := fun a (bc : B × C) ↦ f a bc.1 bc.2)
    _ = ∑' a, ∑' b, ∑' c, f a b c := by
      congr 1
      funext a
      exact ENNReal.tsum_prod

private theorem tsum_four
    {A B C D : Type*} (f : A → B → C → D → ℝ≥0∞) :
    (∑' i : A × (B × (C × D)), f i.1 i.2.1 i.2.2.1 i.2.2.2) =
      ∑' a, ∑' b, ∑' c, ∑' d, f a b c d := by
  calc
    (∑' i : A × (B × (C × D)), f i.1 i.2.1 i.2.2.1 i.2.2.2) =
        ∑' a, ∑' bcd : B × (C × D), f a bcd.1 bcd.2.1 bcd.2.2 :=
      ENNReal.tsum_prod
        (f := fun a (bcd : B × (C × D)) ↦
          f a bcd.1 bcd.2.1 bcd.2.2)
    _ = ∑' a, ∑' b, ∑' c, ∑' d, f a b c d := by
      congr 1
      funext a
      exact tsum_three (f a)

/-- Exact stopped-data decomposition from literal countable code fibers.
All disjointness and union identities are automatic.  The remaining mass
identities are the genuine strong-Markov factorization of each full skeleton
fiber. -/
theorem profileMarkedStoppedDecomposition_of_coding_fibers
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    [Countable Data] [Countable Entrance] [Countable Exit]
    {n : ℕ} (m : Profile n) (mu : Measure Omega)
    (successful terminalEvent markedSource : Set Omega)
    (skeletonWeight : Data → Entrance → Exit → ℝ≥0∞)
    (skeletonKernel : Entrance → Exit → ℝ≥0∞)
    (markedKernel : Entrance → GapChain (profileList m) → Exit → ℝ≥0∞)
    (skeletonCode : Omega → ProfileSkeletonIndex Data Entrance Exit)
    (markedCode : Omega → MarkedProfileIndex Data Entrance Exit m)
    (hsuccessful_measurable : MeasurableSet successful)
    (hmarkedSource_measurable : MeasurableSet markedSource)
    (hskeleton_fiber_measurable : ∀ i,
      MeasurableSet (skeletonCode ⁻¹' {i}))
    (hmarked_fiber_measurable : ∀ i,
      MeasurableSet (markedCode ⁻¹' {i}))
    (hmarked_path : markedSource ⊆ terminalEvent)
    (hskeleton_mass : ∀ data u z,
      mu (codingFiber successful skeletonCode (data, (u, z))) =
        skeletonWeight data u z * skeletonKernel u z)
    (hmarked_mass : ∀ data u z chain,
      mu (codingFiber markedSource markedCode (data, (u, (z, chain)))) =
        skeletonWeight data u z * markedKernel u chain z) :
    ProfileMarkedStoppedDecomposition m mu successful terminalEvent
      skeletonWeight skeletonKernel markedKernel := by
  classical
  constructor
  · rw [← iUnion_codingFiber successful skeletonCode,
      measure_iUnion (codingFiber_pairwise successful skeletonCode)]
    · simp_rw [hskeleton_mass]
      rw [successfulSkeletonMass]
      exact tsum_three fun data u z ↦
        skeletonWeight data u z * skeletonKernel u z
    · intro i
      exact codingFiber_measurable hsuccessful_measurable
        hskeleton_fiber_measurable i
  · have hmarkedMeasure :
        mu markedSource = markedProfileMass m skeletonWeight markedKernel := by
      rw [← iUnion_codingFiber markedSource markedCode,
        measure_iUnion (codingFiber_pairwise markedSource markedCode)]
      · simp_rw [hmarked_mass]
        rw [markedProfileMass]
        exact tsum_four fun data u z chain ↦
          skeletonWeight data u z * markedKernel u chain z
      · intro i
        exact codingFiber_measurable hmarkedSource_measurable
          hmarked_fiber_measurable i
    rw [← hmarkedMeasure]
    exact measure_mono hmarked_path

end

end Erdos1165.AnnularProfileMarkedPartition
