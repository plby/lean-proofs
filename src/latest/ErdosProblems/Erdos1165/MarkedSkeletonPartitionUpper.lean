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

import ErdosProblems.Erdos1165.AppendixPairMoment
import ErdosProblems.Erdos1165.MarkedSkeletonPartition

/-!
# Upper stopped-data decomposition from complete marked skeleton atoms

This is the upper analogue of `MarkedSkeletonPartition`'s lower constructor.
The successful event is still an exact disjoint union of complete unmarked
skeleton atoms.  For an upper bound, however, the literal pair event is
required to be contained in the union of the selected marked atoms.

All future and profile information remains in the skeleton atom and its
weight.  In particular this construction does not condition the pair event
at an early inner-entrance clock.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.MarkedSkeletonPartitionUpper

open MarkedSkeletonPartition MarkedTerminalDisintegration

noncomputable section

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
        ∑' a, ∑' bcd : B × (C × D),
          f a bcd.1 bcd.2.1 bcd.2.2 :=
      ENNReal.tsum_prod
        (f := fun a (bcd : B × (C × D)) ↦
          f a bcd.1 bcd.2.1 bcd.2.2)
    _ = ∑' a, ∑' b, ∑' c, ∑' d, f a b c d := by
      congr 1
      funext a
      exact tsum_three (f a)

/-- A complete measurable atom partition constructs the one-sided upper
stopped-data decomposition used for the far-pair estimate. -/
theorem markedStoppedDataUpperDecomposition_of_atom_partition
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    [Countable Data] [Countable Entrance] [Countable Exit]
    {m : ℕ} (mu : Measure Omega) (pairEvent successful : Set Omega)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (skeletonAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → Set Omega)
    (markedAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → (Fin m → ℕ) → Set Omega)
    (hskeleton_measurable : ∀ data entrance exit,
      MeasurableSet (skeletonAtom data entrance exit))
    (hmarked_measurable : ∀ data entrance exit visits,
      MeasurableSet (markedAtom data entrance exit visits))
    (hskeleton_disjoint : Pairwise fun
      i j : SkeletonIndex Data Entrance Exit m ↦
        Disjoint (indexedSkeletonAtom skeletonAtom i)
          (indexedSkeletonAtom skeletonAtom j))
    (hmarked_disjoint : Pairwise fun
      i j : MarkedIndex Data Entrance Exit m ↦
        Disjoint (indexedMarkedAtom markedAtom i)
          (indexedMarkedAtom markedAtom j))
    (hsuccessful : successful =
      ⋃ i : SkeletonIndex Data Entrance Exit m,
        indexedSkeletonAtom skeletonAtom i)
    (hpair_union : pairEvent ⊆
      ⋃ i : MarkedIndex Data Entrance Exit m,
        restrictedMarkedAtom visitEvent markedAtom i)
    (hskeleton_mass : ∀ data entrance exit,
      mu (skeletonAtom data entrance exit) =
        skeletonWeight data entrance exit *
          skeletonProduct skeletonKernel entrance exit)
    (hmarked_mass : ∀ data entrance exit visits,
      mu (markedAtom data entrance exit visits) =
        skeletonWeight data entrance exit *
          markedProduct markedKernel entrance exit visits) :
    AppendixPairMoment.MarkedStoppedDataUpperDecomposition
      mu pairEvent successful skeletonWeight skeletonKernel markedKernel
        visitEvent := by
  classical
  constructor
  · rw [hsuccessful, measure_iUnion hskeleton_disjoint]
    · simp_rw [indexedSkeletonAtom, hskeleton_mass]
      rw [successfulSkeletonMass]
      exact tsum_three fun data entrance exit ↦
        skeletonWeight data entrance exit *
          skeletonProduct skeletonKernel entrance exit
    · intro i
      exact hskeleton_measurable i.1 i.2.1 i.2.2
  · have hrestricted_measurable : ∀ i : MarkedIndex Data Entrance Exit m,
        MeasurableSet (restrictedMarkedAtom visitEvent markedAtom i) := by
      intro i
      by_cases hi : i.2.2.2 ∈ visitEvent
      · rw [restrictedMarkedAtom, if_pos hi]
        exact hmarked_measurable i.1 i.2.1 i.2.2.1 i.2.2.2
      · rw [restrictedMarkedAtom, if_neg hi]
        exact MeasurableSet.empty
    have hrestricted_disjoint : Pairwise fun
        i j : MarkedIndex Data Entrance Exit m ↦
          Disjoint (restrictedMarkedAtom visitEvent markedAtom i)
            (restrictedMarkedAtom visitEvent markedAtom j) := by
      intro i j hij
      by_cases hi : i.2.2.2 ∈ visitEvent
      · by_cases hj : j.2.2.2 ∈ visitEvent
        · simp only [restrictedMarkedAtom, hi, hj, if_true]
          exact hmarked_disjoint hij
        · simp only [restrictedMarkedAtom, hi, hj, if_true, if_false]
          exact disjoint_bot_right
      · simp only [restrictedMarkedAtom, hi, if_false]
        exact disjoint_bot_left
    have hrestricted_mass : ∀ i : MarkedIndex Data Entrance Exit m,
        mu (restrictedMarkedAtom visitEvent markedAtom i) =
          restrictedMarkedProduct markedKernel visitEvent
            (skeletonWeight i.1 i.2.1 i.2.2.1)
              i.2.1 i.2.2.1 i.2.2.2 := by
      intro i
      by_cases hi : i.2.2.2 ∈ visitEvent
      · rw [restrictedMarkedAtom, if_pos hi, indexedMarkedAtom,
          hmarked_mass, restrictedMarkedProduct, if_pos hi]
      · rw [restrictedMarkedAtom, if_neg hi,
          restrictedMarkedProduct, if_neg hi, measure_empty]
    have hunion_mass :
        mu (⋃ i : MarkedIndex Data Entrance Exit m,
            restrictedMarkedAtom visitEvent markedAtom i) =
          markedVisitEventMass skeletonWeight markedKernel visitEvent := by
      rw [measure_iUnion hrestricted_disjoint hrestricted_measurable]
      simp_rw [hrestricted_mass]
      rw [markedVisitEventMass]
      exact tsum_four fun data entrance exit visits ↦
        restrictedMarkedProduct markedKernel visitEvent
          (skeletonWeight data entrance exit) entrance exit visits
    rw [← hunion_mass]
    exact measure_mono hpair_union

end

end Erdos1165.MarkedSkeletonPartitionUpper
