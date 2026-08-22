/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.MarkedTerminalDisintegration

/-!
# Countable atom partitions for marked stopped skeletons

This file constructs the event-level decomposition required by
`MarkedTerminalDisintegration` from an actual countable measurable atom
partition.  The unmarked atoms retain the full complementary skeleton.  The
marked atoms additionally record the terminal visit vector.  Exact atom-mass
factorizations then turn countable disjoint unions into the nested `tsum`s in
`successfulSkeletonMass` and `markedVisitEventMass`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.MarkedSkeletonPartition

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
        ∑' a, ∑' bcd : B × (C × D), f a bcd.1 bcd.2.1 bcd.2.2 :=
      ENNReal.tsum_prod
        (f := fun a (bcd : B × (C × D)) ↦
          f a bcd.1 bcd.2.1 bcd.2.2)
    _ = ∑' a, ∑' b, ∑' c, ∑' d, f a b c d := by
      congr 1
      funext a
      exact tsum_three (f a)

/-- A single index for a complete unmarked skeleton atom. -/
abbrev SkeletonIndex (Data Entrance Exit : Type*) (m : ℕ) :=
  Data × ((Fin m → Entrance) × (Fin m → Exit))

/-- A single index for a complete skeleton atom with its visit-count marks. -/
abbrev MarkedIndex (Data Entrance Exit : Type*) (m : ℕ) :=
  Data × ((Fin m → Entrance) ×
    ((Fin m → Exit) × (Fin m → ℕ)))

/-- The skeleton atom selected by a bundled countable index. -/
def indexedSkeletonAtom
    {Omega Data Entrance Exit : Type*} {m : ℕ}
    (skeletonAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → Set Omega)
    (i : SkeletonIndex Data Entrance Exit m) : Set Omega :=
  skeletonAtom i.1 i.2.1 i.2.2

/-- The marked atom selected by a bundled countable index. -/
def indexedMarkedAtom
    {Omega Data Entrance Exit : Type*} {m : ℕ}
    (markedAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → (Fin m → ℕ) → Set Omega)
    (i : MarkedIndex Data Entrance Exit m) : Set Omega :=
  markedAtom i.1 i.2.1 i.2.2.1 i.2.2.2

/-- A marked atom retained precisely when its visit vector belongs to the
terminal visit event. -/
def restrictedMarkedAtom
    {Omega Data Entrance Exit : Type*} {m : ℕ}
    (visitEvent : Set (Fin m → ℕ))
    (markedAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → (Fin m → ℕ) → Set Omega)
    (i : MarkedIndex Data Entrance Exit m) : Set Omega := by
  classical
  exact if i.2.2.2 ∈ visitEvent then indexedMarkedAtom markedAtom i else ∅

/-! ## Singleton fibers of countable skeleton codes -/

/-- The part of `source` carrying one value of a countable coding function. -/
def codingFiber {Omega Index : Type*}
    (source : Set Omega) (code : Omega → Index) (i : Index) : Set Omega :=
  source ∩ code ⁻¹' {i}

theorem codingFiber_pairwise {Omega Index : Type*}
    (source : Set Omega) (code : Omega → Index) :
    Pairwise fun i j : Index ↦
      Disjoint (codingFiber source code i) (codingFiber source code j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hi : code x = i := by
    simpa only [codingFiber, mem_inter_iff, mem_preimage,
      mem_singleton_iff] using hxi.2
  have hj : code x = j := by
    simpa only [codingFiber, mem_inter_iff, mem_preimage,
      mem_singleton_iff] using hxj.2
  exact hij (hi.symm.trans hj)

theorem iUnion_codingFiber {Omega Index : Type*}
    (source : Set Omega) (code : Omega → Index) :
    (⋃ i, codingFiber source code i) = source := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hi.1
  · intro hx
    apply mem_iUnion.mpr
    refine ⟨code x, hx, ?_⟩
    simp

theorem codingFiber_measurable
    {Omega Index : Type*} [MeasurableSpace Omega]
    {source : Set Omega} {code : Omega → Index}
    (hsource : MeasurableSet source)
    (hfiber : ∀ i, MeasurableSet (code ⁻¹' {i})) (i : Index) :
    MeasurableSet (codingFiber source code i) :=
  hsource.inter (hfiber i)

/-- A measurable, pairwise-disjoint countable atom partition, together with
the two exact atom-mass factorizations, constructs the stopped-data lower
decomposition used in the terminal-excursion argument.

The marked union is only required to be contained in `terminalEvent`; this is
the one-sided direction supplied by the pathwise marked-visit containment.
The unmarked union, on the other hand, is exactly `successful`. -/
theorem markedStoppedDataLowerDecomposition_of_atom_partition
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    [Countable Data] [Countable Entrance] [Countable Exit]
    {m : ℕ} (mu : Measure Omega) (successful terminalEvent : Set Omega)
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
    (hmarked_union :
      (⋃ i : MarkedIndex Data Entrance Exit m,
        restrictedMarkedAtom visitEvent markedAtom i) ⊆ terminalEvent)
    (hskeleton_mass : ∀ data entrance exit,
      mu (skeletonAtom data entrance exit) =
        skeletonWeight data entrance exit *
          MarkedTerminalDisintegration.skeletonProduct
            skeletonKernel entrance exit)
    (hmarked_mass : ∀ data entrance exit visits,
      mu (markedAtom data entrance exit visits) =
        skeletonWeight data entrance exit *
          MarkedTerminalDisintegration.markedProduct
            markedKernel entrance exit visits) :
    MarkedTerminalDisintegration.MarkedStoppedDataLowerDecomposition
      mu successful terminalEvent skeletonWeight skeletonKernel markedKernel
        visitEvent := by
  classical
  constructor
  · rw [hsuccessful,
      measure_iUnion hskeleton_disjoint]
    · simp_rw [indexedSkeletonAtom, hskeleton_mass]
      rw [MarkedTerminalDisintegration.successfulSkeletonMass]
      exact tsum_three fun data entrance exit ↦
        skeletonWeight data entrance exit *
          MarkedTerminalDisintegration.skeletonProduct
            skeletonKernel entrance exit
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
          MarkedTerminalDisintegration.restrictedMarkedProduct markedKernel
            visitEvent (skeletonWeight i.1 i.2.1 i.2.2.1)
              i.2.1 i.2.2.1 i.2.2.2 := by
      intro i
      by_cases hi : i.2.2.2 ∈ visitEvent
      · rw [restrictedMarkedAtom, if_pos hi, indexedMarkedAtom,
          hmarked_mass, MarkedTerminalDisintegration.restrictedMarkedProduct,
          if_pos hi]
      · rw [restrictedMarkedAtom, if_neg hi,
          MarkedTerminalDisintegration.restrictedMarkedProduct, if_neg hi,
          measure_empty]
    have hunion_mass :
        mu (⋃ i : MarkedIndex Data Entrance Exit m,
            restrictedMarkedAtom visitEvent markedAtom i) =
          MarkedTerminalDisintegration.markedVisitEventMass skeletonWeight
            markedKernel visitEvent := by
      rw [measure_iUnion hrestricted_disjoint hrestricted_measurable]
      simp_rw [hrestricted_mass]
      rw [MarkedTerminalDisintegration.markedVisitEventMass]
      exact tsum_four fun data entrance exit visits ↦
        MarkedTerminalDisintegration.restrictedMarkedProduct markedKernel
          visitEvent (skeletonWeight data entrance exit) entrance exit visits
    rw [← hunion_mass]
    exact measure_mono hmarked_union

/-- Convenience constructor when both atom families are literal singleton
fibers of countable skeleton codes.  Pairwise disjointness and the exact
unmarked union are then automatic.  The pathwise marked premise says that a
point of `markedSource` whose encoded visit vector belongs to `visitEvent`
lies in `terminalEvent`. -/
theorem markedStoppedDataLowerDecomposition_of_coding_fibers
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    [Countable Data] [Countable Entrance] [Countable Exit]
    {m : ℕ} (mu : Measure Omega) (successful terminalEvent markedSource : Set Omega)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (skeletonCode : Omega → SkeletonIndex Data Entrance Exit m)
    (markedCode : Omega → MarkedIndex Data Entrance Exit m)
    (hsuccessful_measurable : MeasurableSet successful)
    (hmarkedSource_measurable : MeasurableSet markedSource)
    (hskeleton_fiber_measurable : ∀ i,
      MeasurableSet (skeletonCode ⁻¹' {i}))
    (hmarked_fiber_measurable : ∀ i,
      MeasurableSet (markedCode ⁻¹' {i}))
    (hmarked_path : ∀ x, x ∈ markedSource →
      (markedCode x).2.2.2 ∈ visitEvent → x ∈ terminalEvent)
    (hskeleton_mass : ∀ data entrance exit,
      mu (codingFiber successful skeletonCode (data, (entrance, exit))) =
        skeletonWeight data entrance exit *
          MarkedTerminalDisintegration.skeletonProduct
            skeletonKernel entrance exit)
    (hmarked_mass : ∀ data entrance exit visits,
      mu (codingFiber markedSource markedCode
          (data, (entrance, (exit, visits)))) =
        skeletonWeight data entrance exit *
          MarkedTerminalDisintegration.markedProduct
            markedKernel entrance exit visits) :
    MarkedTerminalDisintegration.MarkedStoppedDataLowerDecomposition
      mu successful terminalEvent skeletonWeight skeletonKernel markedKernel
        visitEvent := by
  classical
  let skeletonAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → Set Omega :=
    fun data entrance exit ↦
      codingFiber successful skeletonCode (data, (entrance, exit))
  let markedAtom : Data → (Fin m → Entrance) →
      (Fin m → Exit) → (Fin m → ℕ) → Set Omega :=
    fun data entrance exit visits ↦
      codingFiber markedSource markedCode (data, (entrance, (exit, visits)))
  apply markedStoppedDataLowerDecomposition_of_atom_partition mu successful
    terminalEvent skeletonWeight skeletonKernel markedKernel visitEvent
    skeletonAtom markedAtom
  · intro data entrance exit
    exact codingFiber_measurable hsuccessful_measurable
      hskeleton_fiber_measurable (data, (entrance, exit))
  · intro data entrance exit visits
    exact codingFiber_measurable hmarkedSource_measurable
      hmarked_fiber_measurable (data, (entrance, (exit, visits)))
  · simpa only [skeletonAtom, indexedSkeletonAtom] using
      codingFiber_pairwise successful skeletonCode
  · simpa only [markedAtom, indexedMarkedAtom] using
      codingFiber_pairwise markedSource markedCode
  · simpa only [skeletonAtom, indexedSkeletonAtom] using
      (iUnion_codingFiber successful skeletonCode).symm
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    by_cases hvisits : i.2.2.2 ∈ visitEvent
    · rw [restrictedMarkedAtom, if_pos hvisits] at hi
      have hi' : x ∈ codingFiber markedSource markedCode i := by
        simpa only [indexedMarkedAtom, markedAtom] using hi
      apply hmarked_path x hi'.1
      have hcode : markedCode x = i := by
        simpa only [codingFiber, mem_inter_iff, mem_preimage,
          mem_singleton_iff] using hi'.2
      simpa only [hcode] using hvisits
    · rw [restrictedMarkedAtom, if_neg hvisits] at hi
      exact hi.elim
  · exact hskeleton_mass
  · exact hmarked_mass

end

end Erdos1165.MarkedSkeletonPartition
