/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.MarkedSkeletonPartitionUpper

/-!
# Marked stopped-data partitions with dominated atom kernels

Scanner-compatible bridge subtypes have only a one-sided comparison with
the canonical unrestricted bridge kernel.  For an upper decomposition this
is sufficient: each selected marked atom may have mass *at most* its
canonical marked product.  The successful unmarked partition remains exact.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.MarkedSkeletonPartitionKernelUpper

open AppendixPairMoment MarkedSkeletonPartition
open MarkedTerminalDisintegration

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

/-- A disjoint marked atom cover only needs a mass upper bound by the
canonical marked product.  This is the exact interface needed after
restricting bridge codes to a scanner-compatible subtype. -/
theorem markedStoppedDataUpperDecomposition_of_atom_partition_kernelUpper
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
      mu (markedAtom data entrance exit visits) ≤
        skeletonWeight data entrance exit *
          markedProduct markedKernel entrance exit visits) :
    MarkedStoppedDataUpperDecomposition mu pairEvent successful
      skeletonWeight skeletonKernel markedKernel visitEvent := by
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
  · let restricted : MarkedIndex Data Entrance Exit m → Set Omega :=
      fun i ↦ restrictedMarkedAtom visitEvent markedAtom i
    have hrestricted_measurable : ∀ i, MeasurableSet (restricted i) := by
      intro i
      by_cases hi : i.2.2.2 ∈ visitEvent
      · simp only [restricted, restrictedMarkedAtom, hi, if_true]
        exact hmarked_measurable i.1 i.2.1 i.2.2.1 i.2.2.2
      · simp only [restricted, restrictedMarkedAtom, hi, if_false]
        exact MeasurableSet.empty
    have hrestricted_disjoint : Pairwise fun i j ↦
        Disjoint (restricted i) (restricted j) := by
      intro i j hij
      by_cases hi : i.2.2.2 ∈ visitEvent
      · by_cases hj : j.2.2.2 ∈ visitEvent
        · simpa only [restricted, restrictedMarkedAtom, hi, hj, if_true] using
            hmarked_disjoint hij
        · simp only [restricted, restrictedMarkedAtom, hi, hj, if_true,
            if_false]
          exact disjoint_bot_right
      · simp only [restricted, restrictedMarkedAtom, hi, if_false]
        exact disjoint_bot_left
    have hrestricted_mass : ∀ i,
        mu (restricted i) ≤
          restrictedMarkedProduct markedKernel visitEvent
            (skeletonWeight i.1 i.2.1 i.2.2.1)
              i.2.1 i.2.2.1 i.2.2.2 := by
      intro i
      by_cases hi : i.2.2.2 ∈ visitEvent
      · simpa only [restricted, restrictedMarkedAtom, indexedMarkedAtom,
          hi, if_true, restrictedMarkedProduct] using
            hmarked_mass i.1 i.2.1 i.2.2.1 i.2.2.2
      · simp only [restricted, restrictedMarkedAtom, hi, if_false,
          restrictedMarkedProduct, measure_empty]
        exact bot_le
    calc
      mu pairEvent ≤ mu (⋃ i, restricted i) := by
        apply measure_mono
        simpa only [restricted] using hpair_union
      _ = ∑' i, mu (restricted i) :=
        measure_iUnion hrestricted_disjoint hrestricted_measurable
      _ ≤ ∑' i, restrictedMarkedProduct markedKernel visitEvent
            (skeletonWeight i.1 i.2.1 i.2.2.1)
              i.2.1 i.2.2.1 i.2.2.2 :=
        ENNReal.tsum_le_tsum hrestricted_mass
      _ = markedVisitEventMass skeletonWeight markedKernel visitEvent := by
        rw [markedVisitEventMass]
        exact tsum_four fun data entrance exit visits ↦
          restrictedMarkedProduct markedKernel visitEvent
            (skeletonWeight data entrance exit) entrance exit visits

end

end Erdos1165.MarkedSkeletonPartitionKernelUpper
