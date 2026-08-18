/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredCompletedReserveCertificate

/-!
# Greedy generator completion gives the centered reserve certificate

This file packages the finite generator-completion theorem directly into
the centered Corollary 2.17/map-back constructor.  In particular, callers
no longer have to expose the auxiliary completion family or prove its
disjointness, total-size, source-containment, and spanning properties.
-/

namespace Erdos186.CFP

noncomputable section

namespace RandomPartition

/-- Uniform constants for the centered greedy/completion construction.

The remaining inputs are precisely the facts that precede generator
completion: a first-crossing lower bound for every color, a uniformly
bounded nonzero relative index for the greedy selections, and identification
of every color-class span with the common centered span. -/
theorem exists_centeredGreedyCompletionReserveCertificateConstants
    (d : ℕ) (hd : 0 < d) (cNum cDen : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen) :
    ∃ corConstant corWidth denseConstant denseEll denseWidth : ℕ,
      0 < corConstant ∧ 0 < denseConstant ∧
      ∀ {W B A : Finset ℤ} {relevant : Finset ℕ}
        (hproper : Stability.RelevantBoxesProper W relevant),
        (hdrel : d ∈ relevant) → B ⊆ W → A ⊆ B → 0 ∈ B →
        ∀ {q deletionBudget steps level sourceScale s D blockSize K : ℕ}
          (c : {a // a ∈ A} → Fin (q + 1)),
          denseEll ≤ q + 1 →
          max corWidth denseWidth ≤
            (Preprocessing.centeredCoordinateAxisBox
              (BoundingBox.dBoundingBox W d
                (hproper.positive hdrel)).progression
              sourceScale).minWidth →
          denseConstant ≤ q + 1 →
          0 < sourceScale → d ≤ D → 0 < steps →
          (∀ i, steps ≤ (integerColorClass A c i).card) →
          (∀ i, Greedy.dyadicBinStart (integerColorClass A c i)
            deletionBudget steps level < steps) →
          (∀ i, cNum *
              (Preprocessing.centeredCoordinateAxisBox
                (BoundingBox.dBoundingBox W d
                  (hproper.positive hdrel)).progression
                sourceScale).volume ≤
            cDen * Greedy.positiveDyadicThreshold
              (integerColorClass A c i) deletionBudget level) →
          (∀ i,
            (Stability.generatedSubgroup
                (Stability.centeredMinimalIdentificationFamily hproper d)
                (Greedy.selected (integerColorClass A c i) steps)).relIndex
              (Stability.generatedSubgroup
                (Stability.centeredMinimalIdentificationFamily hproper d)
                (integerColorClass A c i)) ≠ 0) →
          (∀ i,
            (Stability.generatedSubgroup
                (Stability.centeredMinimalIdentificationFamily hproper d)
                (Greedy.selected (integerColorClass A c i) steps)).relIndex
              (Stability.generatedSubgroup
                (Stability.centeredMinimalIdentificationFamily hproper d)
                (integerColorClass A c i)) ≤ K) →
          (∀ i, Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d)
              (integerColorClass A c i) =
            Stability.generatedSubgroup
              (Stability.centeredMinimalIdentificationFamily hproper d) B) →
          steps + K ≤ sourceScale →
          (q + 1) * (steps + K) ≤ s →
          s ≤ 2 * (q + 1) * blockSize →
          (((BoundingBox.dBoundingBox W d
              (hproper.positive hdrel)).progression).dilate
            (((q + 1) / denseConstant) * corConstant *
              (2 * sourceScale))).Proper →
          Nonempty (PreprocessedReserveCertificate B s D 0 1
            (4 * denseConstant * blockSize)) := by
  obtain ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
      hcorConstant, hdenseConstant, hcertificate⟩ :=
    exists_centeredCompletedReserveCertificateConstants
      d hd cNum cDen hcNum hc
  refine ⟨corConstant, corWidth, denseConstant, denseEll, denseWidth,
    hcorConstant, hdenseConstant, ?_⟩
  intro W B A relevant hproper hdrel hBW hAB hzeroB q deletionBudget steps level
    sourceScale s D blockSize K c hell hwidth hCell hsourceScale hdD hstepsPos
    hlarge hcross hvolume hfinite hindex hambient hsourceBound hsLower
    hsUpper hnoCarry
  let phi := Stability.centeredMinimalIdentificationFamily hproper d
  let Gamma := Stability.generatedSubgroup phi B
  obtain ⟨completion, hcompletionSubset, _hcompletionDisjoint,
      hcompletionCard, hreserveCard, hreserveSubset, hreserveDisjoint,
      hreserveTotal, hgenerated⟩ :=
    exists_bounded_greedyColorGeneratorCompletionFamily
      c phi Gamma hlarge hfinite hindex hambient
  apply hcertificate hproper hdrel hBW hAB hzeroB c completion hell hwidth hCell
    hsourceScale hdD hlarge hcross
  · intro i
    have hcard : (completedColorSet A c steps completion i).card =
        steps + (completion i).card := by
      simpa only [completedGreedyColorReserve, Stability.card_integerPoints]
        using hreserveCard i
    rw [hcard]
    exact Nat.add_le_add_left (hcompletionCard i) steps |>.trans hsourceBound
  · intro i z hz
    rcases Finset.mem_union.mp hz with hzSelected | hzCompletion
    · exact integerColorClass_subset A c i
        (Greedy.selected_subset (integerColorClass A c i) steps hzSelected)
    · exact integerColorClass_subset A c i
        ((Finset.mem_sdiff.mp (hcompletionSubset i hzCompletion)).1)
  · exact hvolume
  · exact hgenerated
  · exact hreserveDisjoint
  · intro i
    exact (hreserveSubset i).trans (Stability.integerPoints_mono hAB)
  · intro i
    exact Finset.card_pos.mp (by rw [hreserveCard i]; omega)
  · exact hreserveTotal.trans hsLower
  · exact hsUpper
  · exact hnoCarry

end RandomPartition

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.RandomPartition.exists_centeredGreedyCompletionReserveCertificateConstants
