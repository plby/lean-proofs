/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterOnlyVertexStarRate
import ErdosProblems.Erdos207.OutsidePairSurvival

/-!
# Residual-degree concentration in the outer-only process

As long as a fixed residual vertex degree is at least `R`, the deterministic
rate lemma supplies a lower bound for the probability that the next chosen
triangle contains the vertex. Dead paths are discarded only after their
boundary-crossing increment contributes to the one-step exponential bound.
-/

namespace Erdos207

open Finset

noncomputable section

theorem probability_timedStoppedGreedy_residualDegree_alive_deficit_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (U : Finset V) (A : TripleSystemOn V)
    (active : ℕ → GreedyStateOn V → Prop) (S₀ : GreedyStateOn V)
    (Kpair R : ℕ) (d M : ℕ → ℕ) (v : V) (theta a : ℝ)
    (hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀)
    (houtside₀ : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S₀)
    (htri : ConsistsOfTriangles G A)
    (havailable : ∀ i, i < n → ∀ S,
      AbsorberGreedyInvariant F (outerOnlyAvailable U A) S →
      OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S →
      active i S → S.available.Nonempty)
    (hpairTwo : ∀ i, i < n → ∀ S,
      AbsorberGreedyInvariant F (outerOnlyAvailable U A) S →
      OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S →
      active i S → HasPairTwoAwayCutoff F Kpair S)
    (hfloor : ∀ i, i < n → ∀ S,
      AbsorberGreedyInvariant F (outerOnlyAvailable U A) S →
      OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S →
      active i S → HasAvailablePairFloor (d i) S)
    (hMpos : ∀ i, i < n → 0 < M i)
    (hMbound : ∀ i, i < n → ∀ S,
      AbsorberGreedyInvariant F (outerOnlyAvailable U A) S →
      OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S →
      active i S → S.available.card ≤ M i)
    (hsmall : ∀ i, i < n → 3 + Kpair < d i)
    (hrateOne : ∀ i, i < n → R * d i ≤ 2 * M i)
    (halive₀ : R ≤ (scheduledEdgesAt
      (preliminaryResidualInternalEdges G U S₀.chosen) v).card)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) :
    let rate := outerOnlyVertexSelectionRate R d M
    let alive := fun S : GreedyStateOn V ↦
      R ≤ (scheduledEdgesAt
        (preliminaryResidualInternalEdges G U S.chosen) v).card
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    ((L.probability (fun z ↦ alive z.2 ∧
      a ≤ selectedStarDeficit rate v S₀ z.1.1 z.2) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ)) := by
  classical
  dsimp only
  let rate := outerOnlyVertexSelectionRate R d M
  let alive := fun S : GreedyStateOn V ↦
    R ≤ (scheduledEdgesAt
      (preliminaryResidualInternalEdges G U S.chosen) v).card
  let P := fun S : GreedyStateOn V ↦
    AbsorberGreedyInvariant F (outerOnlyAvailable U A) S ∧
      OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S
  suffices htail :
      (((FiniteLaw.timedStoppedProcessLaw n
          (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ alive z.2 ∧
          a ≤ selectedStarDeficit rate v S₀ z.1.1 z.2 -
            selectedStarDeficit rate v S₀ 0 S₀) : ℝ)) ≤
        Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * 1) by
    simpa only [alive, rate, selectedStarDeficit_zero_initial, sub_zero,
      mul_one] using htail
  apply FiniteLaw.probability_timedStoppedProcess_alive_deviation_ge_le_exp_fullIncrement
    (P := P) (alive := alive) n (fun _ ↦ greedyKernel F) active
    (selectedStarDeficit rate v S₀) S₀ theta 1 a 1
  · exact ⟨hAbs₀, houtside₀⟩
  · exact halive₀
  · exact htheta
  · norm_num
  · simpa using hthetaOne
  · norm_num
  · intro i hi S hP hactive
    have hout := greedyKernel_supported_outsideLeavePairsAlive_of_pairCutoff
      hP.2 hP.1.1 (hpairTwo i hi S hP.1 hP.2 hactive)
      (hfloor i hi S hP.1 hP.2 hactive) (hsmall i hi)
    intro S' hmass
    exact ⟨absorberGreedyKernel_supported hP.1 S' hmass, hout S' hmass⟩
  · intro i hi S hP _hactive hdead S' hmass hAlive'
    rcases greedyKernel_supported_step_or_self F S S' hmass with
      rfl | ⟨T, _hT, rfl⟩
    · exact hdead hAlive'
    · apply hdead
      apply hAlive'.trans
      apply card_scheduled_preliminaryResidualInternalEdges_antitone G U v
      intro Q hQ
      exact mem_insert_of_mem hQ
  · intro i hi S hP hactive _hAlive S' hmass _hP'
    have hA := havailable i hi S hP.1 hP.2 hactive
    have hinc := greedyKernel_selectedStar_increment_mem_zero_one
      F S hP.1.1 hA v hmass
    have hdelta :
        selectedStarDeficit rate v S₀ (i + 1) S' -
            selectedStarDeficit rate v S₀ i S =
          rate i -
            (selectedStarCountReal v S' - selectedStarCountReal v S) := by
      simp only [selectedStarDeficit, cumulativeGreedyRate_succ]
      ring
    rw [hdelta]
    rcases hinc with hzero | hone
    · rw [hzero, sub_zero]
      exact (outerOnlyVertexSelectionRate_le_one R d M i
        (hMpos i hi) (hrateOne i hi)).trans (by norm_num)
    · rw [hone]
      have hrnonneg : 0 ≤ rate i := by
        exact outerOnlyVertexSelectionRate_nonneg R d M i
      linarith [outerOnlyVertexSelectionRate_le_one R d M i
        (hMpos i hi) (hrateOne i hi)]
  · intro i hi S hP hactive hAlive
    have hA := havailable i hi S hP.1 hP.2 hactive
    have hratio : rate i ≤
        ((availableTriplesThrough S v).card : ℝ) /
          (S.available.card : ℝ) := by
      simpa only [rate, outerOnlyVertexSelectionRate] using
        (outerOnlyVertexSelectionRate_le_available_ratio
          hP.1 htri hP.2 (hfloor i hi S hP.1 hP.2 hactive) v hAlive
          hA (hMpos i hi) (hMbound i hi S hP.1 hP.2 hactive))
    calc
      (greedyKernel F S).expectationReal
          (fun S' ↦ selectedStarDeficit rate v S₀ (i + 1) S' -
            selectedStarDeficit rate v S₀ i S) =
        (greedyKernel F S).expectationReal
          (fun S' ↦ rate i -
            (selectedStarCountReal v S' - selectedStarCountReal v S)) := by
          congr 1
          funext S'
          simp only [selectedStarDeficit, cumulativeGreedyRate_succ]
          ring
      _ = rate i - (greedyKernel F S).expectationReal
          (fun S' ↦ selectedStarCountReal v S' -
            selectedStarCountReal v S) := by
        rw [FiniteLaw.expectationReal_sub, FiniteLaw.expectationReal_const]
      _ = rate i - ((availableTriplesThrough S v).card : ℝ) /
          (S.available.card : ℝ) := by
        rw [greedyKernel_expectationReal_selectedStar_increment
          F S hP.1.1 hA v]
      _ ≤ 0 := sub_nonpos.mpr hratio
  · intro i hi S hP hactive _hAlive
    have hA := havailable i hi S hP.1 hP.2 hactive
    have hjump : ∀ S', 0 < (greedyKernel F S).mass S' →
        |selectedStarDeficit rate v S₀ (i + 1) S' -
          selectedStarDeficit rate v S₀ i S| ≤ 1 := by
      intro S' hmass
      have hinc := greedyKernel_selectedStar_increment_mem_zero_one
        F S hP.1.1 hA v hmass
      have hdelta :
          selectedStarDeficit rate v S₀ (i + 1) S' -
              selectedStarDeficit rate v S₀ i S =
            rate i -
              (selectedStarCountReal v S' - selectedStarCountReal v S) := by
        simp only [selectedStarDeficit, cumulativeGreedyRate_succ]
        ring
      rw [hdelta]
      have hrnonneg : 0 ≤ rate i :=
        outerOnlyVertexSelectionRate_nonneg R d M i
      have hrone : rate i ≤ 1 :=
        outerOnlyVertexSelectionRate_le_one R d M i
          (hMpos i hi) (hrateOne i hi)
      rcases hinc with hzero | hone
      · rw [hzero, sub_zero, abs_of_nonneg hrnonneg]
        exact hrone
      · rw [hone, abs_of_nonpos (sub_nonpos.mpr hrone)]
        linarith
    calc
      (greedyKernel F S).expectationReal
          (fun S' ↦ (selectedStarDeficit rate v S₀ (i + 1) S' -
            selectedStarDeficit rate v S₀ i S) ^ 2) ≤
        (greedyKernel F S).expectationReal (fun _ ↦ (1 : ℝ)) := by
          refine FiniteLaw.expectationReal_mono_of_supported
            (greedyKernel F S)
            (P := fun S' ↦ 0 < (greedyKernel F S).mass S')
            (fun _ hmass ↦ hmass) ?_
          intro S' hmass
          have habs := hjump S' hmass
          have habs0 : 0 ≤ |selectedStarDeficit rate v S₀ (i + 1) S' -
              selectedStarDeficit rate v S₀ i S| := abs_nonneg _
          have hsquare : |selectedStarDeficit rate v S₀ (i + 1) S' -
              selectedStarDeficit rate v S₀ i S| ^ 2 ≤ 1 := by
            nlinarith
          simpa [sq_abs] using hsquare
      _ = 1 := FiniteLaw.expectationReal_const _ _

end

end Erdos207
