/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterOnlyVertexStarConcentration
import ErdosProblems.Erdos207.TimedStoppedJointInclusion

/-!
# Terminal residual degrees from vertex-star concentration

The vertex-star martingale estimate is useful only on trajectories which
remain active until the terminal clock.  This file makes that conversion and
takes the union bound over vertices.  Inactive trajectories are deliberately
left out: the sharp-process failure theorem pays for that event once, rather
than once for every vertex.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- On active terminal trajectories, a sufficiently large cumulative
vertex-selection rate forces every residual internal degree below `R`, apart
from the sum of the fixed-vertex exponential tails. -/
theorem probability_timedStoppedGreedy_active_exists_residualDegree_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (U : Finset V) (A : TripleSystemOn V)
    (active : ℕ → GreedyStateOn V → Prop) (S₀ : GreedyStateOn V)
    (Kpair R starCap : ℕ) (d M : ℕ → ℕ) (theta a : ℝ)
    (hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀)
    (houtside₀ : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S₀)
    (htri : ConsistsOfTriangles G A)
    (hchosen₀ : S₀.chosen = ∅)
    (hRpos : 0 < R)
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
    (hstarCap : (univ \ U).card - 1 ≤ R + 2 * starCap)
    (hcumulative : a + starCap ≤ cumulativeGreedyRate
      (outerOnlyVertexSelectionRate R d M) n)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) :
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    ((L.probability (fun z ↦ active z.1.1 z.2 ∧ ∃ v : V,
      R ≤ (scheduledEdgesAt
        (preliminaryResidualInternalEdges G U z.2.chosen) v).card) : ℝ)) ≤
      (Fintype.card V : ℝ) *
        Real.exp (-theta * a + theta ^ 2 * (n : ℝ)) := by
  classical
  dsimp only
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let rate := outerOnlyVertexSelectionRate R d M
  let residualDegree : GreedyStateOn V → V → ℕ := fun S v ↦
    (scheduledEdgesAt
      (preliminaryResidualInternalEdges G U S.chosen) v).card
  let Bad : V → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun v z ↦ active z.1.1 z.2 ∧ R ≤ residualDegree z.2 v
  have hInv : L.SupportedOn (fun z ↦
      AbsorberGreedyInvariant F (outerOnlyAvailable U A) z.2) := by
    apply FiniteLaw.timedStoppedProcessLaw_supported n
      (fun _ ↦ greedyKernel F) active S₀ hAbs₀
    intro _i _hi S hS
    exact absorberGreedyKernel_supported hS
  have hchosen : L.SupportedOn (fun z ↦ S₀.chosen ⊆ z.2.chosen) := by
    simpa only [L] using FiniteLaw.timedStoppedProcessLaw_supported
      (P := fun S ↦ S₀.chosen ⊆ S.chosen) n
      (fun _ ↦ greedyKernel F) active S₀ Subset.rfl (by
        intro _i _hi S hS S' hmass
        exact hS.trans
          ((greedyKernel_monotone_singleInsertion F S) S' hmass).1)
  have hterminal : L.SupportedOn (fun z ↦
      z.1.1 = n ∨ ¬ active z.1.1 z.2) := by
    simpa only [L] using
      FiniteLaw.timedStoppedProcessLaw_supported_terminal n
        (fun _ ↦ greedyKernel F) active S₀
  have hsupport : L.SupportedOn (fun z ↦
      AbsorberGreedyInvariant F (outerOnlyAvailable U A) z.2 ∧
        S₀.chosen ⊆ z.2.chosen ∧
        (z.1.1 = n ∨ ¬ active z.1.1 z.2)) := by
    intro z hz
    exact ⟨hInv z hz, hchosen z hz, hterminal z hz⟩
  have hbadAt : ∀ v : V, ((L.probability (Bad v) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ)) := by
    intro v
    by_cases halive₀ : R ≤ residualDegree S₀ v
    · have htail :=
        probability_timedStoppedGreedy_residualDegree_alive_deficit_ge_le_exp
          n F G U A active S₀ Kpair R d M v theta a hAbs₀ houtside₀
          htri havailable hpairTwo hfloor hMpos hMbound hsmall hrateOne
          (by simpa only [residualDegree] using halive₀) htheta hthetaOne
      apply le_trans ?_ htail
      exact_mod_cast L.probability_mono_of_supported hsupport (by
        intro z hz hbad
        have htime : z.1.1 = n :=
          hz.2.2.resolve_right (not_not_intro hbad.1)
        have hv : v ∉ U := by
          intro hvU
          have hempty : scheduledEdgesAt
              (preliminaryResidualInternalEdges G U z.2.chosen) v = ∅ := by
            ext e
            constructor
            · intro heScheduled
              have heData := mem_scheduledEdgesAt_iff.mp heScheduled
              have heInternal :=
                preliminaryResidualInternalEdges_subset_internalOuterEdges
                  G U z.2.chosen heData.1
              have hout := (mem_internalOuterEdges_iff.mp heInternal).2
              have hve := heData.2
              rw [← e.out_eq] at hve
              rcases Sym2.mem_iff.mp hve with hve | hve
              · exact (hout.1 (hve ▸ hvU)).elim
              · exact (hout.2 (hve ▸ hvU)).elim
            · simp
          have : residualDegree z.2 v = 0 := by
            simp only [residualDegree, hempty, card_empty]
          omega
        have hselected : z.2.chosen ⊆ A :=
          hz.1.2.1.1.trans (outerOnlyAvailable_subset U A)
        have houter : TrianglesDisjointFrom U z.2.chosen := by
          intro T hT
          exact (mem_outerOnlyAvailable_iff.mp (hz.1.2.1.1 hT)).2
        have hstar := residual_add_covered_star_le_outer_card_sub_one
          hz.1.1.1 htri hselected houter hv
        have hstarNat : (triplesThrough z.2.chosen v).card ≤ starCap := by
          have hres : R ≤ (scheduledEdgesAt
              (preliminaryResidualInternalEdges G U z.2.chosen) v).card := by
            simpa only [Bad, residualDegree] using hbad.2
          omega
        have hstarReal : selectedStarCountReal v z.2 ≤ starCap := by
          unfold selectedStarCountReal
          exact_mod_cast hstarNat
        refine ⟨by simpa only [residualDegree] using hbad.2, ?_⟩
        rw [selectedStarDeficit, htime]
        have hzero : selectedStarCountReal v S₀ = 0 := by
          simp [selectedStarCountReal, triplesThrough, hchosen₀]
        rw [hzero, sub_zero]
        change a ≤ cumulativeGreedyRate rate n - selectedStarCountReal v z.2
        have hcum : a + (starCap : ℝ) ≤ cumulativeGreedyRate rate n := by
          simpa only [rate] using hcumulative
        linarith)
    · have hzero : L.probability (Bad v) = 0 := by
        apply le_antisymm
        · calc
            L.probability (Bad v) ≤ L.probability (fun _ ↦ False) := by
              apply L.probability_mono_of_supported hsupport
              intro z hz hbad
              exfalso
              apply halive₀
              have hantitone :=
                card_scheduled_preliminaryResidualInternalEdges_antitone
                  G U v hz.2.1
              exact hbad.2.trans hantitone
            _ = 0 := L.probability_false
        · exact zero_le
      rw [hzero]
      positivity
  have hunionNN := L.probability_exists_le (univ : Finset V) Bad
  have hunionReal :
      ((L.probability (fun z ↦ ∃ v : V, Bad v z) : ℝ)) ≤
        ∑ v : V, ((L.probability (Bad v) : ℝ)) := by
    exact_mod_cast (by simpa using hunionNN)
  calc
    ((L.probability (fun z ↦ active z.1.1 z.2 ∧ ∃ v : V,
        R ≤ (scheduledEdgesAt
          (preliminaryResidualInternalEdges G U z.2.chosen) v).card) : ℝ)) =
        ((L.probability (fun z ↦ ∃ v : V, Bad v z) : ℝ)) := by
          congr 2
          funext z
          simp only [Bad, residualDegree]
          aesop
    _ ≤ ∑ v : V, ((L.probability (Bad v) : ℝ)) := hunionReal
    _ ≤ ∑ _v : V,
        Real.exp (-theta * a + theta ^ 2 * (n : ℝ)) := by
      apply sum_le_sum
      intro v _hv
      exact hbadAt v
    _ = (Fintype.card V : ℝ) *
        Real.exp (-theta * a + theta ^ 2 * (n : ℝ)) := by
      simp

/-- Adding a separate bound for process failure gives the full terminal
residual-degree tail, with the inactive event charged exactly once. -/
theorem probability_timedStoppedGreedy_exists_residualDegree_ge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (U : Finset V) (A : TripleSystemOn V)
    (active : ℕ → GreedyStateOn V → Prop) (S₀ : GreedyStateOn V)
    (Kpair R starCap : ℕ) (d M : ℕ → ℕ) (theta a epsilon : ℝ)
    (hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀)
    (houtside₀ : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S₀)
    (htri : ConsistsOfTriangles G A)
    (hchosen₀ : S₀.chosen = ∅)
    (hRpos : 0 < R)
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
    (hstarCap : (univ \ U).card - 1 ≤ R + 2 * starCap)
    (hcumulative : a + starCap ≤ cumulativeGreedyRate
      (outerOnlyVertexSelectionRate R d M) n)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (hinactive :
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      ((L.probability (fun z ↦ ¬ active z.1.1 z.2) : ℝ)) ≤ epsilon) :
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    ((L.probability (fun z ↦ ∃ v : V,
      R ≤ (scheduledEdgesAt
        (preliminaryResidualInternalEdges G U z.2.chosen) v).card) : ℝ)) ≤
      epsilon + (Fintype.card V : ℝ) *
        Real.exp (-theta * a + theta ^ 2 * (n : ℝ)) := by
  classical
  dsimp only at hinactive ⊢
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let inactive : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ ¬ active z.1.1 z.2
  let activeBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ active z.1.1 z.2 ∧ ∃ v : V,
      R ≤ (scheduledEdgesAt
        (preliminaryResidualInternalEdges G U z.2.chosen) v).card
  have hsplit : ((L.probability (fun z ↦ ∃ v : V,
        R ≤ (scheduledEdgesAt
          (preliminaryResidualInternalEdges G U z.2.chosen) v).card) : ℝ)) ≤
      ((L.probability inactive : ℝ)) + ((L.probability activeBad : ℝ)) := by
    have hmono : L.probability (fun z ↦ ∃ v : V,
          R ≤ (scheduledEdgesAt
            (preliminaryResidualInternalEdges G U z.2.chosen) v).card) ≤
        L.probability (fun z ↦ inactive z ∨ activeBad z) := by
      apply L.probability_mono
      intro z hbad
      by_cases hactive : active z.1.1 z.2
      · exact Or.inr ⟨hactive, hbad⟩
      · exact Or.inl hactive
    have hor := L.probability_or_le inactive activeBad
    exact_mod_cast hmono.trans hor
  have hactiveBad : ((L.probability activeBad : ℝ)) ≤
      (Fintype.card V : ℝ) *
        Real.exp (-theta * a + theta ^ 2 * (n : ℝ)) := by
    simpa only [L, activeBad] using
      probability_timedStoppedGreedy_active_exists_residualDegree_ge_le_exp
        n F G U A active S₀ Kpair R starCap d M theta a hAbs₀
        houtside₀ htri hchosen₀ hRpos havailable hpairTwo hfloor hMpos
        hMbound hsmall hrateOne hstarCap hcumulative htheta hthetaOne
  calc
    ((L.probability (fun z ↦ ∃ v : V,
        R ≤ (scheduledEdgesAt
          (preliminaryResidualInternalEdges G U z.2.chosen) v).card) : ℝ)) ≤
        ((L.probability inactive : ℝ)) + ((L.probability activeBad : ℝ)) :=
      hsplit
    _ ≤ epsilon + (Fintype.card V : ℝ) *
        Real.exp (-theta * a + theta ^ 2 * (n : ℝ)) := by
      apply add_le_add
      · simpa only [L, inactive] using hinactive
      · exact hactiveBad

end

end Erdos207
