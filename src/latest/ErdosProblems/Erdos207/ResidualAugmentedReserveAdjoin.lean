/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualReserveAdjoin
import ErdosProblems.Erdos207.PreliminaryAugmentedReserve

/-! # Two exact partitions for the full-union residual event and augmented reserve -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

theorem residualReserveEvent_augmented_partition
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V] [DecidableEq V]
    (initial later : Ω → TripleSystemOn V) (sampled : Ω → Finset (Sym2 V))
    (working : Ω → SimpleGraph V) (U : Finset V)
    (added : Ω → Ξ → TripleSystemOn V) (G : SimpleGraph V)
    (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V)) (z : Ω × Ξ)
    (hpack : IsPackingOn ((initial z.1 ∪ later z.1) ∪ added z.1 z.2))
    (hdis : Disjoint (initial z.1 ∪ later z.1) (added z.1 z.2))
    (hgraph : ∀ T ∈ added z.1 z.2, tripleEdgeFinset T ⊆ graphEdges G)
    (hz : ResidualReserveDistributionEvent (jointInitial initial) (jointLater later added)
      (fun z ↦ preliminaryAugmentedReserve (working z.1) U (sampled z.1) (added z.1 z.2))
      Ifix Dfix Efix Rfix z) :
    ∃ S ∈ Dfix.powerset, ∃ T ∈ Rfix.powerset,
      (IsPackingOn (Dfix \ S) ∧ (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G ∧
        Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix) ∧
      ResidualReserveDistributionEvent initial later sampled Ifix S
        (pendingSurvivalEdges (Dfix \ S) Efix) T z.1 ∧
      Dfix \ S ⊆ added z.1 z.2 ∧
      Rfix \ T ⊆ preliminaryResidualCrossingEdges (working z.1) U (added z.1 z.2) \ sampled z.1 := by
  obtain ⟨S, hS, hQ, hG, hQE, hOld, hNew⟩ := residualDistributionEvent_adjoin_partition
    initial later added G Ifix Dfix Efix z hpack hdis hgraph hz.1
  refine ⟨S, hS, Rfix ∩ sampled z.1, mem_powerset.mpr inter_subset_left,
    ⟨hQ, hG, hQE⟩, ⟨hOld, inter_subset_right⟩, hNew, ?_⟩
  intro e he
  have heR := (mem_sdiff.mp he).1
  have heNot : e ∉ sampled z.1 := fun heS ↦ (mem_sdiff.mp he).2 (mem_inter.mpr ⟨heR, heS⟩)
  exact mem_sdiff.mpr ⟨(mem_union.mp (hz.2 heR)).resolve_left heNot, heNot⟩

theorem FiniteLaw.jointBind_residual_augmentedReserve_probability_le_on_support
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (G : SimpleGraph V)
    (initial later : Ω → TripleSystemOn V) (sampled : Ω → Finset (Sym2 V))
    (working : Ω → SimpleGraph V) (U : Finset V)
    (added : Ω → Ξ → TripleSystemOn V)
    (bound : TripleSystemOn V → Finset (Sym2 V) → ℝ≥0)
    (hpre : ∀ ω, 0 < L.mass ω → ∀ Q E,
      (K ω).probability (fun ξ ↦ Q ⊆ added ω ξ ∧
        E ⊆ preliminaryResidualCrossingEdges (working ω) U (added ω ξ) \ sampled ω) ≤ bound Q E)
    (hstruct : ∀ ω, 0 < L.mass ω → (K ω).SupportedOn fun ξ ↦
      IsPackingOn ((initial ω ∪ later ω) ∪ added ω ξ) ∧
      Disjoint (initial ω ∪ later ω) (added ω ξ) ∧
      ∀ T ∈ added ω ξ, tripleEdgeFinset T ⊆ graphEdges G)
    (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V)) :
    (L.jointBind K).probability
      (ResidualReserveDistributionEvent (jointInitial initial) (jointLater later added)
        (fun z ↦ preliminaryAugmentedReserve (working z.1) U (sampled z.1) (added z.1 z.2))
        Ifix Dfix Efix Rfix) ≤
      ∑ S ∈ Dfix.powerset, ∑ T ∈ Rfix.powerset,
        if IsPackingOn (Dfix \ S) ∧ (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G ∧
          Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix then
          bound (Dfix \ S) (Rfix \ T) * L.probability
            (ResidualReserveDistributionEvent initial later sampled Ifix S
              (pendingSurvivalEdges (Dfix \ S) Efix) T) else 0 := by
  classical
  let Good := fun S : TripleSystemOn V ↦ IsPackingOn (Dfix \ S) ∧
    (Dfix \ S).biUnion tripleEdgeFinset ⊆ graphEdges G ∧
    Disjoint ((Dfix \ S).biUnion tripleEdgeFinset) Efix
  let Old := fun S : TripleSystemOn V ↦ fun T : Finset (Sym2 V) ↦
    ResidualReserveDistributionEvent initial later sampled Ifix S (pendingSurvivalEdges (Dfix \ S) Efix) T
  let New := fun S : TripleSystemOn V ↦ fun T : Finset (Sym2 V) ↦ fun ω ξ ↦
    Dfix \ S ⊆ added ω ξ ∧
      Rfix \ T ⊆ preliminaryResidualCrossingEdges (working ω) U (added ω ξ) \ sampled ω
  let Event := fun S : TripleSystemOn V ↦ fun T : Finset (Sym2 V) ↦ fun z : Ω × Ξ ↦
    Good S ∧ Old S T z.1 ∧ New S T z.1 z.2
  have hsupport := (show L.SupportedOn (fun ω ↦ 0 < L.mass ω) from fun _ h ↦ h).jointBind hstruct
  have hcover : (L.jointBind K).probability
      (ResidualReserveDistributionEvent (jointInitial initial) (jointLater later added)
        (fun z ↦ preliminaryAugmentedReserve (working z.1) U (sampled z.1) (added z.1 z.2))
        Ifix Dfix Efix Rfix) ≤
      (L.jointBind K).probability (fun z ↦ ∃ S ∈ Dfix.powerset, ∃ T ∈ Rfix.powerset, Event S T z) := by
    apply (L.jointBind K).probability_mono_of_supported hsupport
    intro z hz hevent
    exact residualReserveEvent_augmented_partition initial later sampled working U added G
      Ifix Dfix Efix Rfix z hz.2.1 hz.2.2.1 hz.2.2.2 hevent
  apply hcover.trans ((L.jointBind K).probability_exists_le Dfix.powerset
    (fun S z ↦ ∃ T ∈ Rfix.powerset, Event S T z) |>.trans _)
  apply sum_le_sum
  intro S _hS
  apply ((L.jointBind K).probability_exists_le Rfix.powerset (Event S)).trans
  apply sum_le_sum
  intro T _hT
  change (L.jointBind K).probability (Event S T) ≤ if Good S then _ else _
  by_cases hgood : Good S
  · rw [if_pos hgood]
    have hremove : Event S T = (fun z ↦ Old S T z.1 ∧ New S T z.1 z.2) := by
      funext z
      simp only [Event, hgood, true_and]
    rw [hremove]
    exact L.jointBind_probability_and_le_on_support K (Old S T) (New S T)
      (bound (Dfix \ S) (Rfix \ T)) (fun ω hω _ ↦ hpre ω hω (Dfix \ S) (Rfix \ T))
  · rw [if_neg hgood]
    have hzero : Event S T = (fun _ ↦ False) := by
      funext z
      simp only [Event, hgood, false_and]
    rw [hzero, FiniteLaw.probability_false]

end

end Erdos207
