/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingObstructionCharacterization

/-!
# The remaining finite diagonal emergence case

This file isolates the exact limit-reflection issue in the finite diagonal
branch of source Lemma 7.27.  A diagonal record is either genuinely new at
its successor rung, or it is already inessential in the current accumulated
warp despite occurring in no earlier successor-inessential family.  The
second alternative is the zero/limit-stage reflection problem; it cannot be
discarded merely from forward persistence of inessential components.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- Exact split of the diagonal-emergence case.  Outside the genuinely
successor-new record stages, the selected path is already inessential in the
current accumulated warp, but it was not inessential in any earlier
successor warp.  The latter fact is the minimality content of diagonal
emergence. -/
theorem diagonalEmergence_fresh_or_currentInessentialWithoutPriorSuccessor
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Stage kappa} (ha : a ∈ L.diagonalEmergenceStages hlegal)
    {p : Gamma.DPath} (hpChosen : L.chosen a = some p) :
    a ∈ L.freshInessentialRecordStages ∨
      (p ∈ Gamma.inessentialPaths (L.warpAt a) ∧
        ∀ b : Stage kappa, b < a →
          p ∉ Gamma.inessentialPaths (L.successorWarp b)) := by
  by_cases hfresh : a ∈ L.freshInessentialRecordStages
  · exact Or.inl hfresh
  · right
    have hprior : a ∈ L.priorInessentialRecordStages := by
      by_contra hnotPrior
      exact hfresh ⟨ha.1, hnotPrior⟩
    obtain ⟨q, hqChosen, hqCurrent⟩ := hprior
    have hqp : q = p := Option.some.inj (hqChosen.symm.trans hpChosen)
    subst q
    refine ⟨hqCurrent, ?_⟩
    intro b hba
    let B := L.concreteBookkeeping
    let hB : B.IsValid :=
      L.concreteBookkeeping_isValid hlegal.validBookkeeping
    have hpSelected :
        B.selectedPath hB ⟨a, ha.1⟩ = p := by
      apply Option.some.inj
      exact (B.chosen_selectedPath hB ⟨a, ha.1⟩).symm.trans hpChosen
    have hemergence : B.emergenceIndex hB a = a := ha.2
    have hb : b < B.emergenceIndex hB a := by
      rw [hemergence]
      exact hba
    have hnot := B.not_mem_inessentialNext_of_lt_emergenceIndex
      hB ha.1 hb
    rw [hpSelected] at hnot
    exact hnot

/-- The precise finite reflection principle which would eliminate the
non-fresh diagonal alternative: every selected finite path already
inessential in its current accumulated warp must have been inessential in
some strictly earlier successor warp.  This theorem records the reduction;
the principle is deliberately a premise because it is not a field of
`IsLegal`. -/
theorem diagonalEmergence_finite_mem_fresh_of_currentReflection
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hreflect : ∀ (a : Stage kappa) (p : Gamma.DPath) (x : V),
      L.chosen a = some p → Gamma.terminal? p = some x →
      p ∈ Gamma.inessentialPaths (L.warpAt a) →
      ∃ b : Stage kappa, b < a ∧
        p ∈ Gamma.inessentialPaths (L.successorWarp b))
    {a : Stage kappa} (ha : a ∈ L.diagonalEmergenceStages hlegal)
    {p : Gamma.DPath} {x : V} (hpChosen : L.chosen a = some p)
    (hpTerminal : Gamma.terminal? p = some x) :
    a ∈ L.freshInessentialRecordStages := by
  rcases L.diagonalEmergence_fresh_or_currentInessentialWithoutPriorSuccessor
      hlegal ha hpChosen with hfresh | ⟨hpCurrent, hpNoPrior⟩
  · exact hfresh
  · obtain ⟨b, hba, hpEarlier⟩ :=
      hreflect a p x hpChosen hpTerminal hpCurrent
    exact (hpNoPrior b hba hpEarlier).elim

/-- Under finite current-to-prior-successor reflection, full maximal-rung
geometry discharges the finite diagonal classifier: reflection makes the
record fresh, and a fresh finite record forces a hindrance rung. -/
theorem finiteDiagonalEmergenceClassified_of_currentReflection
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hreflect : ∀ (a : Stage kappa) (p : Gamma.DPath) (x : V),
      L.chosen a = some p → Gamma.terminal? p = some x →
      p ∈ Gamma.inessentialPaths (L.warpAt a) →
      ∃ b : Stage kappa, b < a ∧
        p ∈ Gamma.inessentialPaths (L.successorWarp b)) :
    L.FiniteDiagonalEmergenceClassified hlegal := by
  intro a ha p x hpChosen hpTerminal
  have hfresh : a ∈ L.freshInessentialRecordStages :=
    L.diagonalEmergence_finite_mem_fresh_of_currentReflection
      hlegal hreflect ha hpChosen hpTerminal
  exact L.freshInessentialRecord_finite_mem_phiHindrance
    hlegal hfresh hpChosen hpTerminal

/-- The same reflection principle therefore gives the complete diagonal
classification, including the automatic genuinely-new-ray branch. -/
theorem diagonalEmergenceClassified_of_currentReflection
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hreflect : ∀ (a : Stage kappa) (p : Gamma.DPath) (x : V),
      L.chosen a = some p → Gamma.terminal? p = some x →
      p ∈ Gamma.inessentialPaths (L.warpAt a) →
      ∃ b : Stage kappa, b < a ∧
        p ∈ Gamma.inessentialPaths (L.successorWarp b)) :
    L.DiagonalEmergenceClassified hlegal := by
  apply L.diagonalEmergenceClassified_of_finite hlegal
  exact L.finiteDiagonalEmergenceClassified_of_currentReflection
    hlegal hreflect

end KappaLadder
end DWeb
end Erdos599
