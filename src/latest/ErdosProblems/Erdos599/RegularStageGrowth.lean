/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderConstruction
import ErdosProblems.Erdos599.RegularSplitLegality

/-!
# Growth between two legal ladder stages

The successor and direct-limit clauses of a legal ladder imply the global
pathwise growth relation between any two ordinary stages.  This small lemma
is the chronology input used by the canonical survivor intervals.
-/

noncomputable section

open Cardinal Order

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

/-- Every path at an earlier legal-ladder stage has an extension at every
later stage. -/
theorem warpAt_grows_of_le
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta) :
    Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta) := by
  have hall : ∀ b : Ordinal.{u}, ∀ hb : b < kappa.ord,
      ∀ delta : Ladder.Stage kappa, delta.1 ≤ b →
        Gamma.LadderGrows (L.warpAt delta) (L.warpAt ⟨b, hb⟩) := by
    intro b
    induction b using Ordinal.lt_wf.induction with
    | h b ih =>
      intro hb delta hdeltaBeta
      let beta : Ladder.Stage kappa := ⟨b, hb⟩
      change Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta)
      rcases Ordinal.zero_or_succ_or_isSuccLimit beta.1 with
        hzero | ⟨previous, hprevious⟩ | hlimit
      · have hdelta : delta = beta := by
          apply Subtype.ext
          change b = 0 at hzero
          change delta.1 = b
          apply le_antisymm hdeltaBeta
          rw [hzero]
          exact bot_le
        subst delta
        exact Gamma.ladderGrows_refl _
      · by_cases heq : delta = beta
        · subst delta
          exact Gamma.ladderGrows_refl _
        · have hdeltaLt : delta < beta := lt_of_le_of_ne hdeltaBeta heq
          have hpreviousLt : previous < beta.1 := by
            rw [← hprevious]
            exact Order.lt_succ previous
          let previousStage : Ladder.Stage kappa :=
            ⟨previous, hpreviousLt.trans beta.2⟩
          have hdeltaPrevious : delta ≤ previousStage := by
            apply Subtype.coe_le_coe.1
            change delta.1 < b at hdeltaLt
            change Order.succ previous = b at hprevious
            rw [← hprevious] at hdeltaLt
            exact (Order.lt_succ_iff.mp hdeltaLt)
          have hgrowsPrevious : Gamma.LadderGrows
              (L.warpAt delta) (L.warpAt previousStage) :=
            ih previous hpreviousLt previousStage.2 delta hdeltaPrevious
          have hgrowsSuccessor : Gamma.LadderGrows
              (L.warpAt previousStage) (L.warpAt beta) := by
            intro p hp
            obtain ⟨q, hq, hpq⟩ :=
              hL.successorExtensions previousStage p hp
            refine ⟨q, ?_, hpq⟩
            change q ∈ L.accumulated (Ladder.Stage.toExtended beta)
            change q ∈ L.accumulated
              (Ladder.Stage.succExtended previousStage) at hq
            have hstage : Ladder.Stage.toExtended beta =
                Ladder.Stage.succExtended previousStage := by
              apply Subtype.ext
              change b = previous + 1
              exact hprevious.symm
            rwa [hstage]
          exact DWeb.LadderGrows.trans (G := Gamma)
            hgrowsPrevious hgrowsSuccessor
      · by_cases heq : delta = beta
        · subst delta
          exact Gamma.ladderGrows_refl _
        · have hdeltaLt : delta < beta := lt_of_le_of_ne hdeltaBeta heq
          let deltaBelow : Set.Iio beta.1 := ⟨delta.1, hdeltaLt⟩
          intro p hp
          exact hL.limitStages.grows_to_limit
            (Ladder.Stage.toExtended beta) hlimit deltaBelow p hp
  exact hall beta.1 beta.2 delta hdeltaBeta

#print axioms warpAt_grows_of_le

end CardinalInduction
end Erdos599
