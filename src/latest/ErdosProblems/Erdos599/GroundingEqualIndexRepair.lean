/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEmergenceRepair

/-!
# Eliminating the equal-index grounding obstruction

The successor-normalized bookkeeping has two honest emergence cases.  A
selected path either became inessential at a strictly earlier successor rung,
or first became inessential at its own successor rung.  The latter is the
diagonal obstruction classified by the exceptional set.

There is no need to manufacture a strict same-stage chronology in the former
case.  Stationarily many strict-prior records already contradict the assertion
that every successor-inessential family has cardinality below `kappa`: this is
the emergence-fiber pressing-down argument proved in
`GroundingObstructionCharacterization`.  Consequently every equal-subwarp
output of the popularity dichotomy is absorbed by one of the two direct
alternatives of source Lemma 7.27.  The only remaining output is the desired
popular separator.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- The repaired popularity dichotomy with no residual equal-index branch.

The strict-prior branch is absorbed by `largeInessentialStages`: if that set
were empty, all successor-inessential families would be small and the
stationary strict-prior set would contradict the emergence-fiber theorem.  The
diagonal branch was already absorbed by `exceptionalStages` in
`popularAuxiliary_strictPrior_or_exceptionalLarge_or_separator`. -/
theorem popularAuxiliary_exceptionalLarge_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hmono : L.AuxiliaryNonincreasing hL)
    (hclassified : L.DiagonalEmergenceClassified hL.legal) :
    (Stationary.IsStationaryBelow kappa L.exceptionalStages ∨
        L.largeInessentialStages.Nonempty) ∨
      Nonempty (Popular.PopularSeparator
        (L.popularAuxiliaryIndexed hL)) := by
  rcases L.popularAuxiliary_strictPrior_or_exceptionalLarge_or_separator
      hL hmono hclassified with hPrior | hExceptionalLarge | hSeparator
  · left
    right
    by_contra hNoLarge
    have hsmall : ∀ i : Stage kappa,
        #(Gamma.inessentialPaths (L.successorWarp i)) < kappa := by
      intro i
      exact lt_of_not_ge fun hi ↦ hNoLarge ⟨i, hi⟩
    obtain ⟨P, hP⟩ := hPrior
    exact L.strictPriorEmergenceStages_not_stationary_of_all_small
      hL.legal hsmall
        (hP.mono fun _ ha ↦ ha.2.2)
  · exact Or.inl hExceptionalLarge
  · exact Or.inr hSeparator

/-- Regressive-premise wrapper for the equal-index repair. -/
theorem popularAuxiliary_exceptionalLarge_or_separator_of_regressive
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hmono : L.AuxiliaryNonincreasing hL)
    (hreg : Stationary.IsRegressiveOn
      (L.phi \ L.exceptionalStages)
      (L.emergenceIndex hL.legal.validBookkeeping)) :
    (Stationary.IsStationaryBelow kappa L.exceptionalStages ∨
        L.largeInessentialStages.Nonempty) ∨
      Nonempty (Popular.PopularSeparator
        (L.popularAuxiliaryIndexed hL)) :=
  L.popularAuxiliary_exceptionalLarge_or_separator hL hmono
    (L.diagonalEmergenceClassified_of_regressive hL.legal hreg)

/-- Geometric wrapper using the actual successor-corrected form of source
Lemma 7.17.  This is the form consumed by the Section 8 development: the
successor-roof transport supplies weak chronology, while diagonal
classification absorbs exactly the equality case. -/
theorem popularAuxiliary_exceptionalLarge_or_separator_of_successorRoof
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hroof : L.Lemma717SuccessorRoofTransport hL.legal)
    (hclassified : L.DiagonalEmergenceClassified hL.legal) :
    (Stationary.IsStationaryBelow kappa L.exceptionalStages ∨
        L.largeInessentialStages.Nonempty) ∨
      Nonempty (Popular.PopularSeparator
        (L.popularAuxiliaryIndexed hL)) :=
  L.popularAuxiliary_exceptionalLarge_or_separator hL
    (L.auxiliaryNonincreasing_of_successorRoofTransport hL hroof)
    hclassified

/-- Once the two direct Lemma-7.27 alternatives have been discharged, the
popularity argument yields a separator outright; there is no equal-subwarp
case left to switch. -/
theorem popularAuxiliary_separator_of_no_exceptionalLarge
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hmono : L.AuxiliaryNonincreasing hL)
    (hclassified : L.DiagonalEmergenceClassified hL.legal)
    (hNoExceptionalLarge :
      ¬ (Stationary.IsStationaryBelow kappa L.exceptionalStages ∨
        L.largeInessentialStages.Nonempty)) :
    Nonempty (Popular.PopularSeparator
      (L.popularAuxiliaryIndexed hL)) := by
  rcases L.popularAuxiliary_exceptionalLarge_or_separator
      hL hmono hclassified with hExceptionalLarge | hSeparator
  · exact False.elim (hNoExceptionalLarge hExceptionalLarge)
  · exact hSeparator

/-- End-to-end interface for the repaired equality case.  It identifies the
only remaining ambient graph obligations without assuming that a quotient
hindrance or a large inessential family is already an ambient wave. -/
theorem popularAuxiliary_hindrance_or_separator_of_exceptionalLarge
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hmono : L.AuxiliaryNonincreasing hL)
    (hclassified : L.DiagonalEmergenceClassified hL.legal)
    (groundExceptional :
      Stationary.IsStationaryBelow kappa L.exceptionalStages →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (groundLarge : L.largeInessentialStages.Nonempty →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      Nonempty (Popular.PopularSeparator
        (L.popularAuxiliaryIndexed hL)) := by
  rcases L.popularAuxiliary_exceptionalLarge_or_separator
      hL hmono hclassified with
    (hExceptional | hLarge) | hSeparator
  · exact Or.inl (groundExceptional hExceptional)
  · exact Or.inl (groundLarge hLarge)
  · exact Or.inr hSeparator

/-- Successor-roof specialization of the ambient-handler interface. -/
theorem popularAuxiliary_hindrance_or_separator_of_successorRoof
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hroof : L.Lemma717SuccessorRoofTransport hL.legal)
    (hclassified : L.DiagonalEmergenceClassified hL.legal)
    (groundExceptional :
      Stationary.IsStationaryBelow kappa L.exceptionalStages →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (groundLarge : L.largeInessentialStages.Nonempty →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      Nonempty (Popular.PopularSeparator
        (L.popularAuxiliaryIndexed hL)) :=
  L.popularAuxiliary_hindrance_or_separator_of_exceptionalLarge hL
    (L.auxiliaryNonincreasing_of_successorRoofTransport hL hroof)
    hclassified groundExceptional groundLarge

end KappaLadder
end DWeb
end Erdos599
