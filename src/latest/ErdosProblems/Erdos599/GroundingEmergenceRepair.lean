/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingObstructionCharacterization

/-!
# Emergence-index repair for successor-normalized grounding

`GroundingObstructionCharacterization` gives the exact source-faithful
partition of the successor-normalized obstruction set into strict-prior and
diagonal emergence.  This file integrates that partition into the indexed
popularity argument.

The output never asserts unconditional strict descent.  A stationary equal
subwarp has either stationarily many grounded strict-prior records, to which
the old/current-inessential roof lemmas apply, or stationarily many diagonal
records.  The latter is sent to the exceptional alternative of source Lemma
7.27 by `DiagonalEmergenceClassified`.  Once the exceptional and
large-inessential alternatives have been discharged, the only outputs are
the strict-prior grounding branch and the popular separator.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- The regressive premise of source Lemma 7.27 is an equivalent convenient
way to supply the local diagonal-classification fact. -/
theorem diagonalEmergenceClassified_of_regressive
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hreg : Stationary.IsRegressiveOn
      (L.phi \ L.exceptionalStages)
      (L.emergenceIndex hlegal.validBookkeeping)) :
    L.DiagonalEmergenceClassified hlegal := by
  intro a ha
  by_contra hnotExceptional
  have hlt : L.emergenceIndex hlegal.validBookkeeping a < a :=
    hreg a ⟨ha.1, hnotExceptional⟩
  exact (ne_of_lt hlt) ha.2

/-- A genuinely successor-new chosen record belongs to the diagonal
emergence class.  It is not assigned a fabricated strict inequality. -/
theorem freshInessentialRecordStages_subset_diagonalEmergenceStages
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    L.freshInessentialRecordStages ⊆
      L.diagonalEmergenceStages hlegal := by
  intro a ha
  exact ⟨ha.1,
    L.emergenceIndex_eq_self_of_freshInessentialRecord hlegal ha⟩

/-- Literal source-Lemma-7.27 nonstationarity route.  If neither a
stationary exceptional family nor a large successor-inessential family
exists, a stationary diagonal family would make `phi` stationary and
contradict Lemma 7.27. -/
theorem diagonalEmergenceStages_not_stationary_of_no_exceptionalLarge
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hexceptional : L.exceptionalStages ⊆ L.phi)
    (hreg : Stationary.IsRegressiveOn
      (L.phi \ L.exceptionalStages)
      (L.emergenceIndex hlegal.validBookkeeping))
    (htail : ∀ a ∈ L.largeInessentialStages, Set.Ici a ⊆ L.phi)
    (hNoExceptionalLarge :
      ¬ (Stationary.IsStationaryBelow kappa L.exceptionalStages ∨
        L.largeInessentialStages.Nonempty)) :
    ¬ Stationary.IsStationaryBelow kappa
      (L.diagonalEmergenceStages hlegal) := by
  intro hDiagonal
  have hPhi : Stationary.IsStationaryBelow kappa L.phi :=
    hDiagonal.mono (by
      intro a ha
      exact ha.1)
  exact hNoExceptionalLarge
    ((L.stationary_phi_iff_exceptional_or_large hlegal.regular
      hlegal.uncountable hlegal hexceptional hreg htail).1 hPhi)

/-- A stationary equal-index auxiliary warp retains a stationary exact
emergence branch after hanging records are removed.  Only the first output
is a valid input to strict ordinal descent. -/
theorem equalSubwarp_strictPrior_or_diagonalGround_isStationary
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) :
    Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          (L.phiGround ∩ L.strictPriorEmergenceStages hL.legal)) ∨
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          (L.phiGround ∩ L.diagonalEmergenceStages hL.legal)) := by
  let E : Set (Stage kappa) :=
    Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source
  have hGround : Stationary.IsStationaryBelow kappa (E ∩ L.phiGround) :=
    L.equalSubwarp_grounded_initialIndices_isStationary hL P hstat
  have hSplit : E ∩ L.phiGround =
      (E ∩ (L.phiGround ∩ L.strictPriorEmergenceStages hL.legal)) ∪
        (E ∩ (L.phiGround ∩ L.diagonalEmergenceStages hL.legal)) := by
    calc
      E ∩ L.phiGround =
          E ∩ ((L.phiGround ∩ L.strictPriorEmergenceStages hL.legal) ∪
            (L.phiGround ∩ L.diagonalEmergenceStages hL.legal)) :=
        congrArg (fun X : Set (Stage kappa) ↦ E ∩ X)
          (L.phiGround_eq_strictPriorEmergence_union_diagonalEmergence
            hL.legal)
      _ = (E ∩ (L.phiGround ∩ L.strictPriorEmergenceStages hL.legal)) ∪
          (E ∩ (L.phiGround ∩ L.diagonalEmergenceStages hL.legal)) :=
        Set.inter_union_distrib_left E _ _
  rw [hSplit] at hGround
  have hcof : Order.cof (Stage kappa) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift hL.legal.regular]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hL.legal.uncountable).ne'
  exact (isStationary_union_iff hcof).mp hGround

/-- Repaired popularity output before the two direct alternatives of
source Lemma 7.27 are discarded.  The first branch contains only records
with genuinely strict prior emergence. -/
theorem popularAuxiliary_strictPrior_or_exceptionalLarge_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hmono : L.AuxiliaryNonincreasing hL)
    (hclassified : L.DiagonalEmergenceClassified hL.legal) :
    (∃ P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          (L.phiGround ∩ L.strictPriorEmergenceStages hL.legal))) ∨
      (Stationary.IsStationaryBelow kappa L.exceptionalStages ∨
        L.largeInessentialStages.Nonempty) ∨
      Nonempty (Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) := by
  rcases L.popularAuxiliary_equal_or_separator hL hmono with
      hEqual | hSeparator
  · obtain ⟨P, hP⟩ := hEqual
    rcases L.equalSubwarp_strictPrior_or_diagonalGround_isStationary
        hL P hP with hPrior | hDiagonal
    · exact Or.inl ⟨P, hPrior⟩
    · right
      left
      left
      exact hDiagonal.mono (by
        intro a ha
        exact hclassified ha.2.2)
  · exact Or.inr (Or.inr hSeparator)

/-- Regressive-premise wrapper for the repaired popularity output. -/
theorem popularAuxiliary_strictPrior_or_exceptionalLarge_or_separator_of_regressive
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hmono : L.AuxiliaryNonincreasing hL)
    (hreg : Stationary.IsRegressiveOn
      (L.phi \ L.exceptionalStages)
      (L.emergenceIndex hL.legal.validBookkeeping)) :
    (∃ P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          (L.phiGround ∩ L.strictPriorEmergenceStages hL.legal))) ∨
      (Stationary.IsStationaryBelow kappa L.exceptionalStages ∨
        L.largeInessentialStages.Nonempty) ∨
      Nonempty (Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :=
  L.popularAuxiliary_strictPrior_or_exceptionalLarge_or_separator hL hmono
    (L.diagonalEmergenceClassified_of_regressive hL.legal hreg)

/-- After both direct Lemma-7.27 alternatives have been excluded, only
the strict-prior grounding branch or the desired popular separator remains. -/
theorem popularAuxiliary_strictPrior_or_separator_of_no_exceptionalLarge
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (hmono : L.AuxiliaryNonincreasing hL)
    (hclassified : L.DiagonalEmergenceClassified hL.legal)
    (hNoExceptionalLarge :
      ¬ (Stationary.IsStationaryBelow kappa L.exceptionalStages ∨
        L.largeInessentialStages.Nonempty)) :
    (∃ P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
          (L.phiGround ∩ L.strictPriorEmergenceStages hL.legal))) ∨
      Nonempty (Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) := by
  rcases L.popularAuxiliary_strictPrior_or_exceptionalLarge_or_separator
      hL hmono hclassified with hPrior | hExceptionalLarge | hSeparator
  · exact Or.inl hPrior
  · exact False.elim (hNoExceptionalLarge hExceptionalLarge)
  · exact Or.inr hSeparator

end KappaLadder
end DWeb
end Erdos599
