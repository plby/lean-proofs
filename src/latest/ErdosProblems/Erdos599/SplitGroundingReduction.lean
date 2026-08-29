/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingAuxiliary

/-!
# The global reduction of the successor same-stage branch

The successor-normalized ladder has a genuine local same-stage obstruction:
the marker singleton may be selected as an inessential path at the stage at
which it is inserted.  It is therefore unsound to delete that branch from
the local stationary trichotomy.

The split Section 8 auxiliary resolves it globally.  In an equal-index
source--target warp the target marker would have to be the current marker of
the represented record.  But a selected same-stage marker singleton is
inessential in the limiting warp, whereas auxiliary target markers lie on
its essential part.  Thus the equal-index output contains stationary many
grounded records.  This file performs the remaining stationary-set split
and states the exact proposition-level handoff to the unfinished geometric
switching construction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A stationary grounded set splits into stationary many prior-grounded
records or stationary many successor-new grounded records. -/
theorem stationary_prior_or_fresh_of_stationary_phiGround
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround) :
    Stationary.IsStationaryBelow kappa
        L.priorInessentialGroundStages ∨
      Stationary.IsStationaryBelow kappa
        L.freshInessentialGroundStages := by
  rw [L.phiGround_eq_priorInessential_union_freshInessential
    hlegal.validBookkeeping] at hground
  have hcof : Order.cof (Ladder.Stage kappa) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift hlegal.regular]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hlegal.uncountable).ne'
  exact (isStationary_union_iff hcof).mp hground

/-- The weakly chronological split auxiliary has exactly the three global
outputs relevant to Section 8: a prior-grounded stationary obstruction, a
successor-new grounded stationary obstruction, or the popular separator.

In particular there is no same-stage hanging output here.  Its removal is
the global equal-target argument, not a false local provenance assertion. -/
theorem splitPopularAuxiliary_prior_or_fresh_or_separator
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hmono : (L.splitPopularAuxiliaryIndexed hL).Nonincreasing) :
    Stationary.IsStationaryBelow kappa
        L.priorInessentialGroundStages ∨
      Stationary.IsStationaryBelow kappa
          L.freshInessentialGroundStages ∨
        Nonempty
          (Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) := by
  rcases L.splitPopularAuxiliary_groundEqual_or_separator hL hmono with
      ⟨P, hgroundEqual⟩ | hseparator
  · have hground : Stationary.IsStationaryBelow kappa L.phiGround :=
      hgroundEqual.mono (fun _ ha ↦ ha.2)
    rcases L.stationary_prior_or_fresh_of_stationary_phiGround
        hL.legal hground with hprior | hfresh
    · exact Or.inl hprior
    · exact Or.inr (Or.inl hfresh)
  · exact Or.inr (Or.inr hseparator)

/-- Exact handoff from the sound split-ladder/global-auxiliary reduction to
the remaining geometric parts of Section 8.  Unlike the local trichotomy
eliminator, this theorem requires no handler for same-stage records: the
equal-target argument has already converted that possibility to grounded
records. -/
theorem IsSplitKappaHindrance.exists_hindrance_of_globalGroundingOutputs
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hmono : (L.splitPopularAuxiliaryIndexed hL).Nonincreasing)
    (hprior : Stationary.IsStationaryBelow kappa
        L.priorInessentialGroundStages →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (hfresh : Stationary.IsStationaryBelow kappa
        L.freshInessentialGroundStages →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (hseparator : Nonempty
        (Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  rcases L.splitPopularAuxiliary_prior_or_fresh_or_separator hL hmono with
      hpriorStationary | hfreshStationary | hseparatorExists
  · exact hprior hpriorStationary
  · exact hfresh hfreshStationary
  · exact hseparator hseparatorExists

end KappaLadder
end DWeb
end Erdos599
