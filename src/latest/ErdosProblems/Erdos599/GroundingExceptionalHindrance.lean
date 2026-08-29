/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingLemma727Inputs
import ErdosProblems.Erdos599.HindranceGrounding

/-!
# The exceptional alternatives already give a ladder hindrance

The two alternatives in the obstruction characterization have a short,
fully local consequence: each makes the obstruction set stationary and
therefore produces a `kappa`-hindrance.  They do not by themselves provide
an ambient wave.  In particular, a member of `phiHindrance` is a hindrance
in the essential quotient stage `L.stageWeb a`, while the accumulated warp
can contain paths whose initials are earlier marker vertices rather than
vertices of the original source.  Composing such a quotient hindrance with
the accumulated warp is precisely the grounding problem of Section 8.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- A stationary exceptional family is already a stationary family of
obstruction stages.  Normalization is used only for the hindrance-rung
half of `exceptionalStages_subset_phi`. -/
theorem isKappaHindrance_of_exceptionalStages_isStationary
    (L : Gamma.KappaLadder kappa) (hGamma : Gamma.IsNormalized)
    (hlegal : L.IsLegal)
    (hexceptional :
      Stationary.IsStationaryBelow kappa L.exceptionalStages) :
    L.IsKappaHindrance := by
  refine ⟨hlegal, hexceptional.mono ?_⟩
  exact L.exceptionalStages_subset_phi hGamma hlegal

/-- A large successor-inessential family forces an obstruction tail, and
every tail of the regular uncountable stage order is stationary. -/
theorem isKappaHindrance_of_largeInessentialStages_nonempty
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hlarge : L.largeInessentialStages.Nonempty) :
    L.IsKappaHindrance := by
  obtain ⟨a, ha⟩ := hlarge
  letI : Nonempty (Stage kappa) := ⟨a⟩
  have hcof : Order.cof (Stage kappa) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift hlegal.regular]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hlegal.uncountable).ne'
  have htail : Stationary.IsStationaryBelow kappa (Set.Ici a) :=
    (Stationary.isClub_Ici a).isStationary hcof
  refine ⟨hlegal, htail.mono ?_⟩
  exact L.largeInessentialStages_tail_subset_phi hlegal a ha

/-- The stationary exceptional alternative therefore supplies the
stationary grounded records used by the Section 8 construction. -/
theorem phiGround_isStationary_of_exceptionalStages_isStationary
    (L : Gamma.KappaLadder kappa) (hGamma : Gamma.IsNormalized)
    (hlegal : L.IsLegal)
    (hexceptional :
      Stationary.IsStationaryBelow kappa L.exceptionalStages) :
    Stationary.IsStationaryBelow kappa L.phiGround := by
  let hL : L.IsKappaHindrance :=
    L.isKappaHindrance_of_exceptionalStages_isStationary
      hGamma hlegal hexceptional
  exact KappaLadder.IsKappaHindrance.phiGround_isStationary
    L hL hlegal.regular hlegal.uncountable

/-- The large successor-inessential alternative supplies the same
stationary grounded input; no separate ambient-wave shortcut is needed at
the bookkeeping level. -/
theorem phiGround_isStationary_of_largeInessentialStages_nonempty
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hlarge : L.largeInessentialStages.Nonempty) :
    Stationary.IsStationaryBelow kappa L.phiGround := by
  let hL : L.IsKappaHindrance :=
    L.isKappaHindrance_of_largeInessentialStages_nonempty hlegal hlarge
  exact KappaLadder.IsKappaHindrance.phiGround_isStationary
    L hL hlegal.regular hlegal.uncountable

/-- A stationary exceptional set has a stationary hindrance-rung half or
a stationary genuinely-new-ray half.  This is the exact local case split;
neither half changes the ambient grounding obligation. -/
theorem stationary_phiHindrance_or_phiNewRay
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hexceptional :
      Stationary.IsStationaryBelow kappa L.exceptionalStages) :
    Stationary.IsStationaryBelow kappa L.phiHindrance ∨
      Stationary.IsStationaryBelow kappa L.phiNewRay := by
  have hcof : Order.cof (Stage kappa) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift hlegal.regular]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hlegal.uncountable).ne'
  change Stationary.IsStationaryBelow kappa
      (L.phiHindrance ∪ L.phiNewRay) at hexceptional
  exact (isStationary_union_iff hcof).mp hexceptional

/-! ## Exact reductions to the remaining grounding geometry -/

/-- If the limiting ladder warp is already a wave in the original web,
the stationary exceptional alternative produces an ordinary hindrance
immediately.  This is the strongest direct specialization which avoids the
Section 8 switching construction: the latter is needed precisely because a
general limit warp can retain marker-started hanging components. -/
theorem exists_hindrance_of_exceptionalStages_isStationary_of_limitWarp_isWave
    (L : Gamma.KappaLadder kappa) (hGamma : Gamma.IsNormalized)
    (hlegal : L.IsLegal)
    (hexceptional :
      Stationary.IsStationaryBelow kappa L.exceptionalStages)
    (hlimit : Gamma.IsWave L.limitWarp) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  exact L.exists_hindrance_of_limitWarp_isWave
    (L.isKappaHindrance_of_exceptionalStages_isStationary
      hGamma hlegal hexceptional) hlimit

/-- If the limiting ladder warp is already grounded, the large
successor-inessential alternative likewise gives an ordinary hindrance by
essential trimming. -/
theorem exists_hindrance_of_largeInessentialStages_nonempty_of_limitWarp_isWave
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hlarge : L.largeInessentialStages.Nonempty)
    (hlimit : Gamma.IsWave L.limitWarp) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  exact L.exists_hindrance_of_limitWarp_isWave
    (L.isKappaHindrance_of_largeInessentialStages_nonempty
      hlegal hlarge) hlimit

/-- Exact reduction of the exceptional alternative to the output of the
Section 8 grounding construction.  The four fields demanded of `W` are
Assertions 8.18 and 8.22: a warp starting in the original source, with a
separating terminal frontier and an inessential component. -/
theorem exists_hindrance_of_exceptionalStages_isStationary_of_groundingWarp
    (L : Gamma.KappaLadder kappa) (hGamma : Gamma.IsNormalized)
    (hlegal : L.IsLegal)
    (hexceptional :
      Stationary.IsStationaryBelow kappa L.exceptionalStages)
    (hground : L.IsKappaHindrance →
      ∃ W : Set Gamma.DPath,
        Gamma.IsWarp W ∧
        Gamma.initialSet W ⊆ Gamma.source ∧
        Popular.IsSeparator Gamma (Gamma.terminalFrontier W) ∧
        (Gamma.inessentialPaths W).Nonempty) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  let hL : L.IsKappaHindrance :=
    L.isKappaHindrance_of_exceptionalStages_isStationary
      hGamma hlegal hexceptional
  obtain ⟨W, hwarp, hinitial, hseparator, hinessential⟩ := hground hL
  exact exists_hindrance_of_groundingWarp
    hwarp hinitial hseparator hinessential

/-- Exact reduction of the large-inessential alternative to the same
grounding-warp output. -/
theorem exists_hindrance_of_largeInessentialStages_nonempty_of_groundingWarp
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hlarge : L.largeInessentialStages.Nonempty)
    (hground : L.IsKappaHindrance →
      ∃ W : Set Gamma.DPath,
        Gamma.IsWarp W ∧
        Gamma.initialSet W ⊆ Gamma.source ∧
        Popular.IsSeparator Gamma (Gamma.terminalFrontier W) ∧
        (Gamma.inessentialPaths W).Nonempty) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  let hL : L.IsKappaHindrance :=
    L.isKappaHindrance_of_largeInessentialStages_nonempty hlegal hlarge
  obtain ⟨W, hwarp, hinitial, hseparator, hinessential⟩ := hground hL
  exact exists_hindrance_of_groundingWarp
    hwarp hinitial hseparator hinessential

end KappaLadder
end DWeb
end Erdos599
