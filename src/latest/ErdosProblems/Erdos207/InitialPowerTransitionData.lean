/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPowerVortexPackage
import ErdosProblems.Erdos207.MasterOutsidePairSurvival
import ErdosProblems.Erdos207.OuterOnlyPreliminaryGeometry

/-!
# Initial transition data for the power vortex

The initial power-vortex package contains the typicality needed to start the
outer-only preliminary process.  This file turns that typicality into the
three structural invariants used by the first scheduled transition.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

/-- The level-zero typical state of an initial power-vortex package can be
reinitialized on the triangles that meet the first inner vortex set.  The
resulting state has the absorber-greedy invariant, keeps every required
outside pair alive, and has no triangle selected yet. -/
theorem InitialPowerVortexPackage.initialOuterOnlyReady
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (hh : 2 ≤ h)
    (hgap : ((((P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card + 2 : ℕ) : ℝ≥0) <
      (1 - (t : ℝ≥0)⁻¹) *
        ((1 : ℝ≥0) ^ 2 * 1 *
          (P.W.U ((⟨0, hell⟩ : Fin ell).castSucc)).card))) :
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let A := (absorberGreedyInitialState F
      (outsideAvailableTriangles P.H P.B)).available
    let i : Fin ell := ⟨0, hell⟩
    let S₀ := absorberGreedyInitialState F
      (outerOnlyAvailable (P.W.U i.succ) A)
    AbsorberGreedyInvariant F (outerOnlyAvailable (P.W.U i.succ) A) S₀ ∧
      OutsideLeavePairsAlive
        (internalOuterGraph G (P.W.U i.succ))ᶜ (P.W.U i.succ) S₀ ∧
      S₀.chosen = ∅ := by
  dsimp only
  let F := absorberErdosForbiddenConfigurationsOn q P.B
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let A := (absorberGreedyInitialState F
    (outsideAvailableTriangles P.H P.B)).available
  let i : Fin ell := ⟨0, hell⟩
  have hpoint : IsMasterStagePointwiseGood P.W 0 F G A
      ∅ ∅ 1 1 (t : ℝ≥0)⁻¹ h := by
    simpa only [F, G, A] using
      initialMasterStagePointwiseGood_of_typical P.typical
  have hInv : GreedyInvariant F
      (relativePreliminaryInitialState ∅ A) :=
    greedyInvariant_relativePreliminaryInitialState_of_masterPointwiseGood
      hpoint
  have hUzero : P.W.U 0 = univ := by
    rw [P.vortex_eq]
    exact separatedCardinalVortex_U_zero P.H P.X P.B
      (powerFreeSize t step ell)
      (powerFreeSize_antitone t step ell P.base_ge_one)
  have hsupport : GraphSupportedOn G (P.W.U i.castSucc : Set (Fin n)) := by
    have hi : i.castSucc = (0 : Fin (ell + 1)) := by
      ext
      rfl
    rw [hi, hUzero]
    intro u v _huv
    simp
  exact P.typical.absorberGreedyInitialState_outerOnly_ready
    i (by simp [i]) hsupport hh hgap hInv
      (fun _S hS ↦ absorberErdosForbidden_nonempty hS)

end

end Erdos207
