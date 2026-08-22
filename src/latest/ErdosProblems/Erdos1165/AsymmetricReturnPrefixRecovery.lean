/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricExtractedReturnClockRecovery

namespace Erdos1165.AsymmetricReturnPrefixRecovery

open ThickPoint TerminalSkeletonWords AsymmetricSplitLevelSplice
open AsymmetricExtractedReturnClockRecovery

noncomputable section

attribute [local instance] Classical.propDecidable

@[simp] lemma extractTimedReturnSkeleton_entrancePoint_apply
    (omega : StepPath) (middle inner : Set Point) (horizon q : ℕ)
    (j : Fin q) :
    (extractTimedReturnSkeleton omega (0, 0) middle inner horizon q).entrancePoint j =
      trajectory omega
        ((extractTimedReturnSkeleton omega (0, 0) middle inner horizon q).entrance j) :=
  by
    simp only [extractTimedReturnSkeleton, returnEntrancePoint,
      trajectoryFrom_zero_eq_trajectory]

@[simp] lemma extractTimedReturnSkeleton_exitPoint_apply
    (omega : StepPath) (middle inner : Set Point) (horizon q : ℕ)
    (j : Fin q) :
    (extractTimedReturnSkeleton omega (0, 0) middle inner horizon q).exitPoint j =
      trajectory omega
        ((extractTimedReturnSkeleton omega (0, 0) middle inner horizon q).exit j) :=
  by
    simp only [extractTimedReturnSkeleton, returnExitPoint,
      trajectoryFrom_zero_eq_trajectory]

/-- The generic return extractor depends only on the stopped increment
prefix once all selected returns are complete. -/
theorem compressedReturnData_congr_stoppedPrefix
    {horizon q : ℕ} {middle inner : Set Point} {left right : StepPath}
    (hprefix : ∀ r < horizon, left r = right r)
    (hcomplete : ∀ j : Fin q,
      excursionStart (trajectory left) middle inner horizon (j + 1) ≤ horizon) :
    let leftT := extractTimedReturnSkeleton left (0, 0) middle inner horizon q
    let rightT := extractTimedReturnSkeleton right (0, 0) middle inner horizon q
    compressTimedSkeleton left leftT = compressTimedSkeleton right rightT ∧
      intervalWords left leftT.entrance leftT.exit =
        intervalWords right rightT.entrance rightT.exit := by
  classical
  dsimp only
  let leftT := extractTimedReturnSkeleton left (0, 0) middle inner horizon q
  let rightT := extractTimedReturnSkeleton right (0, 0) middle inner horizon q
  have htraj : ∀ r ≤ horizon, trajectory left r = trajectory right r := by
    intro r hr
    exact trajectory_congr_of_incrementPrefix hprefix hr
  have hentrance : ∀ j : Fin q, leftT.entrance j = rightT.entrance j := by
    intro j
    simpa [leftT, rightT, extractTimedReturnSkeleton, returnEntranceTime,
      trajectoryFrom_zero_eq_trajectory] using
      excursionFinish_congr_prefix htraj middle inner (j : ℕ)
  have hexit : ∀ j : Fin q, leftT.exit j = rightT.exit j := by
    intro j
    simpa [leftT, rightT, extractTimedReturnSkeleton, returnExitTime,
      trajectoryFrom_zero_eq_trajectory] using
      excursionStart_congr_prefix htraj middle inner ((j : ℕ) + 1)
  have hwell : leftT.WellFormed := by
    apply extractTimedReturnSkeleton_wellFormed
    simpa only [trajectoryFrom_zero_eq_trajectory] using hcomplete
  have hexitLe : ∀ j : Fin q, leftT.exit j ≤ horizon := by
    intro j
    simpa [leftT, extractTimedReturnSkeleton, returnExitTime,
      trajectoryFrom_zero_eq_trajectory] using hcomplete j
  have hentranceLe : ∀ j : Fin q, leftT.entrance j ≤ horizon := by
    intro j
    exact (hwell.1 j).1.trans (hexitLe j)
  have hentrancePoint : leftT.entrancePoint = rightT.entrancePoint := by
    funext j
    have hp := htraj (leftT.entrance j) (hentranceLe j)
    simpa only [leftT, rightT,
      extractTimedReturnSkeleton_entrancePoint_apply, ← hentrance j] using hp
  have hexitPoint : leftT.exitPoint = rightT.exitPoint := by
    funext j
    have hp := htraj (leftT.exit j) (hexitLe j)
    simpa only [leftT, rightT,
      extractTimedReturnSkeleton_exitPoint_apply, ← hexit j] using hp
  have hentranceFun : leftT.entrance = rightT.entrance := by
    funext j
    exact hentrance j
  have hexitFun : leftT.exit = rightT.exit := by
    funext j
    exact hexit j
  constructor
  · unfold compressTimedSkeleton
    apply Prod.ext
    · apply TerminalSkeletonData.ext
      rw [hentranceFun, hexitFun]
      exact complementaryPieces_congr q rightT.entrance rightT.exit hprefix
        le_rfl (fun j ↦ by rw [← hentrance j]; exact hentranceLe j)
    · exact Prod.ext hentrancePoint hexitPoint
  · funext j
    unfold intervalWords
    rw [hentrance j, hexit j]
    exact incrementSlice_congr hprefix
      (by rw [← hexit j]; exact hexitLe j)

end

end Erdos1165.AsymmetricReturnPrefixRecovery
