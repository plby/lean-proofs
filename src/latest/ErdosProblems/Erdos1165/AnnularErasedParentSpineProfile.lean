/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularErasedParentSpine
import ErdosProblems.Erdos1165.TerminalProfileBoundarySeparation

/-!
# Profile-boundary specialization of the erased parent spine

This file discharges the geometric side conditions of
`absoluteBoundaryFirstAt_boundaryExitWords_complementaryPieces_from` for
one HLOZ profile annulus.  The retained parent first hits the boundary at
level `k - 1`; every reinserted child is a canonical first hit of the
boundary at level `k` and stays in the intervening profile disc.
-/

open Set

namespace Erdos1165.AnnularErasedParentSpineProfile

open AnnularErasedParentSpine AnnularProfileClocks
open MarkedBridgeFactorization TerminalProfileBoundarySeparation
open TerminalSequentialVisitLaw TerminalSpliceProfileGeometry
open TerminalSkeletonInvariance TerminalSkeletonWords ThickPoint

noncomputable section

/-- Profile specialization when membership of every child entrance in the
level-`k` disc is already available. -/
theorem absoluteBoundaryFirstAt_profileBoundaryExitWords
    {m n k : ℕ} {center origin : Point} {omega : StepPath}
    {horizon : ℕ} {t : TimedTerminalSkeleton m}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k ≤ n + 1)
    (ht : t.WellFormed)
    (hfirst : AbsoluteBoundaryFirstAt
      (profileOuterBoundary n k center) origin omega horizon)
    (hhorizon : t.horizon = horizon)
    (hentranceMem : ∀ j,
      t.entrancePoint j ∈ disc center (scaleRadius n k))
    (bridges : (j : Fin m) →
      BoundaryExitWordCode (profileInnerBoundary n k center)
        (t.entrancePoint j) (t.exitPoint j))
    (hentrancePoint : ∀ j, t.entrancePoint j =
      PlanarPotential.trajectoryFrom origin omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j =
      PlanarPotential.trajectoryFrom origin omega (t.exit j)) :
    AbsoluteBoundaryFirstAt (profileOuterBoundary n k center) origin
      (assembledTerminalPath (compressTimedSkeleton omega t)
        (fun j ↦ List.ofFn (bridges j).1.2))
      (assembledTerminalHorizon (compressTimedSkeleton omega t)
        (fun j ↦ List.ofFn (bridges j).1.2)) := by
  apply absoluteBoundaryFirstAt_boundaryExitWords_complementaryPieces_from
    (B := profileOuterBoundary n k center)
    (D := disc center (scaleRadius n k))
    ht hfirst hhorizon
  · intro z hzD hzOuter
    apply (not_mem_discBoundary_of_mem_disc_of_add_one_le hzD
      (scaleRadius_add_one_le_previous hn hk0 hk))
    simpa only [profileOuterBoundary] using hzOuter
  · exact hentranceMem
  · exact hentrancePoint
  · exact hexitPoint

/-- Recursive form: entrances on the next profile boundary automatically
belong to the parent level-`k` disc. -/
theorem absoluteBoundaryFirstAt_profileChildBoundaryExitWords
    {m n k : ℕ} {center origin : Point} {omega : StepPath}
    {horizon : ℕ} {t : TimedTerminalSkeleton m}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (ht : t.WellFormed)
    (hfirst : AbsoluteBoundaryFirstAt
      (profileOuterBoundary n k center) origin omega horizon)
    (hhorizon : t.horizon = horizon)
    (hentranceInner : ∀ j,
      t.entrancePoint j ∈ profileInnerBoundary n (k + 1) center)
    (bridges : (j : Fin m) →
      BoundaryExitWordCode (profileInnerBoundary n k center)
        (t.entrancePoint j) (t.exitPoint j))
    (hentrancePoint : ∀ j, t.entrancePoint j =
      PlanarPotential.trajectoryFrom origin omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j =
      PlanarPotential.trajectoryFrom origin omega (t.exit j)) :
    AbsoluteBoundaryFirstAt (profileOuterBoundary n k center) origin
      (assembledTerminalPath (compressTimedSkeleton omega t)
        (fun j ↦ List.ofFn (bridges j).1.2))
      (assembledTerminalHorizon (compressTimedSkeleton omega t)
        (fun j ↦ List.ofFn (bridges j).1.2)) := by
  apply absoluteBoundaryFirstAt_profileBoundaryExitWords
    hn hk0 (by omega : k ≤ n + 1) ht hfirst hhorizon
  · intro j
    exact (hentranceInner j).1.trans
      (scaleRadius_antitone_of_le (by omega : k ≤ k + 1) hk)
  · exact hentrancePoint
  · exact hexitPoint

end

end Erdos1165.AnnularErasedParentSpineProfile
