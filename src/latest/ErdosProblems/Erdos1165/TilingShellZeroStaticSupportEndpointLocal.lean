/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingPrefixedRaisedRankAcceptedCreationEndpoint
import ErdosProblems.Erdos1165.TilingShellZeroStaticSupportCoarseBridge

/-!
# Final local-time invariance for the static shell carrier

The physical endpoint is independent of insertion totals.  Its source domino
is in `V₁`, hence it is not one of the static `V₂(I₁)` moved dominos.  If it is
represented it belongs to the distinguished complement; if it is not
represented its local time is insertion-independent.  Both cases give the
endpoint-local-time identity needed by the source-correct raised-rank clock.
-/

namespace Erdos1165.TilingShellZeroStaticSupportEndpointLocal

open HLOZShellZeroReplacementWindows LazyDecomposition
open PathInsertion PreStoppingFiber PreStoppingSpatialLaw
open SpatialInsertionFiber StoppedInsertion
open VariableStoppedFiber
open TilingCappedMarginalization TilingDistinguishedTraceInvariant
open TilingInsertedLocalTime TilingLazyDecomposition
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime TilingShellZeroSourcePartition
open TilingShellZeroStaticSupportCoarseBridge TilingSpatialInsertionFiber
open TilingPrefixedStoppedProductDisintegration

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem sourceVTwo_not_vOne
    {t : DominoTiling} {m w : ℕ} {s : WalkPath} {n : ℕ} {b : Point}
    (hVTwo : tilingVTwoAt t (shellZeroSourceTotalWindow m w) s n b) :
    ¬tilingVOneAt t m s n b := by
  have hbaseLt := (mem_shellZeroSourceTotalWindow.mp hVTwo.2).2
  have hpartnerLt : localTime s n (tilingPartner t b) < m :=
    lt_of_le_of_lt hVTwo.1 hbaseLt
  unfold tilingVOneAt
  omega

/-- Same distinguished projection gives the same final local time even when
the common physical endpoint is the unrepresented one-step tail. -/
theorem prefixedTilingFinalLocalTime_eq_of_staticSourceSupport
    (initial : BoundaryTail) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (tail : BoundaryTail) (S : Finset Point)
    (q q' : TilingCappedCoordinates i cap)
    (hstart : trajectory
      (extendPrefix (directionVectorOfList initial.1)) initial.1.length = x)
    (hdist : (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) q).1 =
      (splitTilingCoordinatesEquiv t x r
        (tilingExternalDominoBases t x r \ S) q').1)
    (hsource :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      ∀ b ∈ S,
        tilingVTwoAt t (shellZeroSourceTotalWindow m w) s v.length b)
    (hterminalVOne :
      let v := prefixedTilingInsertionPrefixList initial.1 t x r
        (fun j ↦ (q j : ℕ)) tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingVOneAt t m s v.length (tilingBase t (s v.length))) :
    let v := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q j : ℕ)) tail.1
    let v' := prefixedTilingInsertionPrefixList initial.1 t x r
      (fun j ↦ (q' j : ℕ)) tail.1
    let s := trajectory (extendPrefix (directionVectorOfList v))
    let s' := trajectory (extendPrefix (directionVectorOfList v'))
    localTime s v.length (s v.length) =
      localTime s' v'.length (s' v'.length) := by
  classical
  let D := tilingExternalDominoBases t x r \ S
  let v := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q j : ℕ)) tail.1
  let v' := prefixedTilingInsertionPrefixList initial.1 t x r
    (fun j ↦ (q' j : ℕ)) tail.1
  let s := trajectory (extendPrefix (directionVectorOfList v))
  let s' := trajectory (extendPrefix (directionVectorOfList v'))
  let terminal := prefixedTilingInsertionTerminal initial t x r
    (fun j ↦ (q j : ℕ)) tail
  have hterminal' : prefixedTilingInsertionTerminal initial t x r
      (fun j ↦ (q' j : ℕ)) tail = terminal :=
    (prefixedTilingInsertionTerminal_eq_of_coordinates
      initial t x r (fun j ↦ (q j : ℕ)) (fun j ↦ (q' j : ℕ)) tail
        hstart).symm
  have hpath : finitePathList (pathPrefix s v.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal := by
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r (fun j ↦ (q j : ℕ)) tail hstart
  have hpath' : finitePathList (pathPrefix s' v'.length) =
      prefixedTilingPrefixPointPath initial.1 x
        (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal := by
    rw [← hterminal']
    exact finitePathList_prefixedTilingInsertionPrefix
      initial t x r (fun j ↦ (q' j : ℕ)) tail hstart
  have hend : s v.length = s' v'.length :=
    prefixedTilingInsertionEndpoint_eq_of_coordinates
      initial t x r (fun j ↦ (q j : ℕ)) (fun j ↦ (q' j : ℕ)) tail hstart
  let b := tilingBase t (s v.length)
  have hbNotS : b ∉ S := by
    intro hbS
    exact sourceVTwo_not_vOne (hsource b hbS) hterminalVOne
  have hlist : listLocalTime
        (prefixedTilingPrefixPointPath initial.1 x
          (tilingInsertGapVector t x r (fun j ↦ (q j : ℕ))) terminal)
        (s v.length) =
      listLocalTime
        (prefixedTilingPrefixPointPath initial.1 x
          (tilingInsertGapVector t x r (fun j ↦ (q' j : ℕ))) terminal)
        (s v.length) := by
    by_cases hbExternal : b ∈ tilingExternalDominoBases t x r
    · have hbD : b ∈ D := by
        exact Finset.mem_sdiff.mpr ⟨hbExternal, hbNotS⟩
      apply prefixedTilingPrefixLocalTime_eq_of_distinguished_eq
        initial.1 t x r terminal D q q'
      · simpa only [D] using hdist
      · exact hbD
    · rw [prefixedTilingInsertedPrefix_localTime_of_base_not_mem
          initial.1 t x r (fun j ↦ (q j : ℕ)) terminal (s v.length),
        prefixedTilingInsertedPrefix_localTime_of_base_not_mem
          initial.1 t x r (fun j ↦ (q' j : ℕ)) terminal (s v.length)]
      · exact hbExternal
      · exact hbExternal
  change localTime s v.length (s v.length) =
    localTime s' v'.length (s' v'.length)
  rw [← hend, localTime_eq_listLocalTime, localTime_eq_listLocalTime,
    hpath, hpath']
  exact hlist

end

end Erdos1165.TilingShellZeroStaticSupportEndpointLocal
