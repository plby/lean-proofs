/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedAllCreationConcreteFamily

/-!
# Oriented external codes of reconstructed prefixed insertion words

The retained external code is independent of insertion multiplicities.  This
file exposes that fact from the two literal physical-prefix normalizations;
it does not mention a stopping event or a probability estimate.
-/

namespace Erdos1165.TilingOrientedPrefixedInsertionCode

open LazyDecomposition PathInsertion PreStoppingFiber SpatialInsertionFiber
open StoppedInsertion
open TilingInsertedLocalTime
open TilingLazyDecomposition TilingOrientedAllCreationConcreteFamily
open TilingOrientedShellZeroSourcePartition TilingSpatialInsertionFiber
open TilingPrefixedStoppedProductDisintegration
open VariableStoppedTracePartition
open VariableStoppedFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem orientedExternalCode_eq_of_lists
    {t : DominoTiling} (z z' : OrientedTilingTypedExternalWordCode t)
    (hinitial : z.initial.1 = z'.initial.1)
    (hretained : List.ofFn z.retained.1 = List.ofFn z'.retained.1)
    (htail : z.tail.1 = z'.tail.1) : z = z' := by
  rcases z with ⟨initial, i, r, tail⟩
  rcases z' with ⟨initial', i', r', tail'⟩
  have hi : initial = initial' := Subtype.ext hinitial
  subst initial'
  have hii : i = i' := by
    simpa using congrArg List.length hretained
  subst i'
  have hr : r = r' := by
    apply Subtype.ext
    exact List.ofFn_injective hretained
  subst r'
  have ht : tail = tail' := Subtype.ext htail
  subst tail'
  rfl

private theorem fixedCode_even_prefixedInsertion
    {t : DominoTiling} (z : OrientedTilingTypedExternalWordCode t)
    (hinitial : z.initial.1 = [])
    (q : Fin (z.retainedCount + 1) → ℕ) :
    let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start
      z.retained q z.tail.1
    fixedOrientedTypedExternalWordCode t .even v.length
        (trajectory (extendPrefix (directionVectorOfList v))) = z := by
  rcases z with ⟨initial, i, r, tail⟩
  have hi : initial = (⟨[], by simp⟩ : BoundaryTail) := by
    apply Subtype.ext
    exact hinitial
  subst initial
  let v := prefixedTilingInsertionPrefixList [] t
    (trajectory (extendPrefix (directionVectorOfList [])) 0) r q tail.1
  have hinc : incrementPrefixList v.length
      (stepsOfWalk (trajectory
        (extendPrefix (directionVectorOfList v)))) = v := by
    unfold incrementPrefixList
    rw [stepsOfWalk_trajectory, stepPrefix_extendPrefix,
      ofFn_directionVectorOfList]
  change fixedOrientedTypedExternalWordCode t .even v.length
      (trajectory (extendPrefix (directionVectorOfList v))) = _
  rw [fixedOrientedTypedExternalWordCode_eq_ofPrefix, hinc]
  unfold orientedTypedExternalWordCodeOfPrefix
  dsimp only
  have hpairs : pairDirectionList v = tilingInsertGapVector t
      (trajectory (extendPrefix (directionVectorOfList [])) 0) r q := by
    unfold v prefixedTilingInsertionPrefixList tilingInsertionPrefixList
    simp only [List.nil_append]
    exact pairDirectionList_flatten_append_shortTail _ tail.1 tail.2
  simp only [List.length_nil]
  rw [hpairs]
  apply orientedExternalCode_eq_of_lists
  · rfl
  · simp only [TilingTypedFavoriteTrace.deletedTilingRetainedWord,
      List.ofFn_get]
    exact deleteTilingBlocks_tilingInsertGapVector _ _ _ _
  · unfold v prefixedTilingInsertionPrefixList tilingInsertionPrefixList
    simp only [List.nil_append]
    exact unpairedDirectionTail_flatten_append_shortTail _ tail.1 tail.2

private theorem fixedCode_shifted_prefixedInsertion
    {t : DominoTiling} (z : OrientedTilingTypedExternalWordCode t)
    (hinitial : z.initial.1.length = 1)
    (q : Fin (z.retainedCount + 1) → ℕ) :
    let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start
      z.retained q z.tail.1
    fixedOrientedTypedExternalWordCode t .shifted v.length
        (trajectory (extendPrefix (directionVectorOfList v))) = z := by
  rcases z with ⟨initial, i, r, tail⟩
  obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp hinitial
  have hi : initial = (⟨[d], by simp⟩ : BoundaryTail) := by
    apply Subtype.ext
    exact hd
  subst initial
  let suffix := tilingInsertionPrefixList t
    (trajectory (extendPrefix (directionVectorOfList [d])) 1) r q tail.1
  let v := [d] ++ suffix
  have hinc : incrementPrefixList v.length
      (stepsOfWalk (trajectory
        (extendPrefix (directionVectorOfList v)))) = v := by
    unfold incrementPrefixList
    rw [stepsOfWalk_trajectory, stepPrefix_extendPrefix,
      ofFn_directionVectorOfList]
  change fixedOrientedTypedExternalWordCode t .shifted v.length
      (trajectory (extendPrefix (directionVectorOfList v))) = _
  rw [fixedOrientedTypedExternalWordCode_eq_ofPrefix, hinc]
  unfold orientedTypedExternalWordCodeOfPrefix
  dsimp only
  have htake : v.take 1 = [d] := by simp [v]
  have hdrop : v.drop 1 = suffix := by simp [v]
  have hpairs : pairDirectionList (v.drop 1) = tilingInsertGapVector t
      (trajectory (extendPrefix (directionVectorOfList [d])) 1) r q := by
    rw [hdrop]
    unfold suffix tilingInsertionPrefixList
    exact pairDirectionList_flatten_append_shortTail _ tail.1 tail.2
  apply orientedExternalCode_eq_of_lists
  · exact htake
  · simp only [TilingTypedFavoriteTrace.deletedTilingRetainedWord,
      List.ofFn_get]
    simp only [htake, List.length_singleton]
    rw [hpairs]
    exact deleteTilingBlocks_tilingInsertGapVector _ _ _ _
  · rw [hdrop]
    unfold suffix tilingInsertionPrefixList
    exact unpairedDirectionTail_flatten_append_shortTail _ tail.1 tail.2

/-- The physical even/shifted normalization is sufficient to reconstruct
the exact oriented retained external code for every insertion vector. -/
theorem fixedOrientedTypedExternalWordCode_prefixedInsertion
    {t : DominoTiling} (o : Orientation)
    (z : OrientedTilingTypedExternalWordCode t)
    (horientation : match o with
      | .even => z.initial.1 = []
      | .shifted => z.initial.1.length = 1)
    (q : Fin (z.retainedCount + 1) → ℕ) :
    let v := prefixedTilingInsertionPrefixList z.initial.1 t z.start
      z.retained q z.tail.1
    fixedOrientedTypedExternalWordCode t o v.length
        (trajectory (extendPrefix (directionVectorOfList v))) = z := by
  cases o with
  | even => exact fixedCode_even_prefixedInsertion z horientation q
  | shifted => exact fixedCode_shifted_prefixedInsertion z horientation q

end

end Erdos1165.TilingOrientedPrefixedInsertionCode
