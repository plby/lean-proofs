/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteInputBreakIntervalDirection
import ErdosProblems.Erdos599.HalfwayClosedClassifiedContactSegmentation

/-!
# Mixed closed-or-classified consecutive compressor pieces

The wholly-closed branch retains its literal forward edges.  The outside
branch applies the endpoint-covered Claim-2 classifier to the concrete
coordinate interval; exact endpoints, cut-interior avoidance, and parent
edge provenance are supplied by the compressor construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath
open _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath}
variable {X before innerRoof outerRoof : Set V}
variable {kappa : Cardinal.{u}}

namespace FiniteBreakMixedPiece

def breakIntervalClosedPiece
    (S : RunCompressor.FiniteInput Gamma.graph) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X))
    (hinside : (S.breakIntervalPath X i).vertexSet ⊆ X) :
    ClosedFiniteContactPiece
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
      (S.finiteWalk.breakPoint X i.castSucc)
      (S.finiteWalk.breakPoint X i.succ) where
  path := S.breakIntervalPath X i
  starts_at := S.breakIntervalPath_initial X i
  ends_at := S.breakIntervalPath_terminal X i
  contained := hinside
  forwardEdges_subset_original :=
    S.breakIntervalPath_directionEdges_subset X i .forward
  vertexSet_subset_original := S.breakIntervalPath_vertexSet_subset X i
  edgeSet_subset_original := S.breakIntervalPath_edgeSet_subset X i

theorem exists_breakIntervalClassifiedPiece
    (S : RunCompressor.FiniteInput Gamma.graph) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X))
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (heligible :
      S.finiteWalk.breakPoint X i.castSucc ∉ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∉ Gamma.vertexSet Y →
      HammockEligible before innerRoof outerRoof
        (S.finiteWalk.breakPoint X i.castSucc)
        (.vertex (S.finiteWalk.breakPoint X i.succ)))
    (hinternal :
      S.finiteWalk.breakPoint X i.castSucc ∉ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∉ Gamma.vertexSet Y →
      InternallySafe Y (S.breakIntervalPath X i))
    (houtside : ¬ (S.breakIntervalPath X i).vertexSet ⊆ X)
    (huX : S.finiteWalk.breakPoint X i.castSucc ∈ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.castSucc ∈ X)
    (hvX : S.finiteWalk.breakPoint X i.succ ∈ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∈ X) :
    Nonempty (ClassifiedFiniteContactPiece
      (Y := Y) (kappa := kappa)
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
      (S.finiteWalk.breakPoint X i.castSucc)
      (S.finiteWalk.breakPoint X i.succ)) := by
  obtain ⟨classification⟩ := classifyFinite hclosed hreferenceClosed
    heligible hinternal (S.breakIntervalPath_initial X i)
    (S.breakIntervalPath_terminal X i)
    (S.breakIntervalPath_hammockInterior_disjoint X i) houtside huX hvX
  exact ⟨{
    path := S.breakIntervalPath X i
    starts_at := S.breakIntervalPath_initial X i
    ends_at := S.breakIntervalPath_terminal X i
    classification := classification
    forwardEdges_subset_original :=
      S.breakIntervalPath_directionEdges_subset X i .forward
    vertexSet_subset_original := S.breakIntervalPath_vertexSet_subset X i
    edgeSet_subset_original := S.breakIntervalPath_edgeSet_subset X i
  }⟩

theorem exists_breakIntervalMixedPiece
    (S : RunCompressor.FiniteInput Gamma.graph) (X : Set V)
    (i : Fin (S.finiteWalk.breakCount X))
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (heligible :
      S.finiteWalk.breakPoint X i.castSucc ∉ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∉ Gamma.vertexSet Y →
      HammockEligible before innerRoof outerRoof
        (S.finiteWalk.breakPoint X i.castSucc)
        (.vertex (S.finiteWalk.breakPoint X i.succ)))
    (hinternal :
      S.finiteWalk.breakPoint X i.castSucc ∉ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∉ Gamma.vertexSet Y →
      InternallySafe Y (S.breakIntervalPath X i))
    (huX : S.finiteWalk.breakPoint X i.castSucc ∈ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.castSucc ∈ X)
    (hvX : S.finiteWalk.breakPoint X i.succ ∈ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∈ X) :
    Nonempty (ClassifiedOrClosedFiniteContactPiece
      (Y := Y) (kappa := kappa)
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
      (S.finiteWalk.breakPoint X i.castSucc)
      (S.finiteWalk.breakPoint X i.succ)) := by
  by_cases hinside : (S.breakIntervalPath X i).vertexSet ⊆ X
  · exact ⟨.closed (breakIntervalClosedPiece S X i hinside)⟩
  · obtain ⟨P⟩ := exists_breakIntervalClassifiedPiece S X i hclosed
      hreferenceClosed heligible hinternal hinside huX hvX
    exact ⟨.classified P⟩

end FiniteBreakMixedPiece
end Erdos599.Blueprint.LinkageBlueprint

#print axioms Erdos599.Blueprint.LinkageBlueprint.FiniteBreakMixedPiece.exists_breakIntervalMixedPiece
