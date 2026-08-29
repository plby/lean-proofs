/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteBreakMixedPiece
import ErdosProblems.Erdos599.HalfwayFiniteBreakExact

/-!
# Exact finite closed/classified contact segmentation

Every consecutive break interval is constructed from the literal compressor
coordinates.  Wholly closed intervals take the closed branch; every other
interval is classified by the endpoint-covered Claim-2 theorem.  The exact
coordinate coverage theorems show that no vertex or edge of the assigned
trace is lost.
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

theorem exists_finiteClosedClassifiedContactSegmentation_with_points
    (S : RunCompressor.FiniteInput Gamma.graph) (X : Set V)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (heligible : ∀ i : Fin (S.finiteWalk.breakCount X),
      S.finiteWalk.breakPoint X i.castSucc ∉ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∉ Gamma.vertexSet Y →
      HammockEligible before innerRoof outerRoof
        (S.finiteWalk.breakPoint X i.castSucc)
        (.vertex (S.finiteWalk.breakPoint X i.succ)))
    (hinternal : ∀ i : Fin (S.finiteWalk.breakCount X),
      S.finiteWalk.breakPoint X i.castSucc ∉ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∉ Gamma.vertexSet Y →
      InternallySafe Y (S.breakIntervalPath X i))
    (huX : ∀ i : Fin (S.finiteWalk.breakCount X),
      S.finiteWalk.breakPoint X i.castSucc ∈ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.castSucc ∈ X)
    (hvX : ∀ i : Fin (S.finiteWalk.breakCount X),
      S.finiteWalk.breakPoint X i.succ ∈ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∈ X) :
    ∃ D : FiniteClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa)
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X,
      ∃ hcount : D.count = S.finiteWalk.breakCount X,
        ∀ i, D.point i = S.finiteWalk.breakPoint X
          (Fin.cast (congrArg (fun n : Nat ↦ n + 1) hcount) i) := by
  classical
  let piece : (i : Fin (S.finiteWalk.breakCount X)) →
      ClassifiedOrClosedFiniteContactPiece
        (Y := Y) (kappa := kappa)
        (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
        (S.finiteWalk.breakPoint X i.castSucc)
        (S.finiteWalk.breakPoint X i.succ) := fun i =>
    if hinside : (S.breakIntervalPath X i).vertexSet ⊆ X then
      .closed (breakIntervalClosedPiece S X i hinside)
    else
      .classified {
        path := S.breakIntervalPath X i
        starts_at := S.breakIntervalPath_initial X i
        ends_at := S.breakIntervalPath_terminal X i
        classification := (classifyFinite hclosed hreferenceClosed
          (heligible i) (hinternal i) (S.breakIntervalPath_initial X i)
          (S.breakIntervalPath_terminal X i)
          (S.breakIntervalPath_hammockInterior_disjoint X i) hinside
          (huX i) (hvX i)).some
        forwardEdges_subset_original :=
          S.breakIntervalPath_directionEdges_subset X i .forward
        vertexSet_subset_original := S.breakIntervalPath_vertexSet_subset X i
        edgeSet_subset_original := S.breakIntervalPath_edgeSet_subset X i
      }
  have piece_path (i : Fin (S.finiteWalk.breakCount X)) :
      (piece i).path = S.breakIntervalPath X i := by
    simp only [piece]
    split <;> rfl
  exact ⟨{
    count := S.finiteWalk.breakCount X
    point := S.finiteWalk.breakPoint X
    point_injective := S.finiteWalk.breakPoint_injective X
    piece := piece
    initial_eq := by
      rw [FiniteRunWalk.breakPoint, S.finiteWalk.breakPosition_zero X]
      exact S.toFiniteRunWalk.toFiniteTrace_initial.symm
    terminal_eq := by
      simp [RunCompressor.FiniteInput.finiteWalk, FiniteRunWalk.breakPoint,
        AltPath.terminal?, FiniteRunWalk.toFiniteTrace_terminal,
        FiniteRunWalk.finalPosition]
    vertexSet_exact := by
      rw [S.breakIntervals_vertexSet_exact X]
      congr 2
      funext i
      rw [piece_path i]
    edgeSet_exact := by
      rw [S.breakIntervals_edgeSet_exact X]
      congr 1
      funext i
      rw [piece_path i]
  }, rfl, fun _ ↦ rfl⟩

/-- Forget the optional coordinate equalities, preserving the original
finite-segmentation interface. -/
theorem exists_finiteClosedClassifiedContactSegmentation
    (S : RunCompressor.FiniteInput Gamma.graph) (X : Set V)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (heligible : ∀ i : Fin (S.finiteWalk.breakCount X),
      S.finiteWalk.breakPoint X i.castSucc ∉ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∉ Gamma.vertexSet Y →
      HammockEligible before innerRoof outerRoof
        (S.finiteWalk.breakPoint X i.castSucc)
        (.vertex (S.finiteWalk.breakPoint X i.succ)))
    (hinternal : ∀ i : Fin (S.finiteWalk.breakCount X),
      S.finiteWalk.breakPoint X i.castSucc ∉ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∉ Gamma.vertexSet Y →
      InternallySafe Y (S.breakIntervalPath X i))
    (huX : ∀ i : Fin (S.finiteWalk.breakCount X),
      S.finiteWalk.breakPoint X i.castSucc ∈ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.castSucc ∈ X)
    (hvX : ∀ i : Fin (S.finiteWalk.breakCount X),
      S.finiteWalk.breakPoint X i.succ ∈ Gamma.vertexSet Y →
      S.finiteWalk.breakPoint X i.succ ∈ X) :
    Nonempty (FiniteClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa)
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X) := by
  obtain ⟨D, _hcount, _hpoint⟩ :=
    exists_finiteClosedClassifiedContactSegmentation_with_points S X
      hclosed hreferenceClosed heligible hinternal huX hvX
  exact ⟨D⟩

end FiniteBreakMixedPiece
end Erdos599.Blueprint.LinkageBlueprint

#print axioms Erdos599.Blueprint.LinkageBlueprint.FiniteBreakMixedPiece.exists_finiteClosedClassifiedContactSegmentation
