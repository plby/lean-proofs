/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteClosedClassifiedProducer

/-!
# Certified finite closed/classified contact segmentation

The general classifier returns a type with three positive constructors, so
an arbitrary chosen classification cannot reveal which endpoint case was
used.  Here the constructor branches on endpoint coverage first.  Therefore
every piece which actually contributes a shortcut was built in the exposed,
safe Claim-2 branch, and retains the corresponding geometric certificate.
The existing segmentation interfaces are unchanged.
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

/-- Deterministically construct one mixed piece.  Shortcut membership is
possible only in the last branch, where both exposed endpoints are off the
reference warp and the concrete interval is genuinely safe. -/
theorem exists_breakIntervalMixedPiece_with_certificate
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
    ∃ P : ClassifiedOrClosedFiniteContactPiece
        (Y := Y) (kappa := kappa)
        (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
        (S.finiteWalk.breakPoint X i.castSucc)
        (S.finiteWalk.breakPoint X i.succ),
      P.path = S.breakIntervalPath X i ∧
      ∀ e ∈ P.shortcutEdges,
        S.finiteWalk.breakPoint X i.castSucc ∉ Gamma.vertexSet Y ∧
        S.finiteWalk.breakPoint X i.succ ∉ Gamma.vertexSet Y ∧
        IsSafe Y P.path ∧
        HammockEligible before innerRoof outerRoof
          (S.finiteWalk.breakPoint X i.castSucc)
          (.vertex (S.finiteWalk.breakPoint X i.succ)) ∧
        Disjoint
          (hammockInterior (S.finiteWalk.breakPoint X i.castSucc)
            (.vertex (S.finiteWalk.breakPoint X i.succ)) P.path) X ∧
        ¬P.path.vertexSet ⊆ X := by
  by_cases hinside : (S.breakIntervalPath X i).vertexSet ⊆ X
  · let P : ClassifiedOrClosedFiniteContactPiece
        (Y := Y) (kappa := kappa)
        (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
        (S.finiteWalk.breakPoint X i.castSucc)
        (S.finiteWalk.breakPoint X i.succ) :=
      .closed (breakIntervalClosedPiece S X i hinside)
    refine ⟨P, rfl, ?_⟩
    intro e he
    change e ∈ (∅ : Set (V × V)) at he
    exact (by simpa using he : False).elim
  · by_cases huY :
        S.finiteWalk.breakPoint X i.castSucc ∈ Gamma.vertexSet Y
    · let owner : ClosedReferenceOwner Y X
          (S.finiteWalk.breakPoint X i.castSucc) :=
        (ClosedReferenceOwner.exists_of_mem hreferenceClosed huY (huX huY)).some
      let Cpiece : ClassifiedFiniteContactPiece
          (Y := Y) (kappa := kappa)
          (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
          (S.finiteWalk.breakPoint X i.castSucc)
          (S.finiteWalk.breakPoint X i.succ) := {
        path := S.breakIntervalPath X i
        starts_at := S.breakIntervalPath_initial X i
        ends_at := S.breakIntervalPath_terminal X i
        classification := .initialCovered owner
        forwardEdges_subset_original :=
          S.breakIntervalPath_directionEdges_subset X i .forward
        vertexSet_subset_original := S.breakIntervalPath_vertexSet_subset X i
        edgeSet_subset_original := S.breakIntervalPath_edgeSet_subset X i
      }
      let P : ClassifiedOrClosedFiniteContactPiece
          (Y := Y) (kappa := kappa)
          (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
          (S.finiteWalk.breakPoint X i.castSucc)
          (S.finiteWalk.breakPoint X i.succ) := .classified Cpiece
      refine ⟨P, rfl, ?_⟩
      intro e he
      change e ∈ (∅ : Set (V × V)) at he
      exact (by simpa using he : False).elim
    · by_cases hvY :
          S.finiteWalk.breakPoint X i.succ ∈ Gamma.vertexSet Y
      · let owner : ClosedReferenceOwner Y X
            (S.finiteWalk.breakPoint X i.succ) :=
          (ClosedReferenceOwner.exists_of_mem hreferenceClosed hvY (hvX hvY)).some
        let Cpiece : ClassifiedFiniteContactPiece
            (Y := Y) (kappa := kappa)
            (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
            (S.finiteWalk.breakPoint X i.castSucc)
            (S.finiteWalk.breakPoint X i.succ) := {
          path := S.breakIntervalPath X i
          starts_at := S.breakIntervalPath_initial X i
          ends_at := S.breakIntervalPath_terminal X i
          classification := .terminalCovered owner
          forwardEdges_subset_original :=
            S.breakIntervalPath_directionEdges_subset X i .forward
          vertexSet_subset_original := S.breakIntervalPath_vertexSet_subset X i
          edgeSet_subset_original := S.breakIntervalPath_edgeSet_subset X i
        }
        let P : ClassifiedOrClosedFiniteContactPiece
            (Y := Y) (kappa := kappa)
            (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
            (S.finiteWalk.breakPoint X i.castSucc)
            (S.finiteWalk.breakPoint X i.succ) := .classified Cpiece
        refine ⟨P, rfl, ?_⟩
        intro e he
        change e ∈ (∅ : Set (V × V)) at he
        exact (by simpa using he : False).elim
      · have hsafe : IsSafe Y (S.breakIntervalPath X i) := by
          apply (hinternal huY hvY).isSafe_of_exposedEndpoints
          · simpa only [S.breakIntervalPath_initial] using huY
          · intro w hw
            have hwv := Option.some.inj
              (hw.symm.trans (S.breakIntervalPath_terminal X i))
            simpa only [hwv] using hvY
        have himag : IsImaginaryEdge Gamma Y kappa
            (S.finiteWalk.breakPoint X i.castSucc)
            (S.finiteWalk.breakPoint X i.succ) :=
          isImaginaryEdge_of_closed hclosed (heligible huY hvY) hsafe
            (S.breakIntervalPath_initial X i)
            (S.breakIntervalPath_terminal X i)
            (S.breakIntervalPath_hammockInterior_disjoint X i) hinside
        let Cpiece : ClassifiedFiniteContactPiece
            (Y := Y) (kappa := kappa)
            (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
            (S.finiteWalk.breakPoint X i.castSucc)
            (S.finiteWalk.breakPoint X i.succ) := {
          path := S.breakIntervalPath X i
          starts_at := S.breakIntervalPath_initial X i
          ends_at := S.breakIntervalPath_terminal X i
          classification := .imaginary himag
          forwardEdges_subset_original :=
            S.breakIntervalPath_directionEdges_subset X i .forward
          vertexSet_subset_original := S.breakIntervalPath_vertexSet_subset X i
          edgeSet_subset_original := S.breakIntervalPath_edgeSet_subset X i
        }
        let P : ClassifiedOrClosedFiniteContactPiece
            (Y := Y) (kappa := kappa)
            (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
            (S.finiteWalk.breakPoint X i.castSucc)
            (S.finiteWalk.breakPoint X i.succ) := .classified Cpiece
        refine ⟨P, rfl, ?_⟩
        intro _e _he
        exact ⟨huY, hvY, hsafe, heligible huY hvY,
          S.breakIntervalPath_hammockInterior_disjoint X i, hinside⟩

/-- Assemble the deterministic pieces into the exact finite segmentation.
Besides the old coordinate identities, every shortcut-bearing piece carries
the exposed safe-path certificate used to build it. -/
theorem exists_finiteClosedClassifiedContactSegmentation_with_certificates
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
        (∀ i, D.point i = S.finiteWalk.breakPoint X
          (Fin.cast (congrArg (fun n : Nat ↦ n + 1) hcount) i)) ∧
        (∀ i : Fin D.count, (D.piece i).path =
          S.breakIntervalPath X (Fin.cast hcount i)) ∧
        ∀ (i : Fin D.count) e, e ∈ (D.piece i).shortcutEdges →
          D.point i.castSucc ∉ Gamma.vertexSet Y ∧
          D.point i.succ ∉ Gamma.vertexSet Y ∧
          IsSafe Y (D.piece i).path ∧
          HammockEligible before innerRoof outerRoof
            (D.point i.castSucc) (.vertex (D.point i.succ)) ∧
          Disjoint (hammockInterior (D.point i.castSucc)
            (.vertex (D.point i.succ)) (D.piece i).path) X ∧
          ¬(D.piece i).path.vertexSet ⊆ X := by
  classical
  have hexists (i : Fin (S.finiteWalk.breakCount X)) :=
    exists_breakIntervalMixedPiece_with_certificate S X i hclosed
      hreferenceClosed (heligible i) (hinternal i) (huX i) (hvX i)
  let piece : (i : Fin (S.finiteWalk.breakCount X)) →
      ClassifiedOrClosedFiniteContactPiece
        (Y := Y) (kappa := kappa)
        (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X
        (S.finiteWalk.breakPoint X i.castSucc)
        (S.finiteWalk.breakPoint X i.succ) := fun i ↦
    Classical.choose (hexists i)
  have piece_spec (i : Fin (S.finiteWalk.breakCount X)) :=
    Classical.choose_spec (hexists i)
  let D : FiniteClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa)
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace) X := {
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
      rw [(piece_spec i).1]
    edgeSet_exact := by
      rw [S.breakIntervals_edgeSet_exact X]
      congr 1
      funext i
      rw [(piece_spec i).1]
  }
  refine ⟨D, rfl, fun _ ↦ rfl, fun i ↦ (piece_spec i).1, ?_⟩
  intro i e he
  exact (piece_spec i).2 e he

#print axioms exists_breakIntervalMixedPiece_with_certificate
#print axioms
  exists_finiteClosedClassifiedContactSegmentation_with_certificates

end FiniteBreakMixedPiece
end Erdos599.Blueprint.LinkageBlueprint
