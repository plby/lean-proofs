/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OrientedCutEdgeLocal

/-!
# Certified matching assembly with a prescribed global orientation

Each edge fiber is realized with the restriction of one literal source
orientation.  This module pastes the fibers and retains the equality between
the assembled orientation and that source orientation.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58OrientedCertifiedAssembly

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58ChosenMatchingAssembly
open Erdos547b.ZhaoLemma58OwnerForbiddenCertificate
open Erdos547b.ZhaoLemma58CertifiedMatchingAssembly
open Erdos547b.ZhaoLemma58OrientedCutEdgeLocal

universe v

/-- Assemble certified edge fibers whose local orientations are the literal
restrictions of `globalOrient`. -/
theorem exists_certifiedRootAttachedBranchEmbedding_of_fixedMatchingFibers
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (globalOrient : Fin b → Fin 2 ≃ Fin 2)
    (bad : Fin k → Fin r → Fin 2 → Finset B)
    (hlocal : ∀ e, Nonempty {E : CertifiedOwnerDynamicEmbedding
        (OrderedBranchForest.restrict F (matchingFiber assign e)).branches G
        (fun i ↦ rootImage (F.owner
          (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
        (endpoint e)
        (fun i ↦ F.owner
          (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
        (bad e) //
      E.orient = restrictedOrient assign globalOrient e})
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1)) :
    Nonempty {E : CertifiedRootAttachedBranchEmbedding
        F G rootImage assign endpoint bad // E.orient = globalOrient} := by
  classical
  let localFixed : ∀ e, {E : CertifiedOwnerDynamicEmbedding
      (OrderedBranchForest.restrict F (matchingFiber assign e)).branches G
      (fun i ↦ rootImage (F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
      (endpoint e)
      (fun i ↦ F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
      (bad e) // E.orient = restrictedOrient assign globalOrient e} :=
    fun e ↦ Classical.choice (hlocal e)
  let localCert : ∀ e, CertifiedOwnerDynamicEmbedding
      (OrderedBranchForest.restrict F (matchingFiber assign e)).branches G
      (fun i ↦ rootImage (F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
      (endpoint e)
      (fun i ↦ F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
      (bad e) := fun e ↦ (localFixed e).1
  let localFiberOrient : ∀ e,
      Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2 :=
    fun e ↦ (localCert e).orient
  let localOrient : Fin k → Fin b → Fin 2 ≃ Fin 2 :=
    fun e ↦ extendSelectedOrient (matchingFiber assign e)
      (localFiberOrient e)
  let orient := assembledOrient assign localOrient
  let localEmb : FiberEmbeddingFamily F G rootImage assign endpoint orient :=
    fun e ↦ reorientDynamic
      (OrderedBranchForest.restrict F (matchingFiber assign e)).branches G
      (fun i ↦ rootImage (F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
      (endpoint e) (localFiberOrient e)
      (fun i ↦ orient
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
      (localCert e).embedding (fun i ↦ by
        simp only [orient, assembledOrient_selectedEquiv, localOrient,
          extendSelectedOrient_selectedEquiv])
  let Eraw := rootAttachedBranchEmbeddingOfMatchingFibers F G rootImage assign
    endpoint orient localEmb hsupportDisjoint
  let E : CertifiedRootAttachedBranchEmbedding
      F G rootImage assign endpoint bad := {
    orient := orient
    embedding := Eraw
    avoids := by
      intro j a
      have havoid := (localCert (assign j)).avoids
        (assignmentIndex assign j) (assignmentVertex F assign j a)
      have hidx := selectedEquiv_assignmentIndex assign j
      have horient :
          extendSelectedOrient (matchingFiber assign (assign j))
              (localFiberOrient (assign j)) j =
            localFiberOrient (assign j) (assignmentIndex assign j) := by
        calc
          _ = extendSelectedOrient (matchingFiber assign (assign j))
              (localFiberOrient (assign j))
              (OrderedBranchForest.selectedEquiv
                (matchingFiber assign (assign j))
                (assignmentIndex assign j)) :=
            congrArg (extendSelectedOrient
              (matchingFiber assign (assign j))
              (localFiberOrient (assign j))) hidx.symm
          _ = _ := extendSelectedOrient_selectedEquiv _ _ _
      change (localEmb (assign j)).embedding.copy (assignmentIndex assign j)
          (assignmentVertex F assign j a) ∉
        bad (assign j) (F.owner j)
          (orient j ((F.branches.isTree j).coloringTwoOfVert
            (F.branches.root j) a))
      change (localCert (assign j)).embedding.embedding.copy
          (assignmentIndex assign j) (assignmentVertex F assign j a) ∉ _
      simpa only [hidx, assignmentVertex_coloring, orient, assembledOrient,
        localOrient, horient] using havoid
  }
  refine ⟨⟨E, ?_⟩⟩
  funext j
  have hidx := selectedEquiv_assignmentIndex assign j
  calc
    E.orient j = localFiberOrient (assign j) (assignmentIndex assign j) := by
      change orient j = _
      change extendSelectedOrient (matchingFiber assign (assign j))
        (localFiberOrient (assign j)) j = _
      calc
        _ = extendSelectedOrient (matchingFiber assign (assign j))
            (localFiberOrient (assign j))
            (OrderedBranchForest.selectedEquiv
              (matchingFiber assign (assign j))
              (assignmentIndex assign j)) :=
          congrArg (extendSelectedOrient (matchingFiber assign (assign j))
            (localFiberOrient (assign j))) hidx.symm
        _ = _ := extendSelectedOrient_selectedEquiv _ _ _
    _ = restrictedOrient assign globalOrient (assign j)
        (assignmentIndex assign j) := by
      exact congrFun (localFixed (assign j)).2 (assignmentIndex assign j)
    _ = globalOrient j := by
      unfold restrictedOrient
      rw [hidx]

end Erdos547b.ZhaoLemma58OrientedCertifiedAssembly

#print axioms Erdos547b.ZhaoLemma58OrientedCertifiedAssembly.exists_certifiedRootAttachedBranchEmbedding_of_fixedMatchingFibers
