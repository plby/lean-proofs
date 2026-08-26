/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OwnerForbiddenCertificate
import ErdosProblems.Erdos547b.Lemma58ChosenMatchingAssembly

/-!
# Matching assembly with retained owner-cleaning certificates

The ordinary matching assembly keeps the concrete branch copies but forgets
why their images avoided the owner-specific target-cleaning sets.  This file
assembles the certified edge fibers and retains that one extra fact.  It is
the graph-theoretic bridge needed to reinsert Zhao's deleted cut edges: a cut
parent lying in an earlier branch avoids the non-neighbours of the already
chosen child root.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58CertifiedMatchingAssembly

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

universe v

/-- A full branch realization together with the owner/side bad-set
avoidance inherited from every matching fiber. -/
structure CertifiedRootAttachedBranchEmbedding
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B)
    (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (bad : Fin k → Fin r → Fin 2 → Finset B) where
  orient : Fin b → Fin 2 ≃ Fin 2
  embedding : RootAttachedBranchEmbedding F G rootImage
    (fun j c ↦ endpoint (assign j) c) orient
  avoids : ∀ j a,
    embedding.branchEmbedding.copy j a ∉
      bad (assign j) (F.owner j)
        (orient j ((F.branches.isTree j).coloringTwoOfVert
          (F.branches.root j) a))

/-- Assemble certified dynamically oriented edge fibers. -/
theorem exists_certifiedRootAttachedBranchEmbedding_of_matchingFibers
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (bad : Fin k → Fin r → Fin 2 → Finset B)
    (hlocal : ∀ e, Nonempty (CertifiedOwnerDynamicEmbedding
      (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
        (matchingFiber assign e)).branches G
      (fun i ↦ rootImage (F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
      (endpoint e)
      (fun i ↦ F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
      (bad e)))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1)) :
    Nonempty (CertifiedRootAttachedBranchEmbedding
      F G rootImage assign endpoint bad) := by
  classical
  let localCert : ∀ e, CertifiedOwnerDynamicEmbedding
      (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
        (matchingFiber assign e)).branches G
      (fun i ↦ rootImage (F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
      (endpoint e)
      (fun i ↦ F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
      (bad e) := fun e ↦ Classical.choice (hlocal e)
  let localFiberOrient : ∀ e,
      Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2 :=
    fun e ↦ (localCert e).orient
  let localOrient : Fin k → Fin b → Fin 2 ≃ Fin 2 :=
    fun e ↦ extendSelectedOrient (matchingFiber assign e)
      (localFiberOrient e)
  let orient := assembledOrient assign localOrient
  let localEmb : FiberEmbeddingFamily F G rootImage assign endpoint orient :=
    fun e ↦ reorientDynamic
      (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
        (matchingFiber assign e)).branches G
      (fun i ↦ rootImage (F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
      (endpoint e) (localFiberOrient e)
      (fun i ↦ orient
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
      (localCert e).embedding (fun i ↦ by
        simp only [orient, assembledOrient_selectedEquiv, localOrient,
          extendSelectedOrient_selectedEquiv])
  let E := rootAttachedBranchEmbeddingOfMatchingFibers F G rootImage assign
    endpoint orient localEmb hsupportDisjoint
  refine ⟨{
    orient := orient
    embedding := E
    avoids := ?_
  }⟩
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
            (matchingFiber assign (assign j)) (assignmentIndex assign j)) :=
        congrArg (extendSelectedOrient (matchingFiber assign (assign j))
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

end Erdos547b.ZhaoLemma58CertifiedMatchingAssembly

#print axioms Erdos547b.ZhaoLemma58CertifiedMatchingAssembly.exists_certifiedRootAttachedBranchEmbedding_of_matchingFibers
