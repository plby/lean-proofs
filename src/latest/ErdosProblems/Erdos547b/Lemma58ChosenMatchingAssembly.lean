/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58ChosenOwnerBatches
import ErdosProblems.Erdos547b.Lemma58MatchingAssembly

/-!
# Assembly of matching fibers with locally chosen orientations

The Part-3 owner recursion chooses an orientation separately inside each
matching-edge fiber.  Since distinct edge fibers have disjoint source
indices, these local orientations paste to one literal branch orientation.
After that reindexing, the already proved matching assembly returns the
global root-attached embedding (and, when roots are separated, a literal
copy of the whole branch forest).
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58ChosenMatchingAssembly

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58ChosenOwnerBatches

universe v

/-- Paste the orientation chosen inside every assignment fiber back to the
literal original branch indices. -/
def assembledOrient {b k : ℕ} (assign : Fin b → Fin k)
    (localOrient : Fin k → Fin b → Fin 2 ≃ Fin 2) :
    Fin b → Fin 2 ≃ Fin 2 :=
  fun j ↦ localOrient (assign j) j

@[simp] theorem assembledOrient_selectedEquiv {b k : ℕ}
    (assign : Fin b → Fin k)
    (localOrient : Fin k → Fin b → Fin 2 ≃ Fin 2)
    (e : Fin k) (i : Fin (matchingFiber assign e).card) :
    assembledOrient assign localOrient
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i) =
      localOrient e
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i) := by
  have hj : assign
      (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i) = e := by
    exact (mem_matchingFiber assign e _).mp
      (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i).property
  simp only [assembledOrient, hj]

/-- Assemble edge-local embeddings whose orientations were chosen by their
own dynamic owner recursions. -/
theorem exists_rootAttachedBranchEmbedding_of_chosenMatchingFibers
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (hlocal : ∀ e, ∃ localOrient :
        Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
          (matchingFiber assign e)).branches G
        (fun i ↦ rootImage (F.owner
          (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
        localOrient (endpoint e)))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (RootAttachedBranchEmbedding F G rootImage
        (fun j c ↦ endpoint (assign j) c) orient) := by
  classical
  let localFiberOrient : ∀ e,
      Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2 :=
    fun e ↦ Classical.choose (hlocal e)
  let localOrient : Fin k → Fin b → Fin 2 ≃ Fin 2 :=
    fun e ↦ extendSelectedOrient (matchingFiber assign e)
      (localFiberOrient e)
  let localEmb : ∀ e, DynamicAttachedForestEmbedding
      (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
        (matchingFiber assign e)).branches G
      (fun i ↦ rootImage (F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
      (localFiberOrient e) (endpoint e) :=
    fun e ↦ Classical.choice (Classical.choose_spec (hlocal e))
  let orient := assembledOrient assign localOrient
  have hfixed : FiberEmbeddingFamily F G rootImage assign endpoint orient :=
    fun e ↦ reorientDynamic
      (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
        (matchingFiber assign e)).branches G
      (fun i ↦ rootImage (F.owner
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
      (endpoint e) (localFiberOrient e)
      (fun i ↦ orient
        (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i))
      (localEmb e) (fun i ↦ by
        simp only [orient, assembledOrient_selectedEquiv, localOrient,
          extendSelectedOrient_selectedEquiv])
  exact ⟨orient,
    exists_rootAttachedBranchEmbedding_of_matchingFibers F G rootImage assign
      endpoint orient (fun e ↦ ⟨hfixed e⟩) hsupportDisjoint⟩

/-- Literal whole-forest copy from locally chosen edge-fiber orientations. -/
theorem exists_graphCopy_of_chosenMatchingFibers
    {r b k : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b) (G : SimpleGraph B)
    (rootImage : Fin r → B) (assign : Fin b → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (hlocal : ∀ e, ∃ localOrient :
        Fin (matchingFiber assign e).card → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict F
          (matchingFiber assign e)).branches G
        (fun i ↦ rootImage (F.owner
          (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)))
        localOrient (endpoint e)))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ q e c, rootImage q ∉ endpoint e c) :
    Nonempty (F.graph.Copy G) := by
  obtain ⟨orient, ⟨E⟩⟩ :=
    exists_rootAttachedBranchEmbedding_of_chosenMatchingFibers
      F G rootImage assign endpoint hlocal hsupportDisjoint
  exact ⟨E.toGraphCopy F G rootImage
    (fun j c ↦ endpoint (assign j) c) orient hrootInjective (by
      intro q i a hEq
      have hmem := E.map_branch i a
      exact hrootOutside q (assign i)
        (orient i ((F.branches.isTree i).coloringTwoOfVert
          (F.branches.root i) a)) (hEq.symm ▸ hmem))⟩

end Erdos547b.ZhaoLemma58ChosenMatchingAssembly

#print axioms Erdos547b.ZhaoLemma58ChosenMatchingAssembly.exists_rootAttachedBranchEmbedding_of_chosenMatchingFibers
#print axioms Erdos547b.ZhaoLemma58ChosenMatchingAssembly.exists_graphCopy_of_chosenMatchingFibers
