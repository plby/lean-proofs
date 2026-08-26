/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceReconnectedGraph
import ErdosProblems.Erdos547b.SourceCapacityTerminalBranches
import ErdosProblems.Erdos547b.SourceCapacityGlobalCutPrefix

/-!
# The terminal ordinary prefix copies the reconnected source graph

Its component-root images are retained in their actual high-degree
reservoirs, as required when omitted leaves are restored later.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceTerminalReconnectedCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoSourceReconnectedGraph Erdos547b.ZhaoSourceCapacityGlobalPrefix
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceGlobalPrefixState (CutCoordinate coordinateOwner CutSource)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {r b k : ℕ} (F : OrderedBranchForest r b)
variable (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b)) (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∈ family (locate i).1 (locate i).2)
variable (L : CutSource F.branches F.owner rootSide locate)
variable (A : CutPrefixState W Q S F.branches F.owner rootSide kinds allocation family locate hcover L r)
variable (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2))
variable (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished Q.claim67.M
  (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))

def terminalReconnectedCopy : (reconnectedGraph F L).Copy (embeddingHost W) := by
  let E := A.state.terminalBranchEmbedding W Q S F.branches F.owner rootSide kinds allocation family locate hcover hdisjoint
  let graphCopy := F.copyOfBranchEmbedding (embeddingHost W) A.state.rootImage E
    (fun i j h => A.state.root_injective i j i.isLt j.isLt h)
    (A.state.root_ne_branchCopy W Q S F.branches F.owner rootSide kinds allocation family locate hcover haway)
    (fun i => A.state.branchCopy_attach W Q S F.branches F.owner rootSide kinds allocation family locate hcover i (F.owner i).isLt)
  have hcoord (x : F.Vertex) : graphCopy x =
      A.state.coordinateImage F.branches F.owner W Q S rootSide kinds allocation family locate hcover x
        (coordinateOwner F.branches F.owner x).isLt := by
    cases x <;> rfl
  exact copyOfForestCopy F L (embeddingHost W) graphCopy (by
    intro i hi
    rw [hcoord]
    exact A.cut_adj i hi i.isLt)

theorem terminalReconnectedCopy_root (i : Fin r) :
    terminalReconnectedCopy W Q S F rootSide kinds allocation family locate hcover L A hdisjoint haway (Sum.inl i) =
      A.state.rootImage i := rfl

theorem terminalReconnectedCopy_root_high (i : Fin r) :
    q ≤ G.degree (terminalReconnectedCopy W Q S F rootSide kinds allocation family locate hcover L A hdisjoint haway (Sum.inl i)) := by
  rw [terminalReconnectedCopy_root]
  have hi := A.state.root_mem i i.isLt
  rcases OrderedRootedForest.fin_two_eq_zero_or_one (rootSide i) with hs | hs
  · rw [hs] at hi
    exact Q.A₀_high _ hi
  · rw [hs] at hi
    exact Q.B₀_high _ hi

end Erdos547b.ZhaoSourceTerminalReconnectedCopy

#print axioms Erdos547b.ZhaoSourceTerminalReconnectedCopy.terminalReconnectedCopy
#print axioms Erdos547b.ZhaoSourceTerminalReconnectedCopy.terminalReconnectedCopy_root_high
