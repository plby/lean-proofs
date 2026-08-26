/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceReconnectedGraph
import ErdosProblems.Erdos547b.SourceMatchingTerminalBranches
import ErdosProblems.Erdos547b.SourceMatchingGlobalCutPrefix

/-!
# The terminal ordinary prefix copies the reconnected source graph

Its component-root images are retained in their actual high-degree
reservoirs, as required when omitted leaves are restored later.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingReconnectedCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoSourceReconnectedGraph Erdos547b.ZhaoSourceMatchingGlobalPrefix
open Erdos547b.ZhaoSourceMatchingPendingPlan Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceGlobalPrefixState (CutCoordinate coordinateOwner CutSource)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable (P : (padGraph (reduced W)).Subgraph)
variable {r b k : ℕ} (F : OrderedBranchForest r b)
variable (rootSide : Fin r → Fin 2)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge P))
variable (family : Fin 2 → Fin k → List (Fin b))
variable (avoid : Fin 2 → Finset (Fin hostN)) (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∈ family (locate i).1 (locate i).2)
variable (L : CutSource F.branches F.owner rootSide locate)
variable (A : CutPrefixState W Q S P F.branches F.owner rootSide allocation family avoid locate hcover L r)
variable (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2))
variable (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished P
  (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))

def terminalReconnectedCopy : (reconnectedGraph F L).Copy (embeddingHost W) := by
  let E := A.state.terminalBranchEmbedding W Q S P F.branches F.owner rootSide allocation family avoid locate hcover hdisjoint
  let graphCopy := F.copyOfBranchEmbedding (embeddingHost W) A.state.rootImage E
    (fun i j h => A.state.root_injective i j i.isLt j.isLt h)
    (A.state.root_ne_branchCopy W Q S P F.branches F.owner rootSide allocation family avoid locate hcover haway)
    (fun i => A.state.branchCopy_attach W Q S P F.branches F.owner rootSide allocation family avoid locate hcover i (F.owner i).isLt)
  have hcoord (x : F.Vertex) : graphCopy x =
      A.state.coordinateImage F.branches F.owner W Q S P rootSide allocation family avoid locate hcover x
        (coordinateOwner F.branches F.owner x).isLt := by
    cases x <;> rfl
  exact copyOfForestCopy F L (embeddingHost W) graphCopy (by
    intro i hi
    rw [hcoord]
    exact A.cut_adj i hi i.isLt)

theorem terminalReconnectedCopy_root (i : Fin r) :
    terminalReconnectedCopy W Q S P F rootSide allocation family avoid locate hcover L A hdisjoint haway (Sum.inl i) =
      A.state.rootImage i := rfl

theorem terminalReconnectedCopy_root_high (i : Fin r) :
    q ≤ G.degree (terminalReconnectedCopy W Q S P F rootSide allocation family avoid locate hcover L A hdisjoint haway (Sum.inl i)) := by
  rw [terminalReconnectedCopy_root]
  have hi := A.state.root_mem i i.isLt
  rcases OrderedRootedForest.fin_two_eq_zero_or_one (rootSide i) with hs | hs
  · rw [hs] at hi
    exact Q.A₀_high _ hi
  · rw [hs] at hi
    exact Q.B₀_high _ hi


theorem terminalReconnectedCopy_root_avoid (i : Fin r) :
    terminalReconnectedCopy W Q S P F rootSide allocation family avoid locate hcover L A hdisjoint haway
      (Sum.inl i) ∉ avoid (rootSide i) :=
  A.state.root_avoid i i.isLt

open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule

include hcover hdisjoint haway in
/-- Construct the copy, including its root information, from source budgets. -/
theorem exists_copy_of_sourceBudgets (hP : P.IsMatching)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) (hk : k ≤ 3)
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => F.owner i ≤ F.owner j))
    (hside : ∀ s j i, i ∈ family s j → rootSide (F.owner i) = s)
    (hsmall : ∀ i, F.branches.size i ≤ freshBranchBound α W.clusterSize)
    (globalCount : ℕ) (hglobal : ∀ s, (Finset.univ.biUnion (allocation s)).card ≤ globalCount)
    (hbudget : ∀ s j, family s j ≠ [] → mass (fun i => (F.branches.size i : ℝ)) (family s j) ≤
      (∑ e ∈ allocation s j, capacity W Q P S (rootCluster W Q s) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (allocation s j).card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
    (hroots : (r : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (havoid : ∀ s, ((avoid s).card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * W.clusterSize) :
    ∃ f : (reconnectedGraph F L).Copy (embeddingHost W), ∀ i : Fin r,
      q ≤ G.degree (f (Sum.inl i)) ∧
      f (Sum.inl i) ∈ reservoir W Q (rootSide i) ∧
      f (Sum.inl i) ∉ avoid (rootSide i) := by
  obtain ⟨D⟩ := exists_terminalCutPrefix W Q S P F.branches F.owner
    rootSide allocation family avoid locate hcover L hα hα1 hhost horder hk
    hside hsmall haway globalCount hglobal hbudget hroots havoid hP hnd hordered
  refine ⟨terminalReconnectedCopy W Q S P F rootSide allocation family avoid locate hcover L
    D hdisjoint haway, ?_⟩
  intro i
  exact ⟨terminalReconnectedCopy_root_high W Q S P F rootSide allocation family avoid locate hcover L
    D hdisjoint haway i, D.state.root_mem i i.isLt, D.state.root_avoid i i.isLt⟩

end Erdos547b.ZhaoSourceMatchingReconnectedCopy

#print axioms Erdos547b.ZhaoSourceMatchingReconnectedCopy.terminalReconnectedCopy
#print axioms Erdos547b.ZhaoSourceMatchingReconnectedCopy.terminalReconnectedCopy_root_high

#print axioms Erdos547b.ZhaoSourceMatchingReconnectedCopy.terminalReconnectedCopy_root_avoid
#print axioms Erdos547b.ZhaoSourceMatchingReconnectedCopy.exists_copy_of_sourceBudgets
