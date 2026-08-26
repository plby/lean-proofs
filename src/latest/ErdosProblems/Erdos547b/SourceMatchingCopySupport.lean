/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingReconnectedCopy
import ErdosProblems.Erdos547b.SourceMatchingRowIdentity

/-! # The actual terminal copy uses only its literal physical support -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingCopySupport

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceMatchingGeometry
open Erdos547b.ZhaoSourceMatchingGlobalPrefix Erdos547b.ZhaoSourceMatchingReconnectedCopy
open Erdos547b.ZhaoSourceMatchingRowIdentity Erdos547b.ZhaoSourceReconnectedGraph
open Erdos547b.ZhaoSourceGlobalPrefixState (CutSource)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (P : (padGraph (reduced W)).Subgraph)

def hostSupport : Finset (Fin hostN) :=
  (reservoir W Q 0 ∪ reservoir W Q 1) ∪
    (matchingSupport P).biUnion (padCluster (clusterVertices (assignment W)))

theorem reservoir_subset_hostSupport (s : Fin 2) : reservoir W Q s ⊆ hostSupport W Q P := by
  intro x hx
  apply Finset.mem_union_left
  fin_cases s
  · exact Finset.mem_union_left _ hx
  · exact Finset.mem_union_right _ hx

theorem pairWhole_subset_hostSupport (e : MatchingEdge P) (c : Fin 2) :
    pairWhole W P e c ⊆ hostSupport W Q P := by
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨pairVertex W P e c, pairVertex_mem_support W P e c, hx⟩)

variable (S : CleanSourceWitness W Q)
variable {r b k : ℕ} (F : OrderedBranchForest r b) (rootSide : Fin r → Fin 2)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge P))
variable (family : Fin 2 → Fin k → List (Fin b)) (avoid : Fin 2 → Finset (Fin hostN))
variable (locate : Fin b → Fin 2 × Fin k) (hcover : ∀ i, i ∈ family (locate i).1 (locate i).2)
variable (L : CutSource F.branches F.owner rootSide locate)
variable (A : CutPrefixState W Q S P F.branches F.owner rootSide allocation family avoid locate hcover L r)
variable (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2))
variable (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished P
  (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))

theorem terminalCopy_mem_hostSupport (x : F.Vertex) :
    terminalReconnectedCopy W Q S P F rootSide allocation family avoid locate hcover L A hdisjoint haway x ∈
      hostSupport W Q P := by
  rcases x with i | ⟨j, a⟩
  · rw [terminalReconnectedCopy_root]
    exact reservoir_subset_hostSupport W Q P (rootSide i) (A.state.root_mem i i.isLt)
  · change A.state.branchCopy W Q S P F.branches F.owner rootSide allocation family avoid locate hcover
      j (F.owner j).isLt a ∈ hostSupport W Q P
    exact pairWhole_subset_hostSupport W Q P _ _ (Finset.mem_sdiff.mp
      (A.state.branchCopy_side W Q S P F.branches F.owner rootSide allocation family avoid locate hcover
        j (F.owner j).isLt a)).1

theorem terminalCopy_avoids (unused : Finset (Fin hostN))
    (hdis : Disjoint (hostSupport W Q P) unused) (x : F.Vertex) :
    terminalReconnectedCopy W Q S P F rootSide allocation family avoid locate hcover L A hdisjoint haway x ∉
      unused := by
  intro hx
  exact Finset.disjoint_left.mp hdis
    (terminalCopy_mem_hostSupport W Q P S F rootSide allocation family avoid locate hcover L A hdisjoint haway x) hx

open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceMatchingPendingPlan

include hcover hdisjoint haway in
/-- Construct the copy, including its root information, from source budgets. -/
theorem exists_supported_copy_of_sourceBudgets (hP : P.IsMatching)
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
    ∃ f : (reconnectedGraph F L).Copy (embeddingHost W), (∀ i : Fin r,
      q ≤ G.degree (f (Sum.inl i)) ∧
      f (Sum.inl i) ∈ reservoir W Q (rootSide i) ∧
      f (Sum.inl i) ∉ avoid (rootSide i)) ∧ ∀ x, f x ∈ hostSupport W Q P := by
  obtain ⟨D⟩ := exists_terminalCutPrefix W Q S P F.branches F.owner
    rootSide allocation family avoid locate hcover L hα hα1 hhost horder hk
    hside hsmall haway globalCount hglobal hbudget hroots havoid hP hnd hordered
  refine ⟨terminalReconnectedCopy W Q S P F rootSide allocation family avoid locate hcover L
    D hdisjoint haway, ?_, ?_⟩
  · intro i
    exact ⟨terminalReconnectedCopy_root_high W Q S P F rootSide allocation family avoid locate hcover L
      D hdisjoint haway i, D.state.root_mem i i.isLt, D.state.root_avoid i i.isLt⟩
  · exact terminalCopy_mem_hostSupport W Q P S F rootSide allocation family avoid locate hcover L
      D hdisjoint haway

end Erdos547b.ZhaoSourceMatchingCopySupport

#print axioms Erdos547b.ZhaoSourceMatchingCopySupport.terminalCopy_mem_hostSupport
#print axioms Erdos547b.ZhaoSourceMatchingCopySupport.terminalCopy_avoids
#print axioms Erdos547b.ZhaoSourceMatchingCopySupport.exists_supported_copy_of_sourceBudgets
