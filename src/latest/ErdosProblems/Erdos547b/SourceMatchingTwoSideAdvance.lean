/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingSynchronizedAdvance
import ErdosProblems.Erdos547b.SourceTwoSideFamilyAdvance

/-!
# One actual successor for both source-root sides

Only the families belonging to the current root side require root
selection. The owner-side condition forces every other family to skip
this owner without any eligibility premise. Both sides share the same
updated root map and preserve every earlier original-index copy.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingTwoSideAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceMatchingSynchronizedAdvance Erdos547b.ZhaoSourceMatchingFamilyOwnerAdvance
open Erdos547b.ZhaoSourceMatchingFamilyState Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceMatchingRootSelection Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceFreshChunkBounds

open Erdos547b.ZhaoSourceTwoSideFamilyAdvance (otherSide rootClusters_adj)
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)
open Erdos547b.ZhaoSourceMatchingPendingPlan

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

variable (S : CleanSourceWitness W Q) (P : (padGraph (reduced W)).Subgraph)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

/-- Construct all two-side family successors with a single fresh root.
The opposite-reservoir degree is discharged using the actual rich edge. -/
theorem exists_twoSideFamilyAdvance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) (hk : k ≤ 3)
    (rootSide : Fin r → Fin 2)
    (all : Fin 2 → Fin k → Finset (MatchingEdge P))
    (family : Fin 2 → Fin k → List (Fin b))
    (hside : ∀ s j i, i ∈ family s j → rootSide (owner i) = s)
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (A : ∀ s j, FamilyState W Q S P (rootCluster W Q s) F owner (all s j) (family s j) rootImage n.val)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : ∀ s j, all s j ⊆ edgesAwayFromDistinguished P
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (globalCount : ℕ) (hglobal : ∀ s, (Finset.univ.biUnion (all s)).card ≤ globalCount)
    (hbudget : ∀ s j, family s j ≠ [] → mass (fun i => (F.size i : ℝ)) (family s j) ≤
      (∑ e ∈ all s j, capacity W Q P S (rootCluster W Q s) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (all s j).card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ ((epsilon α : ℝ) + 2 * (rootTypicality α : ℝ)) * W.clusterSize)
    (parent : Option (Fin hostN))
    (hparent : ∀ v, parent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        (#((reservoir W Q (rootSide n)).filter ((embeddingHost W).Adj v)) : ℝ)) :
    ∃ z ∈ reservoir W Q (rootSide n), z ∉ used ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      (((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        (#((reservoir W Q (otherSide (rootSide n))).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ D : ∀ s j, FamilyState W Q S P (rootCluster W Q s) F owner (all s j) (family s j)
          (Function.update rootImage n z) (n.val + 1),
        ∀ s j i hi, ((D s j).currentPlacement W Q S P (rootCluster W Q s) F owner).forestCopy.componentCopy i
            (processedFamily_mono owner (Nat.le_succ n.val) (family s j) hi) =
          ((A s j).currentPlacement W Q S P (rootCluster W Q s) F owner).forestCopy.componentCopy i hi := by
  obtain ⟨z, hz, hfresh, hAdj, hdegree, Dcurrent, hcurrent⟩ :=
    exists_synchronizedFamilyAdvance W Q S P (rootSide n) (otherSide (rootSide n)) F owner
      hα hα1 hhost horder hk (all (rootSide n)) (family (rootSide n)) rootImage n
      (A (rootSide n)) hsmall (haway (rootSide n)) globalCount (hglobal (rootSide n))
      (hbudget (rootSide n)) used hused parent hparent
  have hnext (s : Fin 2) :
      ∃ D : ∀ j, FamilyState W Q S P (rootCluster W Q s) F owner (all s j) (family s j)
          (Function.update rootImage n z) (n.val + 1),
        ∀ j i hi, ((D j).currentPlacement W Q S P (rootCluster W Q s) F owner).forestCopy.componentCopy i
            (processedFamily_mono owner (Nat.le_succ n.val) (family s j) hi) =
          ((A s j).currentPlacement W Q S P (rootCluster W Q s) F owner).forestCopy.componentCopy i hi := by
    by_cases hs : s = rootSide n
    · subst s
      exact ⟨Dcurrent, hcurrent⟩
    · have hno (j : Fin k) (i : Fin b) (hi : i ∈ family s j) : owner i ≠ n := by
        intro ho
        have h := hside s j i hi
        rw [ho] at h
        exact hs h.symm
      have hstep (j : Fin k) := exists_familyAdvance_noAllocation W Q S P (rootCluster W Q s) F owner
        rootImage n (A s j) z
        (by
          intro i hi
          apply hno j i
          exact (A s j).flatten ▸ List.mem_append_right _ hi)
        (by
          intro x hx howner
          obtain ⟨i, hi, hoi⟩ := howner
          have hm : i ∈ activeItems W Q S P (rootCluster W Q s) F owner (A s j).active := by
            rw [hx]
            exact hi
          have hf : i ∈ family s j :=
            (A s j).flatten ▸ List.mem_append_left _ (List.mem_append_right _ hm)
          exact (hno j i hf hoi).elim)
      choose D _ _ _ _ _ hD using hstep
      exact ⟨D, hD⟩
  choose D hD using hnext
  exact ⟨z, hz, hfresh, hAdj, hdegree (rootClusters_adj W Q (rootSide n)), D, hD⟩

end Erdos547b.ZhaoSourceMatchingTwoSideAdvance

#print axioms Erdos547b.ZhaoSourceMatchingTwoSideAdvance.exists_twoSideFamilyAdvance
