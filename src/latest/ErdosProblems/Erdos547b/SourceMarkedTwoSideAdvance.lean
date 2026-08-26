/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedMajorAdvance
import ErdosProblems.Erdos547b.SourceCapacityTwoSideAdvance

/-!
# A common root and complete successors on both source sides

The major side advances ordinary and marked branches together. A minor
owner has no selected marked branches, so their actual images are retained.
Ordinary families on the opposite side also retain their previous copies.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedTwoSideAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceMarkedMajorAdvance Erdos547b.ZhaoSourceMarkedBranchPlacement
open Erdos547b.ZhaoSourceMarkedOwnerAdvance Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoSourceCapacitySynchronizedAdvance Erdos547b.ZhaoSourceCapacityOwnerAdvance
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)
open Erdos547b.ZhaoSourceTwoSideFamilyAdvance (otherSide rootClusters_adj)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (marks : ∀ i, Finset (Fin (F.size i))) (selected : Finset (Fin b))

theorem exists_twoSideAdvance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hk : k ≤ 3) (hCV1 : C ⊆ O.D.V1) (hC : 0 < C.card)
    (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
    (hkind : ∀ s j, (kinds s j).Valid α)
    (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
    (family : Fin 2 → Fin k → List (Fin b))
    (hdisjoint : ∀ s, Pairwise (fun i j => Disjoint (allocation s i) (allocation s j)))
    (hside : ∀ s j i, i ∈ family s j → rootSide (owner i) = s)
    (hselectedSide : ∀ i ∈ selected, rootSide (owner i) = 0)
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (A : ∀ s j, FamilyState W Q S (rootCluster W Q s) F owner (kinds s j)
      (allocation s j) (family s j) rootImage n.val)
    (E : Placement W Q S O P F marks (ownerPrefix selected owner n.val) (fun i => rootImage (owner i)))
    (hbranch : ∀ s j, ∀ i ∈ family s j, (kinds s j).BranchValid F i)
    (hedge : ∀ s j, ∀ e ∈ allocation s j, edgeValid W Q S (rootCluster W Q s) (kinds s j) e)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : ∀ s j, allocation s j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (globalCount : ℕ) (hglobal : ∀ s, (Finset.univ.biUnion (allocation s)).card ≤ globalCount)
    (hbudget : ∀ s j, family s j ≠ [] → mass (fun i => (F.size i : ℝ)) (family s j) ≤
      (∑ e ∈ allocation s j, capacity W Q S (rootCluster W Q s) (kinds s j) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (allocation s j).card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
    (hselectedSize : ∀ i ∈ selected, 3 ≤ F.size i)
    (hmarks : (∑ i ∈ selected, ((marks i).card : ℝ)) ≤ (epsilon α : ℝ) * W.clusterSize)
    (hselectedMass : (∑ i ∈ selected, (F.size i : ℝ)) ≤
      (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize)
    (hcolor : ∀ i ∈ selected, ∀ a ∈ marks i, (F.isTree i).coloringTwoOfVert (F.root i) a = 0)
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (parent : Option (Fin hostN))
    (hparent : ∀ v, parent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        ((reservoir W Q (rootSide n)).filter ((embeddingHost W).Adj v)).card) :
    ∃ z ∈ reservoir W Q (rootSide n), z ∉ used ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      (((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        ((reservoir W Q (otherSide (rootSide n))).filter ((embeddingHost W).Adj z)).card) ∧
      ∃ D : ∀ s j, FamilyState W Q S (rootCluster W Q s) F owner (kinds s j)
          (allocation s j) (family s j) (Function.update rootImage n z) (n.val + 1),
        (∀ s j i hi, ((D s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i
            (processedFamily_mono owner (Nat.le_succ n.val) (family s j) hi) =
          ((A s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i hi) ∧
        ∃ E' : Placement W Q S O P F marks (ownerPrefix selected owner (n.val + 1))
            (fun i => Function.update rootImage n z (owner i)),
          (∀ i (hi : i ∈ ownerPrefix selected owner n.val), E'.forestCopy.componentCopy i
            (ownerPrefix_mono selected owner (Nat.le_succ n.val) hi) = E.forestCopy.componentCopy i hi) ∧
          (∀ i (hi : i ∈ ownerPrefix selected owner n.val), E'.group
            ⟨i, ownerPrefix_mono selected owner (Nat.le_succ n.val) hi⟩ = E.group ⟨i, hi⟩) := by
  let Step (s : Fin 2) : Prop :=
    ∃ z ∈ reservoir W Q s, z ∉ used ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q (otherSide s))) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          ((reservoir W Q (otherSide s)).filter ((embeddingHost W).Adj z)).card) ∧
      ∃ D : ∀ j, FamilyState W Q S (rootCluster W Q s) F owner (kinds s j) (allocation s j) (family s j)
          (Function.update rootImage n z) (n.val + 1),
        (∀ j i hi, ((D j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i
            (processedFamily_mono owner (Nat.le_succ n.val) (family s j) hi) =
          ((A s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i hi) ∧
        ∃ E' : Placement W Q S O P F marks (ownerPrefix selected owner (n.val + 1))
            (fun i => Function.update rootImage n z (owner i)),
          (∀ i (hi : i ∈ ownerPrefix selected owner n.val), E'.forestCopy.componentCopy i
            (ownerPrefix_mono selected owner (Nat.le_succ n.val) hi) = E.forestCopy.componentCopy i hi) ∧
          (∀ i (hi : i ∈ ownerPrefix selected owner n.val), E'.group
            ⟨i, ownerPrefix_mono selected owner (Nat.le_succ n.val) hi⟩ = E.group ⟨i, hi⟩)
  have hcurrent : Step (rootSide n) := by
    by_cases hs : rootSide n = 0
    · rw [hs]
      exact exists_majorAdvance W Q S O P F owner marks selected hα hα1 hhost horder hk hCV1 hC
        (otherSide 0) (kinds 0) (hkind 0) (allocation 0) (family 0) (hdisjoint 0) rootImage n (A 0) E
        (hbranch 0) (hedge 0) hsmall (haway 0) globalCount (hglobal 0) (hbudget 0)
        hselectedSize hmarks hselectedMass hcolor used hused parent (fun v hv => by
          simpa only [hs] using hparent v hv)
    · obtain ⟨z, hz, hfresh, hAdj, hdegree, D, hD⟩ := exists_synchronizedFamilyAdvance W Q S
        (rootSide n) (otherSide (rootSide n)) F owner hα hα1 hhost horder hk
        (kinds (rootSide n)) (hkind (rootSide n)) (allocation (rootSide n)) (family (rootSide n))
        (hdisjoint (rootSide n)) rootImage n (A (rootSide n)) (hbranch (rootSide n)) (hedge (rootSide n))
        hsmall (haway (rootSide n)) globalCount (hglobal (rootSide n)) (hbudget (rootSide n))
        used hused parent hparent
      have hno : ∀ i ∈ selected, owner i ≠ n := by
        intro i hi ho
        have h := hselectedSide i hi
        rw [ho] at h
        exact hs h
      obtain ⟨E', hcopies, hgroups⟩ := exists_ownerSkip W Q S O P F marks selected owner rootImage n E z hno
      exact ⟨z, hz, hfresh, hAdj, hdegree, D, hD, E', hcopies, hgroups⟩
  obtain ⟨z, hz, hfresh, hAdj, hdegree, Dcurrent, hcurrent, E', hEcopies, hEgroups⟩ := hcurrent
  have hnext (s : Fin 2) :
      ∃ D : ∀ j, FamilyState W Q S (rootCluster W Q s) F owner (kinds s j)
          (allocation s j) (family s j) (Function.update rootImage n z) (n.val + 1),
        ∀ j i hi, ((D j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i
            (processedFamily_mono owner (Nat.le_succ n.val) (family s j) hi) =
          ((A s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i hi := by
    by_cases hs : s = rootSide n
    · subst s
      exact ⟨Dcurrent, hcurrent⟩
    · have hno (j : Fin k) (i : Fin b) (hi : i ∈ family s j) : owner i ≠ n := by
        intro ho
        have h := hside s j i hi
        rw [ho] at h
        exact hs h.symm
      have hstep (j : Fin k) := exists_familyAdvance_noAllocation W Q S (rootCluster W Q s) F owner (kinds s j)
        hα hα1 hhost horder (hkind s j) rootImage n (A s j) z
        (by
          intro i hi
          apply hno j i
          exact (A s j).flatten ▸ List.mem_append_right _ hi)
        (by
          intro x hx howner
          obtain ⟨i, hi, hoi⟩ := howner
          have hm : i ∈ activeItems W Q S (rootCluster W Q s) F owner (kinds s j) (A s j).active := by
            rw [hx]
            exact hi
          have hf : i ∈ family s j :=
            (A s j).flatten ▸ List.mem_append_left _ (List.mem_append_right _ hm)
          exact (hno j i hf hoi).elim)
      choose D _ _ _ _ _ hD using hstep
      exact ⟨D, hD⟩
  choose D hD using hnext
  exact ⟨z, hz, hfresh, hAdj, hdegree (rootClusters_adj W Q (rootSide n)), D, hD, E', hEcopies, hEgroups⟩

end Erdos547b.ZhaoSourceMarkedTwoSideAdvance

#print axioms Erdos547b.ZhaoSourceMarkedTwoSideAdvance.exists_twoSideAdvance
