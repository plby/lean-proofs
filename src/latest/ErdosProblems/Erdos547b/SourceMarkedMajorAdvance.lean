/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedCapacityFamilyRoot
import ErdosProblems.Erdos547b.SourceMarkedOwnerAdvance
import ErdosProblems.Erdos547b.SourceCapacityFamilyBudgetAdvance

/-!
# Simultaneous major-side ordinary and marked successors

Both successors use the same constructed root and literal updated root map.
Their previous copies are preserved. Global support separation is proved
separately from the actual source matching and is not inferred from this
pair of componentwise successors alone.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedMajorAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoSourceCapacityFamilyBudgetAdvance Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceRootExclusions Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceMarkedRootExclusions
open Erdos547b.ZhaoSourceMarkedCapacityFamilyRoot Erdos547b.ZhaoSourceMarkedBranchPlacement
open Erdos547b.ZhaoSourceMarkedOwnerAdvance Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (marks : ∀ i, Finset (Fin (F.size i))) (selected : Finset (Fin b))

theorem exists_majorAdvance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hk : k ≤ 3) (hCV1 : C ⊆ O.D.V1) (hC : 0 < C.card)
    (t : Fin 2) (kinds : Fin k → FamilyKind) (hkind : ∀ j, (kinds j).Valid α)
    (allocation : Fin k → Finset (MatchingEdge Q.claim67.M)) (family : Fin k → List (Fin b))
    (hdisjoint : Pairwise (fun i j => Disjoint (allocation i) (allocation j)))
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (A : ∀ j, FamilyState W Q S (rootCluster W Q 0) F owner (kinds j)
      (allocation j) (family j) rootImage n.val)
    (E : Placement W Q S O P F marks (ownerPrefix selected owner n.val) (fun i => rootImage (owner i)))
    (hbranch : ∀ j, ∀ i ∈ family j, (kinds j).BranchValid F i)
    (hedge : ∀ j, ∀ e ∈ allocation j, edgeValid W Q S (rootCluster W Q 0) (kinds j) e)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : ∀ j, allocation j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (globalCount : ℕ) (hglobal : (Finset.univ.biUnion allocation).card ≤ globalCount)
    (hbudget : ∀ j, family j ≠ [] → mass (fun i => (F.size i : ℝ)) (family j) ≤
      (∑ e ∈ allocation j, capacity W Q S (rootCluster W Q 0) (kinds j) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (allocation j).card -
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
        ((reservoir W Q 0).filter ((embeddingHost W).Adj v)).card) :
    ∃ z ∈ reservoir W Q 0, z ∉ used ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q 0)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          ((reservoir W Q t).filter ((embeddingHost W).Adj z)).card) ∧
      ∃ D : ∀ j, FamilyState W Q S (rootCluster W Q 0) F owner (kinds j) (allocation j) (family j)
          (Function.update rootImage n z) (n.val + 1),
        (∀ j i hi, ((D j).currentPlacement W Q S (rootCluster W Q 0) F owner (kinds j)).forestCopy.componentCopy i
            (processedFamily_mono owner (Nat.le_succ n.val) (family j) hi) =
          ((A j).currentPlacement W Q S (rootCluster W Q 0) F owner (kinds j)).forestCopy.componentCopy i hi) ∧
        ∃ E' : Placement W Q S O P F marks (ownerPrefix selected owner (n.val + 1))
            (fun i => Function.update rootImage n z (owner i)),
          (∀ i (hi : i ∈ ownerPrefix selected owner n.val), E'.forestCopy.componentCopy i
            (ownerPrefix_mono selected owner (Nat.le_succ n.val) hi) = E.forestCopy.componentCopy i hi) ∧
          (∀ i (hi : i ∈ ownerPrefix selected owner n.val), E'.group
            ⟨i, ownerPrefix_mono selected owner (Nat.le_succ n.val) hi⟩ = E.group ⟨i, hi⟩) := by
  obtain ⟨z, hz, hfresh, hAdj, hactive, hdegree, hgcount, hggood, bad, hbad⟩ :=
    exists_marked_capacityFamily_root W Q S O P t F owner hα hα1 hhost horder hk hCV1
      kinds hkind allocation family hdisjoint rootImage n.val A haway globalCount hglobal
      used hused parent hparent
  have hstep (j : Fin k) := exists_familyAdvance W Q S (rootCluster W Q 0) F owner (kinds j)
    hα hα1 hhost horder (rootCluster_cases W Q 0) (hkind j) (hbranch j) (hedge j) hsmall (haway j)
    rootImage n (A j) globalCount (hbudget j) z (hactive j) (bad j) (hbad j).1 (hbad j).2.1 (hbad j).2.2
  choose D hD using hstep
  obtain ⟨E', hcopies, hgroups⟩ := exists_ownerAdvance W Q S O P F marks selected owner
    hα hα1 hC rootImage n E ∅ (fun _ => Finset.disjoint_empty_left _)
    hselectedSize hmarks hselectedMass hcolor (fun i _ => hsmall i) z
    (badGroups W Q S O P z) hgcount hggood
  exact ⟨z, hz, hfresh, hAdj, hdegree, D, hD, E', hcopies, hgroups⟩

end Erdos547b.ZhaoSourceMarkedMajorAdvance

#print axioms Erdos547b.ZhaoSourceMarkedMajorAdvance.exists_majorAdvance
