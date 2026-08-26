/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedTwoSideAdvance
import ErdosProblems.Erdos547b.SourceCapacityGlobalPrefix

/-!
# A common global root map with ordinary and marked branch prefixes

The actual earlier root image is excluded at the next root choice. Both
branch placements share this same root map and preserve their old copies.
The deleted tree cut edges are handled by the subsequent cut-prefix layer.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceMarkedTwoSideAdvance Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoSourceMarkedBranchPlacement Erdos547b.ZhaoSourceMarkedOwnerAdvance
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)
open Erdos547b.ZhaoSourceTwoSideFamilyAdvance (otherSide)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (marks : ∀ i, Finset (Fin (F.size i))) (selected : Finset (Fin b))
variable (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b))

structure PrefixState (stage : ℕ) where
  ordinary : Erdos547b.ZhaoSourceCapacityGlobalPrefix.PrefixState W Q S F owner rootSide kinds allocation family stage
  marked : Placement W Q S O P F marks (ownerPrefix selected owner stage) (fun i => ordinary.rootImage (owner i))

def emptyPrefixState
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => owner i ≤ owner j)) :
    PrefixState W Q S O P F owner marks selected rootSide kinds allocation family 0 := by
  let A := Erdos547b.ZhaoSourceCapacityGlobalPrefix.emptyPrefixState W Q S F owner rootSide kinds allocation family
    hnd hordered (fun _ => S.zA)
  refine ⟨A, ?_⟩
  simpa only [ownerPrefix_zero] using Placement.empty W Q S O P F marks (fun i => A.rootImage (owner i))

def ordinarySuccessor (n : Fin r)
    (A : Erdos547b.ZhaoSourceCapacityGlobalPrefix.PrefixState W Q S F owner rootSide kinds allocation family n.val)
    (z : Fin hostN) (hz : z ∈ reservoir W Q (rootSide n))
    (hfresh : z ∉ A.usedRoots W Q S F owner rootSide kinds allocation family)
    (hdegree : ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      ((reservoir W Q (otherSide (rootSide n))).filter ((embeddingHost W).Adj z)).card)
    (Dfamily : ∀ s j, FamilyState W Q S (rootCluster W Q s) F owner (kinds s j)
      (allocation s j) (family s j) (Function.update A.rootImage n z) (n.val + 1)) :
    Erdos547b.ZhaoSourceCapacityGlobalPrefix.PrefixState W Q S F owner rootSide kinds allocation family (n.val + 1) := by
  let root' := Function.update A.rootImage n z
  have hbefore (i : Fin r) (hi : i.val < n.val) : root' i = A.rootImage i :=
    Function.update_of_ne (fun h => Nat.ne_of_lt hi (congrArg Fin.val h)) z A.rootImage
  have hbeforeLt (i : Fin r) (hi : i.val < n.val + 1) (hne : i ≠ n) : i.val < n.val := by
    have hv : i.val ≠ n.val := fun h => hne (Fin.ext h)
    omega
  have hrootCurrent : root' n = z := Function.update_self _ _ _
  exact {
    rootImage := root'
    root_mem := by
      intro i hi
      by_cases hin : i = n
      · subst i
        exact hrootCurrent.symm ▸ hz
      · rw [hbefore i (hbeforeLt i hi hin)]
        exact A.root_mem i (hbeforeLt i hi hin)
    root_injective := by
      intro i j hi hj heq
      by_cases hin : i = n
      · subst i
        by_cases hjn : j = n
        · exact hjn.symm
        · have hjb := hbeforeLt j hj hjn
          rw [hrootCurrent, hbefore j hjb] at heq
          exact (hfresh ((A.mem_usedRoots W Q S F owner rootSide kinds allocation family z).mpr
            ⟨j, hjb, heq.symm⟩)).elim
      · by_cases hjn : j = n
        · subst j
          have hib := hbeforeLt i hi hin
          rw [hbefore i hib, hrootCurrent] at heq
          exact (hfresh ((A.mem_usedRoots W Q S F owner rootSide kinds allocation family z).mpr
            ⟨i, hib, heq⟩)).elim
        · have hib := hbeforeLt i hi hin
          have hjb := hbeforeLt j hj hjn
          rw [hbefore i hib, hbefore j hjb] at heq
          exact A.root_injective i j hib hjb heq
    root_degree := by
      intro i hi
      by_cases hin : i = n
      · subst i
        rw [hrootCurrent]
        exact hdegree
      · rw [hbefore i (hbeforeLt i hi hin)]
        exact A.root_degree i (hbeforeLt i hi hin)
    families := Dfamily }

theorem exists_prefixAdvance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hk : k ≤ 3) (hCV1 : C ⊆ O.D.V1) (hC : 0 < C.card)
    (hkind : ∀ s j, (kinds s j).Valid α)
    (hdisjoint : ∀ s, Pairwise (fun i j => Disjoint (allocation s i) (allocation s j)))
    (hside : ∀ s j i, i ∈ family s j → rootSide (owner i) = s)
    (hselectedSide : ∀ i ∈ selected, rootSide (owner i) = 0)
    (n : Fin r) (A : PrefixState W Q S O P F owner marks selected rootSide kinds allocation family n.val)
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
    (hroots : (r : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (parent : Option (Fin hostN))
    (hparent : ∀ v, parent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        ((reservoir W Q (rootSide n)).filter ((embeddingHost W).Adj v)).card) :
    ∃ z, ∃ D : PrefixState W Q S O P F owner marks selected rootSide kinds allocation family (n.val + 1),
      D.ordinary.rootImage = Function.update A.ordinary.rootImage n z ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      (∀ s j i hi,
        ((D.ordinary.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ n.val) (family s j) hi) =
        ((A.ordinary.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i hi) ∧
      (∀ i (hi : i ∈ ownerPrefix selected owner n.val), D.marked.forestCopy.componentCopy i
        (ownerPrefix_mono selected owner (Nat.le_succ n.val) hi) = A.marked.forestCopy.componentCopy i hi) ∧
      (∀ i (hi : i ∈ ownerPrefix selected owner n.val), D.marked.group
        ⟨i, ownerPrefix_mono selected owner (Nat.le_succ n.val) hi⟩ = A.marked.group ⟨i, hi⟩) := by
  have hused : ((A.ordinary.usedRoots W Q S F owner rootSide kinds allocation family).card : ℝ) ≤
      (epsilon α : ℝ) * W.clusterSize := by
    have hc : ((A.ordinary.usedRoots W Q S F owner rootSide kinds allocation family).card : ℝ) ≤ r := by
      exact_mod_cast A.ordinary.card_usedRoots W Q S F owner rootSide kinds allocation family
    exact hc.trans hroots
  obtain ⟨z, hz, hfresh, hAdj, hdegree, Dfamily, hcopies, E', hmarkedCopies, hmarkedGroups⟩ :=
    exists_twoSideAdvance W Q S O P F owner marks selected hα hα1 hhost horder hk hCV1 hC
      rootSide kinds hkind allocation family hdisjoint hside hselectedSide A.ordinary.rootImage n
      A.ordinary.families A.marked hbranch hedge hsmall haway globalCount hglobal hbudget
      hselectedSize hmarks hselectedMass hcolor
      (A.ordinary.usedRoots W Q S F owner rootSide kinds allocation family) hused parent hparent
  let D : PrefixState W Q S O P F owner marks selected rootSide kinds allocation family (n.val + 1) := {
    ordinary := ordinarySuccessor W Q S F owner rootSide kinds allocation family n A.ordinary z hz hfresh hdegree Dfamily
    marked := E' }
  exact ⟨z, D, rfl, hAdj, hcopies, hmarkedCopies, hmarkedGroups⟩

end Erdos547b.ZhaoSourceMarkedGlobalPrefix

#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.emptyPrefixState
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.ordinarySuccessor
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.exists_prefixAdvance
