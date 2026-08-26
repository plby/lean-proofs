/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityTwoSideAdvance

/-!
# Actual global roots and capacity-aware family prefixes

All families share the same partially revealed root map. The successor
excludes its literal earlier image, constructs both sides' family states,
and preserves root injectivity, reservoir degrees and earlier branch maps.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceCapacityTwoSideAdvance Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)
open Erdos547b.ZhaoSourceTwoSideFamilyAdvance (otherSide)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b))

structure PrefixState (stage : ℕ) where
  rootImage : Fin r → Fin hostN
  root_mem : ∀ i, i.val < stage → rootImage i ∈ reservoir W Q (rootSide i)
  root_injective : ∀ i j, i.val < stage → j.val < stage → rootImage i = rootImage j → i = j
  root_degree : ∀ i, i.val < stage →
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q (otherSide (rootSide i))).filter ((embeddingHost W).Adj (rootImage i))) : ℝ)
  families : ∀ s j, FamilyState W Q S (rootCluster W Q s) F owner (kinds s j)
    (allocation s j) (family s j) rootImage stage

variable {stage : ℕ} (A : PrefixState W Q S F owner rootSide kinds allocation family stage)

def PrefixState.usedRoots : Finset (Fin hostN) :=
  (Finset.univ.filter (fun i : Fin r => i.val < stage)).image A.rootImage

theorem PrefixState.mem_usedRoots (z : Fin hostN) :
    z ∈ A.usedRoots W Q S F owner rootSide kinds allocation family ↔
      ∃ i : Fin r, i.val < stage ∧ A.rootImage i = z := by
  simp only [PrefixState.usedRoots, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem PrefixState.card_usedRoots : (A.usedRoots W Q S F owner rootSide kinds allocation family).card ≤ r := by
  have h := (Finset.card_image_le (f := A.rootImage)
    (s := Finset.univ.filter (fun i : Fin r => i.val < stage))).trans
      (Finset.card_filter_le Finset.univ (fun i : Fin r => i.val < stage))
  simpa only [PrefixState.usedRoots, Finset.card_univ, Fintype.card_fin] using h

def emptyPrefixState
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => owner i ≤ owner j))
    (rootImage : Fin r → Fin hostN) : PrefixState W Q S F owner rootSide kinds allocation family 0 where
  rootImage := rootImage
  root_mem := by omega
  root_injective := by omega
  root_degree := by omega
  families s j := emptyFamilyState W Q S (rootCluster W Q s) F owner (kinds s j)
    (allocation s j) (family s j) (hnd s j) (hordered s j) rootImage

theorem exists_prefixAdvance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hk : k ≤ 3)
    (hkind : ∀ s j, (kinds s j).Valid α)
    (hdisjoint : ∀ s, Pairwise (fun i j => Disjoint (allocation s i) (allocation s j)))
    (hside : ∀ s j i, i ∈ family s j → rootSide (owner i) = s)
    (n : Fin r) (A : PrefixState W Q S F owner rootSide kinds allocation family n.val)
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
    (hroots : (r : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (parent : Option (Fin hostN))
    (hparent : ∀ v, parent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        (#((reservoir W Q (rootSide n)).filter ((embeddingHost W).Adj v)) : ℝ)) :
    ∃ z, ∃ D : PrefixState W Q S F owner rootSide kinds allocation family (n.val + 1),
      D.rootImage = Function.update A.rootImage n z ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      ∀ s j i hi,
        ((D.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ n.val) (family s j) hi) =
        ((A.families s j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds s j)).forestCopy.componentCopy i hi := by
  have hused : ((A.usedRoots W Q S F owner rootSide kinds allocation family).card : ℝ) ≤
      (epsilon α : ℝ) * W.clusterSize := by
    have hc : ((A.usedRoots W Q S F owner rootSide kinds allocation family).card : ℝ) ≤ r := by
      exact_mod_cast A.card_usedRoots W Q S F owner rootSide kinds allocation family
    exact hc.trans hroots
  obtain ⟨z, hz, hfresh, hAdj, hdegree, Dfamily, hcopies⟩ :=
    exists_twoSideFamilyAdvance W Q S F owner hα hα1 hhost horder hk rootSide kinds hkind
      allocation family hdisjoint hside A.rootImage n A.families hbranch hedge hsmall haway
      globalCount hglobal hbudget (A.usedRoots W Q S F owner rootSide kinds allocation family) hused parent hparent
  let root' := Function.update A.rootImage n z
  have hbefore (i : Fin r) (hi : i.val < n.val) : root' i = A.rootImage i :=
    Function.update_of_ne (fun h => Nat.ne_of_lt hi (congrArg Fin.val h)) z A.rootImage
  have hbeforeLt (i : Fin r) (hi : i.val < n.val + 1) (hne : i ≠ n) : i.val < n.val := by
    have hv : i.val ≠ n.val := fun h => hne (Fin.ext h)
    omega
  have hrootCurrent : root' n = z := Function.update_self _ _ _
  let D : PrefixState W Q S F owner rootSide kinds allocation family (n.val + 1) := {
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
  exact ⟨z, D, rfl, hAdj, hcopies⟩

end Erdos547b.ZhaoSourceCapacityGlobalPrefix

#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.PrefixState.card_usedRoots
#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.emptyPrefixState
#print axioms Erdos547b.ZhaoSourceCapacityGlobalPrefix.exists_prefixAdvance
