/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingTwoSideAdvance

/-!
# Global actual root and family prefixes

All family states share one root map. Earlier roots are injective, lie in
their prescribed reservoirs, and retain the opposite-reservoir degree.
The successor excludes the literal used-root image and constructs all new
family states with exact preservation of earlier branch copies.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceMatchingTwoSideAdvance Erdos547b.ZhaoSourceMatchingFamilyOwnerAdvance
open Erdos547b.ZhaoSourceMatchingFamilyState Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceMatchingRootSelection Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceMatchingPendingPlan
open Erdos547b.ZhaoSourceTwoSideFamilyAdvance (otherSide)
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)
open Erdos547b.ZhaoSourceFreshChunkBounds

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable (P : (padGraph (reduced W)).Subgraph)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (rootSide : Fin r → Fin 2)
variable (all : Fin 2 → Fin k → Finset (MatchingEdge P))
variable (family : Fin 2 → Fin k → List (Fin b))
variable (avoid : Fin 2 → Finset (Fin hostN))

structure PrefixState (stage : ℕ) where
  rootImage : Fin r → Fin hostN
  root_mem : ∀ i, i.val < stage → rootImage i ∈ reservoir W Q (rootSide i)
  root_avoid : ∀ i, i.val < stage → rootImage i ∉ avoid (rootSide i)
  root_injective : ∀ i j, i.val < stage → j.val < stage → rootImage i = rootImage j → i = j
  root_degree : ∀ i, i.val < stage →
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q (otherSide (rootSide i))).filter ((embeddingHost W).Adj (rootImage i))) : ℝ)
  families : ∀ s j, FamilyState W Q S P (rootCluster W Q s) F owner
    (all s j) (family s j) rootImage stage

variable {stage : ℕ} (A : PrefixState W Q S P F owner rootSide all family avoid stage)

def PrefixState.usedRoots : Finset (Fin hostN) :=
  (Finset.univ.filter (fun i : Fin r => i.val < stage)).image A.rootImage

theorem PrefixState.mem_usedRoots (z : Fin hostN) :
    z ∈ A.usedRoots W Q S P F owner rootSide all family avoid ↔
      ∃ i : Fin r, i.val < stage ∧ A.rootImage i = z := by
  simp only [PrefixState.usedRoots, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem PrefixState.card_usedRoots : (A.usedRoots W Q S P F owner rootSide all family avoid).card ≤ r := by
  have h := (Finset.card_image_le (f := A.rootImage)
    (s := Finset.univ.filter (fun i : Fin r => i.val < stage))).trans
      (Finset.card_filter_le Finset.univ (fun i : Fin r => i.val < stage))
  simpa only [PrefixState.usedRoots, Finset.card_univ, Fintype.card_fin] using h

def emptyPrefixState (hP : P.IsMatching)
    (hnd : ∀ s j, (family s j).Nodup)
    (hordered : ∀ s j, (family s j).Pairwise (fun i j => owner i ≤ owner j))
    (rootImage : Fin r → Fin hostN) : PrefixState W Q S P F owner rootSide all family avoid 0 where
  rootImage := rootImage
  root_mem := by omega
  root_avoid := by omega
  root_injective := by omega
  root_degree := by omega
  families s j := emptyFamilyState W Q S P (rootCluster W Q s) F owner hP
    (all s j) (family s j) (hnd s j) (hordered s j) rootImage

/-- A global successor with actual root injectivity and exact family-copy
preservation. Its optional parent is an already existing host image. -/
theorem exists_prefixAdvance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) (hk : k ≤ 3)
    (hside : ∀ s j i, i ∈ family s j → rootSide (owner i) = s)
    (n : Fin r) (A : PrefixState W Q S P F owner rootSide all family avoid n.val)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : ∀ s j, all s j ⊆ edgesAwayFromDistinguished P
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (globalCount : ℕ) (hglobal : ∀ s, (Finset.univ.biUnion (all s)).card ≤ globalCount)
    (hbudget : ∀ s j, family s j ≠ [] → mass (fun i => (F.size i : ℝ)) (family s j) ≤
      (∑ e ∈ all s j, capacity W Q P S (rootCluster W Q s) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (all s j).card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
    (hroots : (r : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (havoid : ∀ s, ((avoid s).card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * W.clusterSize)
    (parent : Option (Fin hostN))
    (hparent : ∀ v, parent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        (#((reservoir W Q (rootSide n)).filter ((embeddingHost W).Adj v)) : ℝ)) :
    ∃ z, ∃ D : PrefixState W Q S P F owner rootSide all family avoid (n.val + 1),
      D.rootImage = Function.update A.rootImage n z ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      ∀ s j i hi, ((D.families s j).currentPlacement W Q S P (rootCluster W Q s) F owner).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ n.val) (family s j) hi) =
        ((A.families s j).currentPlacement W Q S P (rootCluster W Q s) F owner).forestCopy.componentCopy i hi := by
  have hused : ((A.usedRoots W Q S P F owner rootSide all family avoid).card : ℝ) ≤
      (epsilon α : ℝ) * W.clusterSize := by
    have hc : ((A.usedRoots W Q S P F owner rootSide all family avoid).card : ℝ) ≤ r := by
      exact_mod_cast A.card_usedRoots W Q S P F owner rootSide all family avoid
    exact hc.trans hroots
  let excluded := A.usedRoots W Q S P F owner rootSide all family avoid ∪ avoid (rootSide n)
  have hexcluded : (excluded.card : ℝ) ≤
      ((epsilon α : ℝ) + 2 * (rootTypicality α : ℝ)) * W.clusterSize := by
    have hc : (excluded.card : ℝ) ≤
        ((A.usedRoots W Q S P F owner rootSide all family avoid).card : ℝ) +
          (avoid (rootSide n)).card := by
      exact_mod_cast Finset.card_union_le
        (A.usedRoots W Q S P F owner rootSide all family avoid) (avoid (rootSide n))
    nlinarith only [hc, hused, havoid (rootSide n)]
  obtain ⟨z, hz, hfreshAll, hAdj, hdegree, Dfamily, hcopies⟩ :=
    exists_twoSideFamilyAdvance W Q S P F owner hα hα1 hhost horder hk rootSide all family hside
      A.rootImage n A.families hsmall haway globalCount hglobal hbudget
      excluded hexcluded parent hparent
  have hfresh : z ∉ A.usedRoots W Q S P F owner rootSide all family avoid :=
    fun hz => hfreshAll (Finset.mem_union_left _ hz)
  have hzAvoid : z ∉ avoid (rootSide n) := fun hz => hfreshAll (Finset.mem_union_right _ hz)
  let root' := Function.update A.rootImage n z
  have hbefore (i : Fin r) (hi : i.val < n.val) : root' i = A.rootImage i :=
    Function.update_of_ne (fun h => Nat.ne_of_lt hi (congrArg Fin.val h)) z A.rootImage
  have hbeforeLt (i : Fin r) (hi : i.val < n.val + 1) (hne : i ≠ n) : i.val < n.val := by
    have hv : i.val ≠ n.val := fun h => hne (Fin.ext h)
    omega
  have hrootCurrent : root' n = z := Function.update_self _ _ _
  let D : PrefixState W Q S P F owner rootSide all family avoid (n.val + 1) := {
    rootImage := root'
    root_mem := by
      intro i hi
      by_cases hin : i = n
      · subst i
        exact hrootCurrent.symm ▸ hz
      · rw [hbefore i (hbeforeLt i hi hin)]
        exact A.root_mem i (hbeforeLt i hi hin)
    root_avoid := by
      intro i hi
      by_cases hin : i = n
      · subst i
        rw [hrootCurrent]
        exact hzAvoid
      · rw [hbefore i (hbeforeLt i hi hin)]
        exact A.root_avoid i (hbeforeLt i hi hin)
    root_injective := by
      intro i j hi hj heq
      by_cases hin : i = n
      · subst i
        by_cases hjn : j = n
        · exact hjn.symm
        · have hjb := hbeforeLt j hj hjn
          rw [hrootCurrent, hbefore j hjb] at heq
          exact (hfresh ((A.mem_usedRoots W Q S P F owner rootSide all family avoid z).mpr
            ⟨j, hjb, heq.symm⟩)).elim
      · by_cases hjn : j = n
        · subst j
          have hib := hbeforeLt i hi hin
          rw [hbefore i hib, hrootCurrent] at heq
          exact (hfresh ((A.mem_usedRoots W Q S P F owner rootSide all family avoid z).mpr
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

end Erdos547b.ZhaoSourceMatchingGlobalPrefix

#print axioms Erdos547b.ZhaoSourceMatchingGlobalPrefix.PrefixState.card_usedRoots
#print axioms Erdos547b.ZhaoSourceMatchingGlobalPrefix.emptyPrefixState
#print axioms Erdos547b.ZhaoSourceMatchingGlobalPrefix.exists_prefixAdvance
