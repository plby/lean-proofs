/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingCopySupport
import ErdosProblems.Erdos547b.SourceMatchingCapacityMargins
import ErdosProblems.Erdos547b.SourceReconnectedTwoRowCopy

/-!
# Actual ordinary copies from two arbitrary-matching row budgets

Source-family lists are constructed from the existing owner-sorted list.
The extra root exclusions survive in the actual returned graph copy.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingTwoRowCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoSourceMatchingReconnectedCopy Erdos547b.ZhaoSourceMatchingCapacityMargins
open Erdos547b.ZhaoSourceMatchingCopySupport
open Erdos547b.ZhaoSourceMatchingGeometry Erdos547b.ZhaoSourceMatchingPendingPlan
open Erdos547b.ZhaoSourceReconnectedGraph Erdos547b.ZhaoSourceFiniteCapacityLayout
open Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceReconnectedTwoRowCopy (sideFamily sideLocate)
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceGlobalPrefixState (CutSource)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable (P : (padGraph (reduced W)).Subgraph)
variable {r b : ℕ} (F : OrderedBranchForest r b) (rootSide : Fin r → Fin 2)
variable (L : CutSource F.branches F.owner rootSide (sideLocate F rootSide))

include S in
theorem exists_reconnectedCopy_of_twoRowBudgets (hP : P.IsMatching)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (E : Fin 2 → Finset (MatchingEdge P)) (hdisjoint : Disjoint (E 0) (E 1))
    (haway : ∀ s, E s ⊆ edgesAwayFromDistinguished P (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (hsmall : ∀ i, F.branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (r : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (avoid : Fin 2 → Finset (Fin hostN))
    (havoid : ∀ s, ((avoid s).card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * W.clusterSize)
    (hbudget : ∀ s, sideFamily F rootSide s ≠ ∅ →
      (∑ i ∈ sideFamily F rootSide s, (F.branches.size i : ℝ)) + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ E s, pairWeight W Q S P (rootCluster W Q s) e) :
    ∃ f : (reconnectedGraph F L).Copy (embeddingHost W), (∀ i : Fin r,
      q ≤ G.degree (f (Sum.inl i)) ∧
      f (Sum.inl i) ∈ reservoir W Q (rootSide i) ∧
      f (Sum.inl i) ∉ avoid (rootSide i)) ∧ ∀ x, f x ∈ hostSupport W Q P := by
  let family := fun (s : Fin 2) (_ : Fin 1) => familyList F.owner (sideFamily F rootSide s)
  have hcover : ∀ i, i ∈ family (sideLocate F rootSide i).1 (sideLocate F rootSide i).2 := by
    intro i
    exact (mem_familyList _ _ i).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
  have hside : ∀ s j i, i ∈ family s j → rootSide (F.owner i) = s := by
    intro s j i hi
    exact (Finset.mem_filter.mp ((mem_familyList _ _ i).mp hi)).2
  have hvolume : (W.clusterSize : ℝ) * Fintype.card (MatchingEdge P) ≤ q := by
    simpa only [Finset.card_univ] using matchingVolume_bound W P hP hhost Finset.univ
  have hbudget' : ∀ s j, family s j ≠ [] → mass (fun i => (F.branches.size i : ℝ)) (family s j) ≤
      (∑ e ∈ E s, capacity W Q P S (rootCluster W Q s) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (E s).card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * Fintype.card (MatchingEdge P) := by
    intro s j hnonempty
    change mass _ (familyList _ _) ≤ _
    rw [mass_familyList]
    apply capacityBudget_of_row_margin W Q S P (rootCluster W Q s) hα hα1 (E s)
      (Fintype.card (MatchingEdge P)) (matchingVolume_bound W P hP hhost _) hvolume
    apply hbudget s
    intro he
    apply hnonempty
    simp only [family, familyList, he, Finset.notMem_empty, decide_false, List.filter_false]
  have hallDisjoint : ∀ x y : Fin 2 × Fin 1, x ≠ y → Disjoint (E x.1) (E y.1) := by
    rintro ⟨s, i⟩ ⟨t, j⟩ hne
    have hst : s ≠ t := fun h => hne (Prod.ext h (Subsingleton.elim i j))
    fin_cases s <;> fin_cases t
    · exact (hst rfl).elim
    · exact hdisjoint
    · exact hdisjoint.symm
    · exact (hst rfl).elim
  exact exists_supported_copy_of_sourceBudgets W Q P S F rootSide (fun s (_ : Fin 1) => E s)
    family avoid (sideLocate F rootSide) hcover L hallDisjoint (fun s _ => haway s) hP
    hα hα1 hhost horder (by decide) (fun _ _ => familyList_nodup _ _)
    (fun _ _ => familyList_ordered _ _) hside hsmall (Fintype.card (MatchingEdge P))
    (fun _ => Finset.card_le_univ _) hbudget' hroots havoid

end Erdos547b.ZhaoSourceMatchingTwoRowCopy

#print axioms Erdos547b.ZhaoSourceMatchingTwoRowCopy.exists_reconnectedCopy_of_twoRowBudgets
