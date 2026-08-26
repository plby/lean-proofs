/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceSelectedMarkedTreeCopy
import ErdosProblems.Erdos547b.SourceFiniteCapacityLayout
import ErdosProblems.Erdos547b.SourceExceptionalFamilies
import ErdosProblems.Erdos547b.SourceExceptionalIdealGains
import ErdosProblems.Erdos547b.SourceMatchingVolume

/-!
# Two literal residual source families beside the selected marked forest

Owner-sorted filtered lists supply the source layout. The source three-gamma
row-weight margin pays all ordinary capacity and bad-edge losses.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedTwoRowTreeCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.TreePartition
open Erdos547b.ZhaoSourceSelectedMarkedTreeCopy Erdos547b.ZhaoSourceFiniteCapacityLayout
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoSourceExceptionalIdealGains
open Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceCapacityBudgetMargins Erdos547b.ZhaoSourceMatchingVolume
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceClaim616Selection Erdos547b.ZhaoSourceCrossingClusters
open Erdos547b.ZhaoClaim68BranchAdapter Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616HierarchyAttachments Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim615SourceSelection

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U}
variable (sourceP : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))
variable (F : SelectedF0Within (branchForest sourceP) (halfBranches sourceP)
  (selectionTarget W Q S O C) (freshBranchBound α W.clusterSize))

include P hT in
theorem exists_treeCopy_of_twoRowBudgets
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hCV1 : C ⊆ O.D.V1) (hCcard : C.card = crossingScale W)
    (E : Fin 2 → Finset (MatchingEdge Q.claim67.M)) (hdisjoint : Disjoint (E 0) (E 1))
    (haway : ∀ s, E s ⊆ awayEdges W Q)
    (hresidual : ∀ s e, e ∈ E s →
      e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C ∨ e ∈ O.D.mbEdges)
    (hbudget : ∀ s, sideBranches sourceP s \ F.selected ≠ ∅ →
      (branchMass sourceP (sideBranches sourceP s \ F.selected) : ℝ) + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ E s, sideWeight W Q S s e) :
    Nonempty (T.Copy (embeddingHost W)) := by
  let family := fun (s : Fin 2) (_ : Fin 1) =>
    familyList (branchForest sourceP).owner (sideBranches sourceP s \ F.selected)
  let locate := fun i => (componentReservoirSide sourceP ((branchForest sourceP).owner i), (0 : Fin 1))
  have hcover : ∀ i, i ∉ F.selected → i ∈ family (locate i).1 (locate i).2 := by
    intro i hi
    apply (mem_familyList _ _ _).mpr
    exact Finset.mem_sdiff.mpr ⟨(mem_sideBranches sourceP _ i).mpr rfl, hi⟩
  apply exists_treeCopy_of_residualBudgets W Q S O P hT sourceP F
    (globalCount := Fintype.card (MatchingEdge Q.claim67.M))
    (fun _ _ => .threshold 0) (fun s _ => E s) family locate hcover (fun _ => rfl)
    hα hα1 hhost horder hcard (by decide) hCV1 hCcard
    (by intros; constructor <;> norm_num)
    (fun _ _ => familyList_nodup _ _) (fun _ _ => familyList_ordered _ _)
    (fun s j i hi => (mem_sideBranches sourceP s i).mp
      (Finset.mem_sdiff.mp ((mem_familyList _ _ i).mp hi)).1)
    (fun _ _ i _ => ordinary_branchValid _ i) (by intros; trivial)
  · rintro ⟨s, i⟩ ⟨t, j⟩ hne
    have hst : s ≠ t := fun h => hne (Prod.ext h (Subsingleton.elim i j))
    fin_cases s <;> fin_cases t
    · exact (hst rfl).elim
    · exact hdisjoint
    · exact hdisjoint.symm
    · exact (hst rfl).elim
  · exact fun s _ => haway s
  · exact fun s _ e he => hresidual s e he
  · exact fun _ => Finset.card_le_univ _
  · intro s j hnonempty
    have hne : sideBranches sourceP s \ F.selected ≠ ∅ := by
      intro hempty
      apply hnonempty
      simp only [family, familyList, hempty, Finset.notMem_empty, decide_false, List.filter_false]
    change mass _ (familyList _ _) ≤ _
    rw [mass_familyList]
    apply capacityBudget_of_ideal_margin W Q S (rootCluster W Q s) hα hα1 (.threshold 0) (E s)
      (Fintype.card (MatchingEdge Q.claim67.M)) (matchingVolume_bound W Q hhost _) (fullMatchingVolume_bound W Q hhost)
    simpa only [ordinary_idealCapacity, branchMass, Nat.cast_sum] using hbudget s hne

end Erdos547b.ZhaoSourceMarkedTwoRowTreeCopy

#print axioms Erdos547b.ZhaoSourceMarkedTwoRowTreeCopy.exists_treeCopy_of_twoRowBudgets
