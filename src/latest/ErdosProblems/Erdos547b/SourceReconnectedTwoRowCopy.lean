/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceTerminalReconnectedCopy
import ErdosProblems.Erdos547b.SourceFiniteCapacityLayout
import ErdosProblems.Erdos547b.SourceExceptionalIdealGains
import ErdosProblems.Erdos547b.SourceMatchingVolume
import ErdosProblems.Erdos547b.SourceExceptionalRowBounds

/-!
# Reconnected ordinary forests from the actual two-row weight margins

Every source list, root image and branch image is constructed. All original
root images retain their high degree in the original host.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceReconnectedTwoRowCopy

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoSourceTerminalReconnectedCopy Erdos547b.ZhaoSourceReconnectedGraph
open Erdos547b.ZhaoSourceCapacityGlobalPrefix Erdos547b.ZhaoSourceFiniteCapacityLayout
open Erdos547b.ZhaoSourceCapacityBudgetMargins Erdos547b.ZhaoSourceMatchingVolume
open Erdos547b.ZhaoSourceExceptionalIdealGains Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSourceGlobalPrefixState (CutSource)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {r b : ℕ} (F : OrderedBranchForest r b) (rootSide : Fin r → Fin 2)

def sideFamily (s : Fin 2) : Finset (Fin b) :=
  Finset.univ.filter fun i => rootSide (F.owner i) = s

def sideLocate (i : Fin b) : Fin 2 × Fin 1 := (rootSide (F.owner i), 0)

variable (L : CutSource F.branches F.owner rootSide (sideLocate F rootSide))

include S in
theorem exists_reconnectedCopy_of_twoRowBudgets
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (E : Fin 2 → Finset (MatchingEdge Q.claim67.M)) (hdisjoint : Disjoint (E 0) (E 1))
    (haway : ∀ s, E s ⊆ awayEdges W Q)
    (hsmall : ∀ i, F.branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (r : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (hbudget : ∀ s, sideFamily F rootSide s ≠ ∅ →
      (∑ i ∈ sideFamily F rootSide s, (F.branches.size i : ℝ)) + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ E s, sideWeight W Q S s e) :
    ∃ f : (reconnectedGraph F L).Copy (embeddingHost W), ∀ i, q ≤ G.degree (f (Sum.inl i)) := by
  let family := fun (s : Fin 2) (_ : Fin 1) => familyList F.owner (sideFamily F rootSide s)
  have hcover : ∀ i, i ∈ family (sideLocate F rootSide i).1 (sideLocate F rootSide i).2 := by
    intro i
    exact (mem_familyList _ _ i).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
  have hkind : ∀ (_ : Fin 2) (_ : Fin 1), FamilyKind.Valid α (.threshold 0) := by
    intros
    constructor <;> norm_num
  have hside : ∀ s j i, i ∈ family s j → rootSide (F.owner i) = s := by
    intro s j i hi
    exact (Finset.mem_filter.mp ((mem_familyList _ _ i).mp hi)).2
  have hbudget' : ∀ s j, family s j ≠ [] → mass (fun i => (F.branches.size i : ℝ)) (family s j) ≤
      (∑ e ∈ E s, capacity W Q S (rootCluster W Q s) (.threshold 0) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (E s).card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * Fintype.card (MatchingEdge Q.claim67.M) := by
    intro s j hnonempty
    change mass _ (familyList _ _) ≤ _
    rw [mass_familyList]
    apply capacityBudget_of_ideal_margin W Q S (rootCluster W Q s) hα hα1 (.threshold 0) (E s)
      (Fintype.card (MatchingEdge Q.claim67.M)) (matchingVolume_bound W Q hhost _) (fullMatchingVolume_bound W Q hhost)
    have hne : sideFamily F rootSide s ≠ ∅ := by
      intro he
      apply hnonempty
      simp only [family, familyList, he, Finset.notMem_empty, decide_false, List.filter_false]
    simpa only [ordinary_idealCapacity] using hbudget s hne
  have hsameSide (s : Fin 2) : Pairwise (fun (_ _ : Fin 1) => Disjoint (E s) (E s)) := by
    intro i j hne
    exact (hne (Subsingleton.elim _ _)).elim
  obtain ⟨A⟩ := exists_terminalCutPrefix W Q S F.branches F.owner rootSide (fun _ _ => .threshold 0)
    (fun s (_ : Fin 1) => E s) family (sideLocate F rootSide) hcover L
    hα hα1 hhost horder (by decide) hkind hsameSide hside
    (fun _ _ i _ => ordinary_branchValid _ i) (by intros; trivial) hsmall (fun s _ => haway s)
    (Fintype.card (MatchingEdge Q.claim67.M)) (fun _ => Finset.card_le_univ _) hbudget' hroots
    (fun _ _ => familyList_nodup _ _) (fun _ _ => familyList_ordered _ _)
  have hallDisjoint : ∀ x y : Fin 2 × Fin 1, x ≠ y → Disjoint (E x.1) (E y.1) := by
    rintro ⟨s, i⟩ ⟨t, j⟩ hne
    have hst : s ≠ t := fun h => hne (Prod.ext h (Subsingleton.elim i j))
    fin_cases s <;> fin_cases t
    · exact (hst rfl).elim
    · exact hdisjoint
    · exact hdisjoint.symm
    · exact (hst rfl).elim
  exact ⟨terminalReconnectedCopy W Q S F rootSide _ _ family _ hcover L A hallDisjoint (fun s _ => haway s),
    terminalReconnectedCopy_root_high W Q S F rootSide _ _ family _ hcover L A hallDisjoint (fun s _ => haway s)⟩

end Erdos547b.ZhaoSourceReconnectedTwoRowCopy

#print axioms Erdos547b.ZhaoSourceReconnectedTwoRowCopy.exists_reconnectedCopy_of_twoRowBudgets
