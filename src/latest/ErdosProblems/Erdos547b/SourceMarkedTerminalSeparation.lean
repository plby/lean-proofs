/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedOrdinaryBranchSupport
import ErdosProblems.Erdos547b.SourcePrivateGroupSeparation

/-!
# Disjointness of the terminal combined branch images

Within a stored forest use its actual copy disjointness. Across ordinary
families use allocated matching edges; across the marked/ordinary split
use the source private-group separation theorem.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedGlobalPrefix

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourcePrivateGroupSeparation
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoLemma58DynamicBatchAppend

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (marks : ∀ i, Finset (Fin (F.size i))) (selected : Finset (Fin b))
variable (rootSide : Fin r → Fin 2) (kinds : Fin 2 → Fin k → FamilyKind)
variable (allocation : Fin 2 → Fin k → Finset (MatchingEdge Q.claim67.M))
variable (family : Fin 2 → Fin k → List (Fin b)) (locate : Fin b → Fin 2 × Fin k)
variable (hcover : ∀ i, i ∉ selected → i ∈ family (locate i).1 (locate i).2)
variable (A : PrefixState W Q S O P F owner marks selected rootSide kinds allocation family r)

theorem PrefixState.ordinary_copies_ne
    (hdisjoint : ∀ x y : Fin 2 × Fin k, x ≠ y → Disjoint (allocation x.1 x.2) (allocation y.1 y.2))
    (i j : Fin b) (hi : i ∉ selected) (hj : j ∉ selected) (hij : i ≠ j)
    (a : Fin (F.size i)) (d : Fin (F.size j)) :
    A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt a ≠
      A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover j (owner j).isLt d := by
  intro heq
  by_cases hloc : locate i = locate j
  · rw [A.branchCopy_eq_ordinary W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt hi,
      A.branchCopy_eq_ordinary W Q S O P F owner marks selected rootSide kinds allocation family locate hcover j (owner j).isLt hj] at heq
    have hfst := congrArg Prod.fst hloc
    have hsnd := congrArg Prod.snd hloc
    change (locate i).1 = (locate j).1 at hfst
    change (locate i).2 = (locate j).2 at hsnd
    let E := (A.ordinary.families (locate j).1 (locate j).2).currentPlacement W Q S
      (rootCluster W Q (locate j).1) F owner (kinds (locate j).1 (locate j).2)
    have hiMem : i ∈ (family (locate j).1 (locate j).2).toFinset.filter (fun i => (owner i).val < r) := by
      refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ?_, (owner i).isLt⟩
      simpa only [hfst, hsnd] using hcover i hi
    have hjMem : j ∈ (family (locate j).1 (locate j).2).toFinset.filter (fun i => (owner i).val < r) :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hcover j hj), (owner j).isLt⟩
    have heq' : E.forestCopy.componentCopy i hiMem a = E.forestCopy.componentCopy j hjMem d := by
      let eval : {p : Fin 2 × Fin k // i ∈ (family p.1 p.2).toFinset.filter (fun i => (owner i).val < r)} →
          Fin hostN := fun p =>
        ((A.ordinary.families p.1.1 p.1.2).currentPlacement W Q S
          (rootCluster W Q p.1.1) F owner (kinds p.1.1 p.1.2)).forestCopy.componentCopy i p.2 a
      have hindices : (⟨locate i, Finset.mem_filter.mpr
          ⟨List.mem_toFinset.mpr (hcover i hi), (owner i).isLt⟩⟩ :
          {p : Fin 2 × Fin k // i ∈ (family p.1 p.2).toFinset.filter (fun i => (owner i).val < r)}) =
          ⟨locate j, hiMem⟩ := Subtype.ext hloc
      exact (congrArg eval hindices).symm.trans heq
    exact Set.disjoint_left.mp (E.forestCopy.disjoint_ranges i hiMem j hjMem hij) ⟨a, rfl⟩ ⟨d, heq'.symm⟩
  · obtain ⟨e, he, c, ha⟩ := A.ordinary_branch_support W Q S F owner O P marks selected rootSide kinds allocation family locate hcover
      i hi (owner i).isLt a
    obtain ⟨f, hf, l, hd⟩ := A.ordinary_branch_support W Q S F owner O P marks selected rootSide kinds allocation family locate hcover
      j hj (owner j).isLt d
    have hef : e ≠ f := fun h => Finset.disjoint_left.mp (hdisjoint (locate i) (locate j) hloc) he (h.symm ▸ hf)
    exact Finset.disjoint_left.mp (edgeWhole_cross_disjoint W Q e f hef c l) ha (heq.symm ▸ hd)

theorem PrefixState.marked_copies_ne
    (i j : Fin b) (hi : i ∈ selected) (hj : j ∈ selected) (hij : i ≠ j)
    (a : Fin (F.size i)) (d : Fin (F.size j)) :
    A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt a ≠
      A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover j (owner j).isLt d := by
  intro heq
  rw [A.branchCopy_eq_marked W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt hi,
    A.branchCopy_eq_marked W Q S O P F owner marks selected rootSide kinds allocation family locate hcover j (owner j).isLt hj] at heq
  exact Set.disjoint_left.mp (A.marked.forestCopy.disjoint_ranges i (Finset.mem_filter.mpr ⟨hi, (owner i).isLt⟩)
    j (Finset.mem_filter.mpr ⟨hj, (owner j).isLt⟩) hij) ⟨a, rfl⟩ ⟨d, heq.symm⟩

theorem PrefixState.mixed_copies_ne (hCV1 : C ⊆ O.D.V1)
    (hresidual : ∀ s j e, e ∈ allocation s j →
      e ∈ O.D.minEdges \ MatchingDecomposition.MzeroEdges O.D C ∨ e ∈ O.D.mbEdges)
    (i j : Fin b) (hi : i ∈ selected) (hj : j ∉ selected)
    (a : Fin (F.size i)) (d : Fin (F.size j)) :
    A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt a ≠
      A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover j (owner j).isLt d := by
  intro heq
  let himem : i ∈ ownerPrefix selected owner r := Finset.mem_filter.mpr ⟨hi, (owner i).isLt⟩
  let x := A.marked.group ⟨i, himem⟩
  have ha : A.branchCopy W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt a ∈
      P.support W Q S O x := by
    rw [A.branchCopy_eq_marked W Q S O P F owner marks selected rootSide kinds allocation family locate hcover i (owner i).isLt hi]
    exact A.marked_copy_mem_support W Q S O P F owner marks selected rootSide kinds allocation family i himem a
  obtain ⟨e, he, c, hd⟩ := A.ordinary_branch_support W Q S F owner O P marks selected rootSide kinds allocation family locate hcover
    j hj (owner j).isLt d
  have hpair : edgeWhole W Q e c ⊆ pairWhole W Q e := by
    rcases OrderedRootedForest.fin_two_eq_zero_or_one c with rfl | rfl
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  exact Finset.disjoint_left.mp (group_disjoint_ordinary W Q S O P hCV1 e (hresidual _ _ e he) x)
    ha (heq.symm ▸ hpair hd)

end Erdos547b.ZhaoSourceMarkedGlobalPrefix

#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.ordinary_copies_ne
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.marked_copies_ne
#print axioms Erdos547b.ZhaoSourceMarkedGlobalPrefix.PrefixState.mixed_copies_ne
