/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceGeneralizedChunkInitial
import ErdosProblems.Erdos547b.SourceReservationFamilyState

/-!
# Actual family state with a concrete threshold or Appendix capacity

The ledger uses the family's real capacity. Active graph data contain the
appropriate concrete prefix, not a presumed continuation. The original
source-domain and copy-preservation identities remain exact.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityFamilyState

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoSourcePendingPlacement Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourcePendingOwnerInterval Erdos547b.ZhaoSourceActiveChunk
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoSourceGeneralizedChunk

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)

structure ActiveState (rootImage : Fin r → Fin hostN) (n : ℕ) where
  source : ChunkSource W Q S C F owner kind
  backend : source.Backend W Q S C F owner kind
  copyPrefix : source.Prefix W Q S C F owner kind backend rootImage n
  root_positive : ∀ i, 0 < rootDensity W S (Sum.inl C)
    (edgeVertex W Q source.edge ((source.chosen W Q S C F owner kind copyPrefix).orient i 0))

/-- Store a constructed concrete prefix without altering any image. -/
def activeStateOfPrefix (hα : 0 < α) (hkind : kind.Valid α)
    (D : ChunkSource W Q S C F owner kind) (backend : D.Backend W Q S C F owner kind)
    {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S C F owner kind backend rootImage n) :
    ActiveState W Q S C F owner kind rootImage n where
  source := D
  backend := backend
  copyPrefix := E
  root_positive := D.chosen_root_positive W Q S C F owner kind hα hkind E

def activeItems {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (ActiveState W Q S C F owner kind rootImage n)) : List (Fin b) :=
  match a with
  | none => []
  | some x => x.source.items

def activeEdges {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (ActiveState W Q S C F owner kind rootImage n)) : Finset (MatchingEdge Q.claim67.M) :=
  match a with
  | none => ∅
  | some x => {x.source.edge}

def activeSelected {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (ActiveState W Q S C F owner kind rootImage n)) : Finset (Fin b) :=
  match a with
  | none => ∅
  | some x => prefixSelected x.source.items (ownerCutoff (listOwner owner x.source.items) n)

def activePlacement {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (ActiveState W Q S C F owner kind rootImage n)) :
    BranchPlacement F (embeddingHost W) (activeSelected W Q S C F owner kind a)
      (fun i => rootImage (owner i)) (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) :=
  match a with
  | none => BranchPlacement.empty F (embeddingHost W) (fun i => rootImage (owner i)) _
  | some x => x.source.placement W Q S C F owner kind x.copyPrefix

theorem activeSelected_eq_filter {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (ActiveState W Q S C F owner kind rootImage n)) :
    activeSelected W Q S C F owner kind a =
      (activeItems W Q S C F owner kind a).toFinset.filter (fun i => (owner i).val < n) := by
  cases a with
  | none => simp [activeSelected, activeItems]
  | some x => exact prefixSelected_ownerCutoff x.source.items owner x.source.owner_mono n

theorem activePlacement_edge_mem {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (ActiveState W Q S C F owner kind rootImage n))
    (i : {i // i ∈ activeSelected W Q S C F owner kind a}) :
    (activePlacement W Q S C F owner kind a).edge i ∈ activeEdges W Q S C F owner kind a := by
  cases a with
  | none => exact (Finset.notMem_empty _ i.2).elim
  | some x => exact Finset.mem_singleton.mpr rfl

theorem activePlacement_root_positive {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (ActiveState W Q S C F owner kind rootImage n))
    (i : {i // i ∈ activeSelected W Q S C F owner kind a}) :
    0 < rootDensity W S (Sum.inl C)
      (edgeVertex W Q ((activePlacement W Q S C F owner kind a).edge i)
        ((activePlacement W Q S C F owner kind a).orient i 0)) := by
  cases a with
  | none => exact (Finset.notMem_empty _ i.2).elim
  | some x => exact x.root_positive (position x.source.items i.1 (prefixSelected_mem_items i.2))

structure FamilyState (all : Finset (MatchingEdge Q.claim67.M)) (family : List (Fin b))
    (rootImage : Fin r → Fin hostN) (n : ℕ) where
  family_nodup : family.Nodup
  family_order : family.Pairwise (fun i j => owner i ≤ owner j)
  completed : List (Fin b)
  active : Option (ActiveState W Q S C F owner kind rootImage n)
  remaining : List (Fin b)
  flatten : completed ++ activeItems W Q S C F owner kind active ++ remaining = family
  completed_before : ∀ i ∈ completed, (owner i).val < n
  remaining_after : ∀ i ∈ remaining, n ≤ (owner i).val
  closedEdges : Finset (MatchingEdge Q.claim67.M)
  closed_subset : closedEdges ⊆ all
  active_subset : activeEdges W Q S C F owner kind active ⊆ all
  edge_disjoint : Disjoint closedEdges (activeEdges W Q S C F owner kind active)
  closed : BranchPlacement F (embeddingHost W) completed.toFinset (fun i => rootImage (owner i))
    (fun e => residualSide (edgeWhole W Q e) (deleted W Q e))
  closed_edge_mem : ∀ i, closed.edge i ∈ closedEdges
  closed_root_positive : ∀ i, 0 < rootDensity W S (Sum.inl C)
    (edgeVertex W Q (closed.edge i) (closed.orient i 0))
  reserved_ledger : remaining ≠ [] →
    (∑ e ∈ closedEdges ∪ activeEdges W Q S C F owner kind active,
      (capacity W Q S C kind e - freshBranchBound α W.clusterSize)) ≤
        mass (fun i => (F.size i : ℝ)) (completed ++ activeItems W Q S C F owner kind active)

variable {all : Finset (MatchingEdge Q.claim67.M)} {family : List (Fin b)}
variable {rootImage : Fin r → Fin hostN} {n : ℕ}
variable (A : FamilyState W Q S C F owner kind all family rootImage n)

theorem FamilyState.domain_eq :
    A.completed.toFinset ∪ activeSelected W Q S C F owner kind A.active =
      family.toFinset.filter (fun i => (owner i).val < n) := by
  have hclosed : A.completed.toFinset.filter (fun i => (owner i).val < n) = A.completed.toFinset := by
    exact Finset.filter_eq_self.mpr (fun i hi => A.completed_before i (List.mem_toFinset.mp hi))
  have hremaining : A.remaining.toFinset.filter (fun i => (owner i).val < n) = ∅ := by
    exact Finset.filter_eq_empty_iff.mpr (fun i hi hlt =>
      (not_lt_of_ge (A.remaining_after i (List.mem_toFinset.mp hi))) hlt)
  have h := congrArg (fun l : List (Fin b) => l.toFinset.filter (fun i => (owner i).val < n)) A.flatten
  simp only [List.toFinset_append, Finset.filter_union, hclosed, hremaining, Finset.union_empty] at h
  rw [activeSelected_eq_filter]
  exact h

theorem FamilyState.completed_active_source_disjoint :
    Disjoint A.completed.toFinset (activeSelected W Q S C F owner kind A.active) := by
  have hnd : (A.completed ++ activeItems W Q S C F owner kind A.active ++ A.remaining).Nodup :=
    A.flatten.symm ▸ A.family_nodup
  have hd := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2
  apply Finset.disjoint_left.mpr
  intro i hi hj
  rw [activeSelected_eq_filter] at hj
  have hm := List.mem_toFinset.mp (Finset.mem_filter.mp hj).1
  exact hd i (List.mem_toFinset.mp hi) i hm rfl

theorem FamilyState.closed_active_support_disjoint :
    ∀ i : {i // i ∈ A.completed.toFinset},
      ∀ j : {j // j ∈ activeSelected W Q S C F owner kind A.active}, ∀ c d,
        Disjoint (residualSide (edgeWhole W Q (A.closed.edge i)) (deleted W Q (A.closed.edge i)) c)
          (residualSide (edgeWhole W Q ((activePlacement W Q S C F owner kind A.active).edge j))
            (deleted W Q ((activePlacement W Q S C F owner kind A.active).edge j)) d) := by
  intro i j c d
  have hi := A.closed_edge_mem i
  have hj := activePlacement_edge_mem W Q S C F owner kind A.active j
  have hne : A.closed.edge i ≠ (activePlacement W Q S C F owner kind A.active).edge j := by
    intro heq
    exact Finset.disjoint_left.mp A.edge_disjoint hi (heq.symm ▸ hj)
  exact (edgeWhole_cross_disjoint W Q _ _ hne c d).mono Finset.sdiff_subset Finset.sdiff_subset

def FamilyState.unionPlacement :
    BranchPlacement F (embeddingHost W)
      (A.completed.toFinset ∪ activeSelected W Q S C F owner kind A.active)
      (fun i => rootImage (owner i)) (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) :=
  A.closed.append (activePlacement W Q S C F owner kind A.active)
    (A.closed_active_support_disjoint W Q S C F owner kind)

theorem FamilyState.union_root_positive
    (i : {i // i ∈ A.completed.toFinset ∪ activeSelected W Q S C F owner kind A.active}) :
    0 < rootDensity W S (Sum.inl C)
      (edgeVertex W Q ((A.unionPlacement W Q S C F owner kind).edge i)
        ((A.unionPlacement W Q S C F owner kind).orient i 0)) := by
  by_cases hi : i.1 ∈ A.completed.toFinset
  · simpa only [FamilyState.unionPlacement, BranchPlacement.append, dif_pos hi] using
      A.closed_root_positive ⟨i.1, hi⟩
  · have ha := (Finset.mem_union.mp i.2).resolve_left hi
    simpa only [FamilyState.unionPlacement, BranchPlacement.append, dif_neg hi] using
      activePlacement_root_positive W Q S C F owner kind A.active ⟨i.1, ha⟩

def FamilyState.currentPlacement :
    BranchPlacement F (embeddingHost W) (family.toFinset.filter (fun i => (owner i).val < n))
      (fun i => rootImage (owner i)) (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) :=
  Erdos547b.ZhaoSourceReservationFamilyState.castPlacement W Q F owner
    (A.domain_eq W Q S C F owner kind) (A.unionPlacement W Q S C F owner kind)

theorem FamilyState.current_root_positive
    (i : {i // i ∈ family.toFinset.filter (fun i => (owner i).val < n)}) :
    0 < rootDensity W S (Sum.inl C)
      (edgeVertex W Q ((A.currentPlacement W Q S C F owner kind).edge i)
        ((A.currentPlacement W Q S C F owner kind).orient i 0)) :=
  A.union_root_positive W Q S C F owner kind ⟨i.1, (A.domain_eq W Q S C F owner kind).symm ▸ i.2⟩

theorem FamilyState.current_copy_completed (i : Fin b) (hi : i ∈ A.completed.toFinset) :
    (A.currentPlacement W Q S C F owner kind).forestCopy.componentCopy i
        ((A.domain_eq W Q S C F owner kind) ▸ Finset.mem_union_left _ hi) =
      A.closed.forestCopy.componentCopy i hi :=
  A.closed.append_copy_left (activePlacement W Q S C F owner kind A.active)
    (A.closed_active_support_disjoint W Q S C F owner kind) i hi

theorem FamilyState.current_copy_active (i : Fin b)
    (hi : i ∈ activeSelected W Q S C F owner kind A.active) :
    (A.currentPlacement W Q S C F owner kind).forestCopy.componentCopy i
        ((A.domain_eq W Q S C F owner kind) ▸ Finset.mem_union_right _ hi) =
      (activePlacement W Q S C F owner kind A.active).forestCopy.componentCopy i hi :=
  A.closed.append_copy_right (activePlacement W Q S C F owner kind A.active)
    (A.closed_active_support_disjoint W Q S C F owner kind)
    (A.completed_active_source_disjoint W Q S C F owner kind) i hi

def emptyFamilyState (all : Finset (MatchingEdge Q.claim67.M)) (family : List (Fin b))
    (hnd : family.Nodup) (horder : family.Pairwise (fun i j => owner i ≤ owner j))
    (rootImage : Fin r → Fin hostN) : FamilyState W Q S C F owner kind all family rootImage 0 where
  family_nodup := hnd
  family_order := horder
  completed := []
  active := none
  remaining := family
  flatten := by simp [activeItems]
  completed_before := by simp
  remaining_after := fun _ _ => Nat.zero_le _
  closedEdges := ∅
  closed_subset := Finset.empty_subset _
  active_subset := Finset.empty_subset _
  edge_disjoint := Finset.disjoint_empty_left _
  closed := BranchPlacement.empty F (embeddingHost W) (fun i => rootImage (owner i)) _
  closed_edge_mem := fun i => (Finset.notMem_empty _ i.2).elim
  closed_root_positive := fun i => (Finset.notMem_empty _ i.2).elim
  reserved_ledger := by intro _; simp [activeEdges, activeItems, mass]

end Erdos547b.ZhaoSourceCapacityFamilyState

#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.activeStateOfPrefix
#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.FamilyState.domain_eq
#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.FamilyState.current_root_positive
#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.FamilyState.current_copy_completed
#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.FamilyState.current_copy_active
#print axioms Erdos547b.ZhaoSourceCapacityFamilyState.emptyFamilyState
