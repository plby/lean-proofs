/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingActiveChunk

/-!
# Ordinary reservation state for an arbitrary physical matching

The source list is split into completed, active, and unreserved portions.
Completed copies and the active owner prefix give an actual original-index
placement of exactly the processed owners. The reserved-mass ledger is
separate from the actual graph-copy domain.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingFamilyState

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoSourcePendingPlacement Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourcePendingOwnerInterval Erdos547b.ZhaoSourceMatchingActiveChunk
open Erdos547b.ZhaoSourceActiveChunk (prefixSelected_ownerCutoff)
open Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceMatchingGeometry Erdos547b.ZhaoSourceMatchingPendingPlan
open Erdos547b.ZhaoSourceMatchingParentCleanup Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (P : (padGraph (reduced W)).Subgraph) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

abbrev Active (rootImage : Fin r → Fin hostN) (n : ℕ) :=
  Σ D : PendingChunk W Q S P C F owner, D.Prefix W Q S P C F owner rootImage n

def activeItems {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (Active W Q S P C F owner rootImage n)) : List (Fin b) :=
  match a with
  | none => []
  | some x => x.1.items

def activeEdges {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (Active W Q S P C F owner rootImage n)) : Finset (MatchingEdge P) :=
  match a with
  | none => ∅
  | some x => {x.1.edge}

def activeSelected {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (Active W Q S P C F owner rootImage n)) : Finset (Fin b) :=
  match a with
  | none => ∅
  | some x => prefixSelected x.1.items (ownerCutoff (listOwner owner x.1.items) n)

def activePlacement {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (Active W Q S P C F owner rootImage n)) :
    BranchPlacement F (embeddingHost W) (activeSelected W Q S P C F owner a)
      (fun i => rootImage (owner i)) (fun e => residualSide (pairWhole W P e) (deleted W Q P e)) :=
  match a with
  | none => BranchPlacement.empty F (embeddingHost W) (fun i => rootImage (owner i)) _
  | some x => x.1.placement W Q S P C F owner x.2

theorem activeSelected_eq_filter {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (Active W Q S P C F owner rootImage n)) :
    activeSelected W Q S P C F owner a =
      (activeItems W Q S P C F owner a).toFinset.filter (fun i => (owner i).val < n) := by
  cases a with
  | none => simp [activeSelected, activeItems]
  | some x => exact prefixSelected_ownerCutoff x.1.items owner x.1.owner_mono n

theorem activePlacement_edge_mem {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (Active W Q S P C F owner rootImage n))
    (i : {i // i ∈ activeSelected W Q S P C F owner a}) :
    (activePlacement W Q S P C F owner a).edge i ∈ activeEdges W Q S P C F owner a := by
  cases a with
  | none => exact (Finset.notMem_empty _ i.2).elim
  | some x => exact Finset.mem_singleton.mpr rfl

theorem activePlacement_root_positive {rootImage : Fin r → Fin hostN} {n : ℕ}
    (a : Option (Active W Q S P C F owner rootImage n))
    (i : {i // i ∈ activeSelected W Q S P C F owner a}) :
    0 < rootDensity W S (Sum.inl C)
      (pairVertex W P ((activePlacement W Q S P C F owner a).edge i)
        ((activePlacement W Q S P C F owner a).orient i 0)) := by
  cases a with
  | none => exact (Finset.notMem_empty _ i.2).elim
  | some x =>
      exact x.1.plan.root_positive (position x.1.items i.1 (prefixSelected_mem_items i.2))

/-- All graph and source data at one global owner boundary. -/
structure FamilyState (all : Finset (MatchingEdge P)) (family : List (Fin b))
    (rootImage : Fin r → Fin hostN) (n : ℕ) where
  matching : P.IsMatching
  family_nodup : family.Nodup
  family_order : family.Pairwise (fun i j => owner i ≤ owner j)
  completed : List (Fin b)
  active : Option (Active W Q S P C F owner rootImage n)
  remaining : List (Fin b)
  flatten : completed ++ activeItems W Q S P C F owner active ++ remaining = family
  completed_before : ∀ i ∈ completed, (owner i).val < n
  remaining_after : ∀ i ∈ remaining, n ≤ (owner i).val
  closedEdges : Finset (MatchingEdge P)
  closed_subset : closedEdges ⊆ all
  active_subset : activeEdges W Q S P C F owner active ⊆ all
  edge_disjoint : Disjoint closedEdges (activeEdges W Q S P C F owner active)
  closed : BranchPlacement F (embeddingHost W) completed.toFinset (fun i => rootImage (owner i))
    (fun e => residualSide (pairWhole W P e) (deleted W Q P e))
  closed_edge_mem : ∀ i, closed.edge i ∈ closedEdges
  closed_root_positive : ∀ i, 0 < rootDensity W S (Sum.inl C)
    (pairVertex W P (closed.edge i) (closed.orient i 0))
  reserved_ledger : remaining ≠ [] →
    (∑ e ∈ closedEdges ∪ activeEdges W Q S P C F owner active,
      (capacity W Q P S C e - freshBranchBound α W.clusterSize)) ≤
        mass (fun i => (F.size i : ℝ)) (completed ++ activeItems W Q S P C F owner active)

variable {all : Finset (MatchingEdge P)} {family : List (Fin b)}
variable {rootImage : Fin r → Fin hostN} {n : ℕ}
variable (A : FamilyState W Q S P C F owner all family rootImage n)

/-- The actual copied source domain is exactly the earlier owners. -/
theorem FamilyState.domain_eq :
    A.completed.toFinset ∪ activeSelected W Q S P C F owner A.active =
      family.toFinset.filter (fun i => (owner i).val < n) := by
  have hclosed : A.completed.toFinset.filter (fun i => (owner i).val < n) = A.completed.toFinset := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact A.completed_before i (List.mem_toFinset.mp hi)
  have hremaining : A.remaining.toFinset.filter (fun i => (owner i).val < n) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi hlt
    exact (not_lt_of_ge (A.remaining_after i (List.mem_toFinset.mp hi))) hlt
  have h := congrArg (fun l : List (Fin b) => l.toFinset.filter (fun i => (owner i).val < n)) A.flatten
  simp only [List.toFinset_append, Finset.filter_union, hclosed, hremaining, Finset.union_empty] at h
  rw [activeSelected_eq_filter]
  exact h

theorem FamilyState.completed_active_source_disjoint :
    Disjoint A.completed.toFinset (activeSelected W Q S P C F owner A.active) := by
  have hnd : (A.completed ++ activeItems W Q S P C F owner A.active ++ A.remaining).Nodup :=
    A.flatten.symm ▸ A.family_nodup
  have hd := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2
  apply Finset.disjoint_left.mpr
  intro i hi hj
  rw [activeSelected_eq_filter] at hj
  have hm := List.mem_toFinset.mp (Finset.mem_filter.mp hj).1
  exact hd i (List.mem_toFinset.mp hi) i hm rfl

/-- Distinct recorded matching edges separate the completed and active
graph images, regardless of how many source vertices remain reserved. -/
theorem FamilyState.closed_active_support_disjoint :
    ∀ i : {i // i ∈ A.completed.toFinset},
      ∀ j : {j // j ∈ activeSelected W Q S P C F owner A.active}, ∀ c d,
        Disjoint (residualSide (pairWhole W P (A.closed.edge i)) (deleted W Q P (A.closed.edge i)) c)
          (residualSide (pairWhole W P ((activePlacement W Q S P C F owner A.active).edge j))
            (deleted W Q P ((activePlacement W Q S P C F owner A.active).edge j)) d) := by
  intro i j c d
  have hi := A.closed_edge_mem i
  have hj := activePlacement_edge_mem W Q S P C F owner A.active j
  have hne : A.closed.edge i ≠ (activePlacement W Q S P C F owner A.active).edge j := by
    intro heq
    exact Finset.disjoint_left.mp A.edge_disjoint hi (heq.symm ▸ hj)
  exact (pairWhole_cross_disjoint W P A.matching _ _ hne c d).mono Finset.sdiff_subset Finset.sdiff_subset

/-- The union placement uses only already constructed graph copies. -/
def FamilyState.unionPlacement :
    BranchPlacement F (embeddingHost W)
      (A.completed.toFinset ∪ activeSelected W Q S P C F owner A.active)
      (fun i => rootImage (owner i)) (fun e => residualSide (pairWhole W P e) (deleted W Q P e)) :=
  A.closed.append (activePlacement W Q S P C F owner A.active)
    (A.closed_active_support_disjoint W Q S P C F owner)

theorem FamilyState.union_root_positive
    (i : {i // i ∈ A.completed.toFinset ∪ activeSelected W Q S P C F owner A.active}) :
    0 < rootDensity W S (Sum.inl C)
      (pairVertex W P ((A.unionPlacement W Q S P C F owner).edge i)
        ((A.unionPlacement W Q S P C F owner).orient i 0)) := by
  by_cases hi : i.1 ∈ A.completed.toFinset
  · simpa only [FamilyState.unionPlacement, BranchPlacement.append, dif_pos hi] using
      A.closed_root_positive ⟨i.1, hi⟩
  · have ha := (Finset.mem_union.mp i.2).resolve_left hi
    simpa only [FamilyState.unionPlacement, BranchPlacement.append, dif_neg hi] using
      activePlacement_root_positive W Q S P C F owner A.active ⟨i.1, ha⟩

/-- Transport only the selected-domain equality, preserving every copy. -/
def castPlacement {s t : Finset (Fin b)} (hst : s = t)
    (E : BranchPlacement F (embeddingHost W) s (fun i => rootImage (owner i))
      (fun e => residualSide (pairWhole W P e) (deleted W Q P e))) :
    BranchPlacement F (embeddingHost W) t (fun i => rootImage (owner i))
      (fun e => residualSide (pairWhole W P e) (deleted W Q P e)) where
  edge i := E.edge ⟨i.1, hst.symm ▸ i.2⟩
  orient i := E.orient ⟨i.1, hst.symm ▸ i.2⟩
  forestCopy := {
    componentCopy := fun i hi => E.forestCopy.componentCopy i (hst.symm ▸ hi)
    disjoint_ranges := fun i hi j hj hne => E.forestCopy.disjoint_ranges i (hst.symm ▸ hi) j (hst.symm ▸ hj) hne }
  attach i hi := E.attach i (hst.symm ▸ hi)
  map_side i hi a := E.map_side i (hst.symm ▸ hi) a

/-- A genuine placement of every family branch belonging to an already
processed global owner; unchosen future roots contribute no graph premise. -/
def FamilyState.currentPlacement :
    BranchPlacement F (embeddingHost W) (family.toFinset.filter (fun i => (owner i).val < n))
      (fun i => rootImage (owner i)) (fun e => residualSide (pairWhole W P e) (deleted W Q P e)) :=
  castPlacement W Q P F owner (A.domain_eq W Q S P C F owner) (A.unionPlacement W Q S P C F owner)

theorem FamilyState.current_root_positive
    (i : {i // i ∈ family.toFinset.filter (fun i => (owner i).val < n)}) :
    0 < rootDensity W S (Sum.inl C)
      (pairVertex W P ((A.currentPlacement W Q S P C F owner).edge i)
        ((A.currentPlacement W Q S P C F owner).orient i 0)) :=
  A.union_root_positive W Q S P C F owner ⟨i.1, (A.domain_eq W Q S P C F owner).symm ▸ i.2⟩

theorem FamilyState.current_copy_completed (i : Fin b) (hi : i ∈ A.completed.toFinset) :
    (A.currentPlacement W Q S P C F owner).forestCopy.componentCopy i
        ((A.domain_eq W Q S P C F owner) ▸ Finset.mem_union_left _ hi) =
      A.closed.forestCopy.componentCopy i hi := by
  exact A.closed.append_copy_left (activePlacement W Q S P C F owner A.active)
    (A.closed_active_support_disjoint W Q S P C F owner) i hi

theorem FamilyState.current_copy_active (i : Fin b)
    (hi : i ∈ activeSelected W Q S P C F owner A.active) :
    (A.currentPlacement W Q S P C F owner).forestCopy.componentCopy i
        ((A.domain_eq W Q S P C F owner) ▸ Finset.mem_union_right _ hi) =
      (activePlacement W Q S P C F owner A.active).forestCopy.componentCopy i hi := by
  exact A.closed.append_copy_right (activePlacement W Q S P C F owner A.active)
    (A.closed_active_support_disjoint W Q S P C F owner)
    (A.completed_active_source_disjoint W Q S P C F owner) i hi

/-- Empty initialization for any total root map, whose values are still
unconstrained at this stage. No matching edge or graph image is invented. -/
def emptyFamilyState (hP : P.IsMatching) (all : Finset (MatchingEdge P)) (family : List (Fin b))
    (hnd : family.Nodup) (horder : family.Pairwise (fun i j => owner i ≤ owner j))
    (rootImage : Fin r → Fin hostN) : FamilyState W Q S P C F owner all family rootImage 0 where
  matching := hP
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

end Erdos547b.ZhaoSourceMatchingFamilyState

#print axioms Erdos547b.ZhaoSourceMatchingFamilyState.FamilyState.domain_eq
#print axioms Erdos547b.ZhaoSourceMatchingFamilyState.FamilyState.closed_active_support_disjoint
#print axioms Erdos547b.ZhaoSourceMatchingFamilyState.FamilyState.currentPlacement
#print axioms Erdos547b.ZhaoSourceMatchingFamilyState.FamilyState.current_root_positive
#print axioms Erdos547b.ZhaoSourceMatchingFamilyState.FamilyState.current_copy_completed
#print axioms Erdos547b.ZhaoSourceMatchingFamilyState.FamilyState.current_copy_active
#print axioms Erdos547b.ZhaoSourceMatchingFamilyState.emptyFamilyState
