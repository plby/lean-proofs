/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingFamilyState

/-!
# Source-list and reservation facts for a family allocation step

The exact concatenation invariant gives order, nonrepetition and mass
identities. If a current-owner branch remains unreserved, every branch in
the old active chunk has owner at most the current one.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingFamilyState

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceMatchingPendingPlan Erdos547b.ZhaoSourceFreshChunkBounds

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (P : (padGraph (reduced W)).Subgraph) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable {all : Finset (MatchingEdge P)} {family : List (Fin b)}
variable {rootImage : Fin r → Fin hostN} {stage : ℕ}
variable (A : FamilyState W Q S P C F owner all family rootImage stage)

abbrev FamilyState.reservedItems := A.completed ++ activeItems W Q S P C F owner A.active
abbrev FamilyState.reservedEdges := A.closedEdges ∪ activeEdges W Q S P C F owner A.active

theorem FamilyState.reserved_nodup : (A.reservedItems W Q S P C F owner).Nodup := by
  have h : (A.completed ++ activeItems W Q S P C F owner A.active ++ A.remaining).Nodup :=
    A.flatten.symm ▸ A.family_nodup
  exact (List.nodup_append.mp h).1

theorem FamilyState.reserved_order :
    (A.reservedItems W Q S P C F owner).Pairwise (fun i j => owner i ≤ owner j) := by
  have h : (A.completed ++ activeItems W Q S P C F owner A.active ++ A.remaining).Pairwise
      (fun i j => owner i ≤ owner j) := A.flatten.symm ▸ A.family_order
  exact (List.pairwise_append.mp h).1

theorem FamilyState.remaining_order : A.remaining.Pairwise (fun i j => owner i ≤ owner j) := by
  have h : (A.completed ++ activeItems W Q S P C F owner A.active ++ A.remaining).Pairwise
      (fun i j => owner i ≤ owner j) := A.flatten.symm ▸ A.family_order
  exact (List.pairwise_append.mp h).2.1

theorem FamilyState.reserved_before_remaining :
    ∀ i ∈ A.reservedItems W Q S P C F owner, ∀ j ∈ A.remaining, owner i ≤ owner j := by
  have h : (A.completed ++ activeItems W Q S P C F owner A.active ++ A.remaining).Pairwise
      (fun i j => owner i ≤ owner j) := A.flatten.symm ▸ A.family_order
  exact (List.pairwise_append.mp h).2.2

theorem FamilyState.completed_active_items_disjoint :
    Disjoint A.completed.toFinset (activeItems W Q S P C F owner A.active).toFinset := by
  have h := (List.nodup_append.mp (A.reserved_nodup W Q S P C F owner)).2.2
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact h i (List.mem_toFinset.mp hi) i (List.mem_toFinset.mp hj) rfl

theorem FamilyState.reserved_remaining_disjoint :
    Disjoint (A.reservedItems W Q S P C F owner).toFinset A.remaining.toFinset := by
  have hnd : (A.completed ++ activeItems W Q S P C F owner A.active ++ A.remaining).Nodup :=
    A.flatten.symm ▸ A.family_nodup
  have h := (List.nodup_append.mp hnd).2.2
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact h i (List.mem_toFinset.mp hi) i (List.mem_toFinset.mp hj) rfl

theorem FamilyState.reserved_mass_split :
    mass (fun i => (F.size i : ℝ)) (A.reservedItems W Q S P C F owner) +
      mass (fun i => (F.size i : ℝ)) A.remaining = mass (fun i => (F.size i : ℝ)) family := by
  have h := congrArg (mass (fun i => (F.size i : ℝ))) A.flatten
  simpa only [mass, FamilyState.reservedItems, List.map_append, List.sum_append] using h

theorem FamilyState.reserved_edges_subset : A.reservedEdges W Q S P C F owner ⊆ all :=
  Finset.union_subset A.closed_subset A.active_subset

theorem FamilyState.reserved_before_succ_of_current (n : Fin r)
    (hcurrent : ∃ i ∈ A.remaining, owner i = n) :
    ∀ i ∈ A.reservedItems W Q S P C F owner, (owner i).val < n.val + 1 := by
  obtain ⟨j, hj, howner⟩ := hcurrent
  intro i hi
  have h := A.reserved_before_remaining W Q S P C F owner i hi j hj
  rw [howner] at h
  exact Nat.lt_succ_of_le h

theorem FamilyState.ledger_of_current (n : Fin r)
    (hcurrent : ∃ i ∈ A.remaining, owner i = n) :
    (∑ e ∈ A.reservedEdges W Q S P C F owner,
      (capacity W Q P S C e - freshBranchBound α W.clusterSize)) ≤
        mass (fun i => (F.size i : ℝ)) (A.reservedItems W Q S P C F owner) := by
  apply A.reserved_ledger
  intro hnil
  obtain ⟨i, hi, _⟩ := hcurrent
  rw [hnil] at hi
  exact List.not_mem_nil hi

end Erdos547b.ZhaoSourceMatchingFamilyState

#print axioms Erdos547b.ZhaoSourceMatchingFamilyState.FamilyState.reserved_before_remaining
#print axioms Erdos547b.ZhaoSourceMatchingFamilyState.FamilyState.reserved_mass_split
#print axioms Erdos547b.ZhaoSourceMatchingFamilyState.FamilyState.reserved_before_succ_of_current
#print axioms Erdos547b.ZhaoSourceMatchingFamilyState.FamilyState.ledger_of_current
