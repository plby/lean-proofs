/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityFamilyRequirements
import ErdosProblems.Erdos547b.SourceAbsoluteBadBudget
import ErdosProblems.Erdos547b.SourceOwnerListSplit

/-!
# Actual current-owner packing from a capacity-aware family ledger

Both concrete capacities obey the same two-cluster bad-edge cost bound.
The reserved source ledger and total family budget therefore construct a
saturated packing of the current owner into the retained unused edges.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityFamilyPacking

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceAbsoluteBadBudget
open Erdos547b.ZhaoSourceOwnerListSplit

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W) (kind : FamilyKind)

def capacityBins (all used bad : Finset (MatchingEdge Q.claim67.M)) : List (MatchingEdge Q.claim67.M) :=
  (((all \ used) \ bad).filter (fun e => (freshBranchBound α W.clusterSize : ℝ) <
    capacity W Q S C kind e)).toList

theorem mem_capacityBins (all used bad : Finset (MatchingEdge Q.claim67.M)) (e : MatchingEdge Q.claim67.M) :
    e ∈ capacityBins W Q S C kind all used bad ↔
      e ∈ (all \ used) \ bad ∧ (freshBranchBound α W.clusterSize : ℝ) < capacity W Q S C kind e := by
  simp only [capacityBins, Finset.mem_toList, Finset.mem_filter]

variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

theorem exists_currentOwnerPacking
    (hα : 0 < α) (hC : C = Q.A ∨ C = Q.B) (hkind : kind.Valid α)
    {all : Finset (MatchingEdge Q.claim67.M)} {family : List (Fin b)}
    (hedge : ∀ e ∈ all, edgeValid W Q S C kind e)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (A : FamilyState W Q S C F owner kind all family rootImage n.val)
    (hcurrent : ∃ i ∈ A.remaining, owner i = n)
    (globalCount : ℕ)
    (hbudget : mass (fun i => (F.size i : ℝ)) family ≤
      (∑ e ∈ all, capacity W Q S C kind e) -
        (freshBranchBound α W.clusterSize : ℝ) * all.card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
    (bad : Finset (MatchingEdge Q.claim67.M))
    (hbad : bad ⊆ A.unusedEdges W Q S C F owner kind)
    (hcount : (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * globalCount) :
    ∃ R : OwnerSplit owner n A.remaining,
      Nonempty (SaturatedPacking
        (capacityBins W Q S C kind all (A.reservedEdges W Q S C F owner kind) bad)
        R.current (fun i => (F.size i : ℝ)) (capacity W Q S C kind)
        (freshBranchBound α W.clusterSize)) := by
  obtain ⟨R⟩ := exists_ownerSplit owner n A.remaining
    (A.remaining_order W Q S C F owner kind) A.remaining_after
  have hfuture0 : 0 ≤ mass (fun i => (F.size i : ℝ)) R.future := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact Nat.cast_nonneg _
  have hbudget' : mass (fun i => (F.size i : ℝ)) R.current +
      mass (fun i => (F.size i : ℝ)) (A.reservedItems W Q S C F owner kind) ≤
      (∑ e ∈ all, capacity W Q S C kind e) -
        (freshBranchBound α W.clusterSize : ℝ) * all.card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount := by
    have hs := R.mass_split (fun i => (F.size i : ℝ))
    have ht := A.reserved_mass_split W Q S C F owner kind
    linarith only [hbudget, hfuture0, hs, ht]
  refine ⟨R, ?_⟩
  exact exists_residualPacking_absolute all (A.reservedEdges W Q S C F owner kind) bad R.current
    (fun i => (F.size i : ℝ)) (capacity W Q S C kind) (freshBranchBound α W.clusterSize)
    (rootTypicality α) W.clusterSize (mass (fun i => (F.size i : ℝ)) (A.reservedItems W Q S C F owner kind))
    globalCount (A.reserved_edges_subset W Q S C F owner kind) hbad hcount
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (fun e he => capacity_le_twice_clusterSize W Q hα S C hC kind hkind e
      (hedge e (Finset.mem_sdiff.mp he).1))
    (A.ledger_of_current W Q S C F owner kind n hcurrent)
    (fun i _ => ⟨by exact_mod_cast Nat.zero_lt_of_lt (F.root i).isLt,
      by exact_mod_cast hsmall i⟩) hbudget'

end Erdos547b.ZhaoSourceCapacityFamilyPacking

#print axioms Erdos547b.ZhaoSourceCapacityFamilyPacking.exists_currentOwnerPacking
