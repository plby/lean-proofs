/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFamilyAllocationAdvance
import ErdosProblems.Erdos547b.SourceAbsoluteBadBudget

/-!
# A full owner successor from the source family's scalar budget

The current owner's root satisfies the old active-pair constraints and
all but an absolutely bounded set of unused edges. The static family
budget constructs the finite packing, then the actual graph successor.
No later root image or graph realization is assumed.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceFamilyBudgetAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceFamilyAllocationAdvance Erdos547b.ZhaoSourceAbsoluteBadBudget
open Erdos547b.ZhaoSourceFamilyOwnerAdvance Erdos547b.ZhaoSourceOwnerListSplit
open Erdos547b.ZhaoSourceReservationFamilyState Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable {all : Finset (MatchingEdge Q.claim67.M)} {family : List (Fin b)}
variable (rootImage : Fin r → Fin hostN) (n : Fin r)
variable (A : FamilyState W Q S C F owner all family rootImage n.val)

/-- Full actual family advance under the absolute bad-edge budget.
This includes empty current-owner fibers and terminal reservations. -/
theorem exists_familyAdvance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hC : C = Q.A ∨ C = Q.B)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : all ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (globalCount : ℕ)
    (hbudget : mass (fun i => (F.size i : ℝ)) family ≤
      (∑ e ∈ all, partOneCapacity W Q S C e) -
        (freshBranchBound α W.clusterSize : ℝ) * all.card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
    (z : Fin hostN)
    (heligible : ∀ x, A.active = some x → (∃ i ∈ x.1.items, owner i = n) →
      EligibleRoot W Q S C x.1.edge z)
    (bad : Finset (MatchingEdge Q.claim67.M))
    (hbad : bad ⊆ all \ A.reservedEdges W Q S C F owner)
    (hcount : (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * globalCount)
    (hgood : ∀ e ∈ (all \ A.reservedEdges W Q S C F owner) \ bad,
      EligibleRoot W Q S C e z) :
    ∃ D : FamilyState W Q S C F owner all family
        (Function.update rootImage n z) (n.val + 1),
      ∀ i hi, (D.currentPlacement W Q S C F owner).forestCopy.componentCopy i
          (processedFamily_mono owner (Nat.le_succ n.val) family hi) =
        (A.currentPlacement W Q S C F owner).forestCopy.componentCopy i hi := by
  by_cases hcurrent : ∃ i ∈ A.remaining, owner i = n
  · obtain ⟨R⟩ := exists_ownerSplit owner n A.remaining
      (A.remaining_order W Q S C F owner) A.remaining_after
    have hfuture0 : 0 ≤ mass (fun i => (F.size i : ℝ)) R.future := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      exact Nat.cast_nonneg _
    have hbudget' : mass (fun i => (F.size i : ℝ)) R.current +
        mass (fun i => (F.size i : ℝ)) (A.reservedItems W Q S C F owner) ≤
        (∑ e ∈ all, partOneCapacity W Q S C e) -
          (freshBranchBound α W.clusterSize : ℝ) * all.card -
          4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount := by
      have hs := R.mass_split (fun i => (F.size i : ℝ))
      have ht := A.reserved_mass_split W Q S C F owner
      linarith only [hbudget, hfuture0, hs, ht]
    obtain ⟨P⟩ := exists_residualPacking_absolute all (A.reservedEdges W Q S C F owner) bad
      R.current (fun i => (F.size i : ℝ)) (partOneCapacity W Q S C)
      (freshBranchBound α W.clusterSize) (rootTypicality α) W.clusterSize
      (mass (fun i => (F.size i : ℝ)) (A.reservedItems W Q S C F owner)) globalCount
      (A.reserved_edges_subset W Q S C F owner) hbad hcount (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (fun e _ => partOneCapacity_le_twice_clusterSize W Q hα S C hC e)
      (A.ledger_of_current W Q S C F owner n hcurrent)
      (by
        intro i _
        constructor
        · exact_mod_cast Nat.zero_lt_of_lt (F.root i).isLt
        · exact_mod_cast hsmall i) hbudget'
    apply exists_familyAdvance_withPacking W Q S C F owner rootImage n A hα hα1 hhost horder hC
      z hcurrent heligible R (goodBins W Q S C all (A.reservedEdges W Q S C F owner) bad) P hsmall
    · intro e he
      have hg := Finset.mem_filter.mp (Finset.mem_toList.mp (List.mem_toFinset.mp he))
      exact (Finset.mem_sdiff.mp hg.1).1
    · intro e he
      have hg := Finset.mem_filter.mp (Finset.mem_toList.mp he)
      exact haway (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hg.1).1).1
    · intro e he
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
    · intro e he
      exact hgood e (Finset.mem_filter.mp (Finset.mem_toList.mp he)).1
  · obtain ⟨D, _, _, _, _, _, hcopies⟩ := exists_familyAdvance_noAllocation W Q S C F owner
      rootImage n A z (fun i hi he => hcurrent ⟨i, hi, he⟩) heligible
    exact ⟨D, hcopies⟩

end Erdos547b.ZhaoSourceFamilyBudgetAdvance

#print axioms Erdos547b.ZhaoSourceFamilyBudgetAdvance.exists_familyAdvance
