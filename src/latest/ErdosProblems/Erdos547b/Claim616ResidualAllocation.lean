/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim617BranchCount
import ErdosProblems.Erdos547b.SpecialSegmentation

/-!
# Source residuals for Zhao Claims 6.16 and 6.17

This file contains only source combinatorics.  Starting with the canonical
major parity half and a branch-closed selected `F₀`, it defines the literal
residual `F₁` and the minor half `F_b`, and records the exact edge-demand
partition identities used by the three matching allocations.

The strengthened mark set contains every Zhao component root and every
canonical root-deleted branch root.  Consequently the downstream whole-tree
hierarchy can never mix two canonical branch classes in one segment.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim616ResidualAllocation

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59SpecialSegmentation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

abbrev BranchIndex (P : ZhaoForestPartition T globalRoot small) :=
  Fin (Fintype.card (ChildKey P.orderedForest))

/-- Canonical root-deleted branches owned by the minor component-parity
class. -/
def minorBranches (P : ZhaoForestPartition T globalRoot small) :
    Finset (BranchIndex P) :=
  Finset.univ.filter fun j =>
    T.dist globalRoot (P.roots ((branchForest P).owner j)) % 2 =
      (minorParity P).val

@[simp] theorem mem_minorBranches
    (P : ZhaoForestPartition T globalRoot small) (j : BranchIndex P) :
    j ∈ minorBranches P ↔
      T.dist globalRoot (P.roots ((branchForest P).owner j)) % 2 =
        (minorParity P).val := by
  simp [minorBranches]

/-- Major and minor branch families are disjoint because their owner-root
parities are opposite. -/
theorem halfBranches_disjoint_minorBranches
    (P : ZhaoForestPartition T globalRoot small) :
    Disjoint (halfBranches P) (minorBranches P) := by
  rw [Finset.disjoint_left]
  intro j hjMajor hjMinor
  have hmajor := (Finset.mem_filter.mp hjMajor).2
  have hminor := (mem_minorBranches P j).mp hjMinor
  by_cases h : (parityPart P 1).card ≤ (parityPart P 0).card
  · simp [majorParity, minorParity, h] at hmajor hminor
    omega
  · simp [majorParity, minorParity, h] at hmajor hminor
    omega

/-- Every canonical root-deleted branch belongs to exactly one parity half. -/
theorem halfBranches_union_minorBranches
    (P : ZhaoForestPartition T globalRoot small) :
    halfBranches P ∪ minorBranches P = Finset.univ := by
  ext j
  simp only [Finset.mem_union, Finset.mem_univ, iff_true,
    halfBranches, Finset.mem_filter, true_and, mem_minorBranches]
  have hmod :
      T.dist globalRoot (P.roots ((branchForest P).owner j)) % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  by_cases h : (parityPart P 1).card ≤ (parityPart P 0).card
  · simp [majorParity, minorParity, h]
    omega
  · simp [majorParity, minorParity, h]
    omega

/-- Branch indices left in the major half after selecting `F₀`.  Singleton
branches are deliberately retained. -/
def majorResidualBranches
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Finset (BranchIndex P) :=
  halfBranches P \ S.selected

@[simp] theorem mem_majorResidualBranches
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (j : BranchIndex P) :
    j ∈ majorResidualBranches P S ↔
      j ∈ halfBranches P ∧ j ∉ S.selected := by
  simp [majorResidualBranches]

theorem selected_disjoint_majorResidual
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    Disjoint S.selected (majorResidualBranches P S) := by
  exact Finset.disjoint_sdiff

theorem selected_union_majorResidual
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    S.selected ∪ majorResidualBranches P S = halfBranches P := by
  rw [majorResidualBranches, Finset.union_sdiff_of_subset S.selected_available]

/-- The selected, residual-major, and minor branch families partition every
canonical branch index. -/
theorem selected_union_residual_union_minor
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    S.selected ∪ majorResidualBranches P S ∪ minorBranches P = Finset.univ := by
  rw [selected_union_majorResidual, halfBranches_union_minorBranches]

/-- Literal source forests `F₀`, `F₁`, and `F_b`. -/
abbrev F0
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :=
  S.toSelectedF0.forest

abbrev F1
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :=
  OrderedBranchForest.restrict (branchForest P) (majorResidualBranches P S)

abbrev Fb (P : ZhaoForestPartition T globalRoot small) :=
  OrderedBranchForest.restrict (branchForest P) (minorBranches P)

/-- Generic exact mass split for a selected subfamily. -/
theorem edgeDemand_restrict_add_residual
    {r b : ℕ} (F : OrderedBranchForest r b)
    (available selected : Finset (Fin b)) (hsub : selected ⊆ available) :
    OrderedBranchForest.edgeDemand (OrderedBranchForest.restrict F selected) +
        OrderedBranchForest.edgeDemand
          (OrderedBranchForest.restrict F (available \ selected)) =
      OrderedBranchForest.edgeDemand (OrderedBranchForest.restrict F available) := by
  rw [OrderedBranchForest.edgeDemand_restrict,
    OrderedBranchForest.edgeDemand_restrict,
    OrderedBranchForest.edgeDemand_restrict]
  have hsplit := Finset.sum_sdiff hsub (f := F.branches.size)
  omega

/-- `||F₀|| + ||F₁||` is exactly the mass of the canonical major half. -/
theorem edgeDemand_F0_add_F1
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    OrderedBranchForest.edgeDemand (F0 P S) +
        OrderedBranchForest.edgeDemand (F1 P S) =
      OrderedBranchForest.edgeDemand
        (OrderedBranchForest.restrict (branchForest P) (halfBranches P)) := by
  exact edgeDemand_restrict_add_residual (branchForest P)
    (halfBranches P) S.selected S.selected_available

/-- The two parity halves account for every root-deleted branch. -/
theorem edgeDemand_major_add_minor
    (P : ZhaoForestPartition T globalRoot small) :
    OrderedBranchForest.edgeDemand
        (OrderedBranchForest.restrict (branchForest P) (halfBranches P)) +
      OrderedBranchForest.edgeDemand (Fb P) =
    OrderedBranchForest.edgeDemand (branchForest P) := by
  rw [OrderedBranchForest.edgeDemand_restrict,
    OrderedBranchForest.edgeDemand_restrict,
    OrderedBranchForest.edgeDemand]
  rw [← Finset.sum_union (halfBranches_disjoint_minorBranches P),
    halfBranches_union_minorBranches]

/-- Exact three-way mass partition used by the matching allocator. -/
theorem edgeDemand_F0_add_F1_add_Fb
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack) :
    OrderedBranchForest.edgeDemand (F0 P S) +
        OrderedBranchForest.edgeDemand (F1 P S) +
      OrderedBranchForest.edgeDemand (Fb P) =
    OrderedBranchForest.edgeDemand (branchForest P) := by
  rw [← edgeDemand_major_add_minor P, ← edgeDemand_F0_add_F1 P S]

/-- A uniform source branch bound is inherited by all three restrictions. -/
theorem restricted_branch_size_le
    {r b : ℕ} (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (bound : ℕ) (hsmall : ∀ j, F.branches.size j ≤ bound)
    (i : Fin s.card) :
    (OrderedBranchForest.restrict F s).branches.size i ≤ bound := by
  simpa using hsmall (OrderedBranchForest.selectedEquiv s i)

theorem F0_branch_size_le
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (bound : ℕ) (hsmall : ∀ j, (branchForest P).branches.size j ≤ bound)
    (i : Fin S.selected.card) : (F0 P S).branches.size i ≤ bound :=
  restricted_branch_size_le (branchForest P) S.selected bound hsmall i

theorem F1_branch_size_le
    (P : ZhaoForestPartition T globalRoot small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (bound : ℕ) (hsmall : ∀ j, (branchForest P).branches.size j ≤ bound)
    (i : Fin (majorResidualBranches P S).card) :
    (F1 P S).branches.size i ≤ bound :=
  restricted_branch_size_le (branchForest P) (majorResidualBranches P S)
    bound hsmall i

theorem Fb_branch_size_le
    (P : ZhaoForestPartition T globalRoot small)
    (bound : ℕ) (hsmall : ∀ j, (branchForest P).branches.size j ≤ bound)
    (i : Fin (minorBranches P).card) :
    (Fb P).branches.size i ≤ bound :=
  restricted_branch_size_le (branchForest P) (minorBranches P) bound hsmall i

/-- Every hierarchy fiber cut from a bounded branch is itself bounded.  This
is the exact `t ≤ εN` input for the segmented source. -/
theorem segmented_size_le_of_branch_size_le
    {r b : ℕ} (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F)) (bound : ℕ)
    (hsmall : ∀ j, F.branches.size j ≤ bound)
    (i : Fin #(marks F special)) :
    (segmentedOrderedForest F special).size i ≤ bound := by
  let q := (markEnum F special i).1
  calc
    (segmentedOrderedForest F special).size i =
        Nat.card {a // a ∈ fiberSet F special q} := rfl
    _ ≤ F.branches.size q.1 := by
      let e : {a // a ∈ fiberSet F special q} ↪ Fin (F.branches.size q.1) :=
        Function.Embedding.subtype _
      simpa only [Nat.card_fin] using
        Nat.card_le_card_of_injective e e.injective
    _ ≤ bound := hsmall q.1

/-- Optional-special slack is inherited after forgetting the impossible
original-root coordinates. -/
theorem branchSpecial_card_le_bound
    {r b : ℕ} (F : OrderedBranchForest r b) (special : Finset F.Vertex)
    (bound : ℕ) (hcard : #special ≤ bound) :
    #(branchSpecial F special) ≤ bound :=
  (card_branchSpecial_le F special).trans hcard

/-- Literal marks for aggregate allocation: all Zhao component roots, all
canonical branch roots, and the optional parent/special set. -/
def allocationMarkedVertices
    (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V) : Finset V :=
  partitionRoots P ∪
    ((Finset.univ.image (actualBranchRoot P)) ∪ optional)

theorem partitionRoots_subset_allocationMarkedVertices
    (P : ZhaoForestPartition T globalRoot small) (optional : Finset V) :
    partitionRoots P ⊆ allocationMarkedVertices P optional := by
  intro x hx
  exact Finset.mem_union_left _ hx

theorem actualBranchRoot_mem_allocationMarkedVertices
    (P : ZhaoForestPartition T globalRoot small) (optional : Finset V)
    (j : BranchIndex P) :
    actualBranchRoot P j ∈ allocationMarkedVertices P optional := by
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem optional_subset_allocationMarkedVertices
    (P : ZhaoForestPartition T globalRoot small) (optional : Finset V) :
    optional ⊆ allocationMarkedVertices P optional := by
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_union_right _ hx)

/-- The cost of strengthening the hierarchy marks is explicit. -/
theorem card_allocationMarkedVertices_le
    (P : ZhaoForestPartition T globalRoot small) (optional : Finset V) :
    #(allocationMarkedVertices P optional) ≤
      P.numParts + Fintype.card (BranchIndex P) + #optional := by
  calc
    #(allocationMarkedVertices P optional) ≤
        #(partitionRoots P) +
          #(Finset.univ.image (actualBranchRoot P)) + #optional := by
      have houter := Finset.card_union_le (partitionRoots P)
        ((Finset.univ.image (actualBranchRoot P)) ∪ optional)
      have hinner := Finset.card_union_le
        (Finset.univ.image (actualBranchRoot P)) optional
      dsimp only [allocationMarkedVertices]
      omega
    _ ≤ P.numParts + Fintype.card (BranchIndex P) + #optional := by
      rw [partitionRoots_card]
      gcongr
      exact Finset.card_image_le

end Erdos547b.ZhaoClaim616ResidualAllocation

#print axioms Erdos547b.ZhaoClaim616ResidualAllocation.edgeDemand_F0_add_F1_add_Fb
#print axioms Erdos547b.ZhaoClaim616ResidualAllocation.segmented_size_le_of_branch_size_le
#print axioms Erdos547b.ZhaoClaim616ResidualAllocation.card_allocationMarkedVertices_le
