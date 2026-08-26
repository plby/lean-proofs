/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59Part2Full

/-!
# The source-forest selection in Zhao Claim 6.16

This module isolates the genuinely combinatorial part of Claim 6.16.  A
root-subforest is obtained by selecting whole root-deleted branches.  The
selected family is reindexed as an actual `OrderedBranchForest`; its edge
count, Level1 count, and Level>=2 count are then computed exactly.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim616SourceBridge

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Part2Full

universe u

namespace OrderedBranchForest

variable {r b : ℕ}

/-- Canonical enumeration of a selected family of root-deleted branches. -/
noncomputable def selectedEquiv (s : Finset (Fin b)) :
    Fin s.card ≃ {j // j ∈ s} :=
  (Finset.equivFin s).symm

/-- The root-subforest obtained by retaining precisely the branches in `s`.
All original roots are retained; roots with no selected branch are isolated.
This convention is harmless for edge counts and is exactly what is needed
for later root-partition gluing. -/
noncomputable def restrict (F : OrderedBranchForest r b)
    (s : Finset (Fin b)) : OrderedBranchForest r s.card where
  branches :=
    { size := fun j => F.branches.size (selectedEquiv s j)
      tree := fun j => F.branches.tree (selectedEquiv s j)
      isTree := fun j => F.branches.isTree (selectedEquiv s j)
      root := fun j => F.branches.root (selectedEquiv s j) }
  owner := fun j => F.owner (selectedEquiv s j)

@[simp] theorem restrict_size (F : OrderedBranchForest r b)
    (s : Finset (Fin b)) (j : Fin s.card) :
    (restrict F s).branches.size j =
      F.branches.size (selectedEquiv s j) := rfl

@[simp] theorem restrict_owner (F : OrderedBranchForest r b)
    (s : Finset (Fin b)) (j : Fin s.card) :
    (restrict F s).owner j = F.owner (selectedEquiv s j) := rfl

/-- The sum over the canonical enumeration is the sum over the selected
finite family. -/
theorem sum_selectedEquiv (s : Finset (Fin b)) (w : Fin b → ℕ) :
    ∑ j : Fin s.card, w (selectedEquiv s j) = ∑ j ∈ s, w j := by
  classical
  let e := selectedEquiv s
  calc
    ∑ j : Fin s.card, w (e j) = ∑ z : {j // j ∈ s}, w z := by
      exact Fintype.sum_equiv e (fun j : Fin s.card => w (e j))
        (fun z : {j // j ∈ s} => w z) (fun j => rfl)
    _ = ∑ j ∈ s, w j := Finset.sum_attach s w

@[simp] theorem levelOneDemand_restrict (F : OrderedBranchForest r b)
    (s : Finset (Fin b)) :
    levelOneDemand (restrict F s) = s.card := by
  simp [levelOneDemand]

@[simp] theorem deepDemand_restrict (F : OrderedBranchForest r b)
    (s : Finset (Fin b)) :
    deepDemand (restrict F s) =
      ∑ j ∈ s, (F.branches.size j - 1) := by
  classical
  simp only [deepDemand, restrict_size]
  exact sum_selectedEquiv s (fun j => F.branches.size j - 1)

/-- `||F||` for a branch forest: every selected branch contributes its
attachment edge and all internal tree edges, hence exactly its order. -/
def edgeDemand (F : OrderedBranchForest r b) : ℕ :=
  ∑ j, F.branches.size j

@[simp] theorem edgeDemand_restrict (F : OrderedBranchForest r b)
    (s : Finset (Fin b)) :
    edgeDemand (restrict F s) = ∑ j ∈ s, F.branches.size j := by
  classical
  simp only [edgeDemand, restrict_size]
  exact sum_selectedEquiv s F.branches.size

/-- Every selected branch consists of its Level1 root plus its deep tail. -/
theorem levelOne_add_deep_eq_edgeDemand_restrict
    (F : OrderedBranchForest r b) (s : Finset (Fin b))
    (hpos : ∀ j ∈ s, 0 < F.branches.size j) :
    levelOneDemand (restrict F s) + deepDemand (restrict F s) =
      edgeDemand (restrict F s) := by
  rw [levelOneDemand_restrict, deepDemand_restrict, edgeDemand_restrict]
  calc
    s.card + ∑ j ∈ s, (F.branches.size j - 1) =
        ∑ j ∈ s, (1 + (F.branches.size j - 1)) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = ∑ j ∈ s, F.branches.size j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjpos := hpos j hj
      omega

/-- Zhao's `F₃`: root-deleted branches having at least three vertices. -/
def largeBranches (F : OrderedBranchForest r b) : Finset (Fin b) :=
  Finset.univ.filter fun j => 3 ≤ F.branches.size j

@[simp] theorem mem_largeBranches (F : OrderedBranchForest r b) (j : Fin b) :
    j ∈ largeBranches F ↔ 3 ≤ F.branches.size j := by
  simp [largeBranches]

def largeBranchMass (F : OrderedBranchForest r b) : ℕ :=
  ∑ j ∈ largeBranches F, F.branches.size j

end OrderedBranchForest

/-! ## Exact finite prefix selection -/

/-- First-threshold selection for a finite family of positive integral
weights.  The overshoot is strictly smaller than the uniform branch bound.
This is the precise finite sentence used to obtain display (6.23). -/
theorem exists_subset_sum_between_target_and_target_add
    {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℕ) (target slack : ℕ)
    (hslack : 0 < slack)
    (hsmall : ∀ a ∈ s, w a ≤ slack)
    (htotal : target ≤ ∑ a ∈ s, w a) :
    ∃ t ⊆ s,
      target ≤ ∑ a ∈ t, w a ∧
      ∑ a ∈ t, w a < target + slack := by
  classical
  let xs := s.toList
  let weights := xs.map w
  let P : ℕ → Prop := fun i => target ≤ (weights.take i).sum
  have htotal' : target ≤ weights.sum := by
    simpa [weights, xs] using htotal
  have hex : ∃ i, P i := by
    exact ⟨weights.length, by simpa [P] using htotal'⟩
  let i := Nat.find hex
  have hi : P i := Nat.find_spec hex
  have hilen : i ≤ weights.length :=
    Nat.find_min' hex (m := weights.length) (by simpa [P] using htotal')
  let chosenList := xs.take i
  let t := chosenList.toFinset
  have htSub : t ⊆ s := by
    intro a ha
    have haList : a ∈ chosenList := List.mem_toFinset.mp ha
    exact Finset.mem_toList.mp (List.mem_of_mem_take haList)
  have hnodup : chosenList.Nodup := (Finset.nodup_toList s).take
  have hsum : ∑ a ∈ t, w a = (weights.take i).sum := by
    have htake : weights.take i = chosenList.map w := by
      simp [weights, chosenList, xs]
    rw [htake]
    simpa [t] using (List.sum_toFinset w hnodup)
  refine ⟨t, htSub, ?_, ?_⟩
  · rw [hsum]
    exact hi
  · rw [hsum]
    by_cases hi0 : i = 0
    · have htarget0 : target = 0 := by
        have : target ≤ 0 := by simpa [P, hi0] using hi
        omega
      simp [hi0, htarget0, hslack]
    · let j := i - 1
      have hji : j < i := by simp [j]; omega
      have hjlt : (weights.take j).sum < target := by
        have hnot := Nat.find_min hex hji
        simp only [P] at hnot
        omega
      have hjlen : j < weights.length := by omega
      have hisucc : j + 1 = i := by simp [j]; omega
      have hwmem : weights[j] ∈ weights := List.getElem_mem hjlen
      obtain ⟨a, ha, haw⟩ := List.mem_map.mp hwmem
      have haS : a ∈ s := by
        exact Finset.mem_toList.mp (by simpa [weights, xs] using ha)
      have hwle : weights[j] ≤ slack := by
        simpa [haw] using hsmall a haS
      rw [← hisucc, List.sum_take_succ weights j hjlen]
      omega

/-! ## The selected root-subforest and its three budgets -/

/-- Concrete output of the source selection in Claim 6.16.  It stores only
the selected branch indices and exact numerical consequences; the actual
root-subforest is definitionally `F.restrict selected`. -/
structure SelectedF0 {r b : ℕ} (F : OrderedBranchForest r b)
    (target slack : ℕ) where
  selected : Finset (Fin b)
  selected_large : selected ⊆ OrderedBranchForest.largeBranches F
  lower : target ≤ OrderedBranchForest.edgeDemand
    (OrderedBranchForest.restrict F selected)
  upper : OrderedBranchForest.edgeDemand
    (OrderedBranchForest.restrict F selected) < target + slack

/-- A selected root-subforest constrained to a branch-closed source half.
The extra field is purely structural; the numerical certificate remains the
literal `SelectedF0` above. -/
structure SelectedF0Within {r b : ℕ} (F : OrderedBranchForest r b)
    (available : Finset (Fin b)) (target slack : ℕ) extends
    SelectedF0 F target slack where
  selected_available : selected ⊆ available

/-- Claim-6.16 selection inside an arbitrary branch-closed available family.
This is the form used for the canonical parity half: no branch from the
other half can enter the selected root-subforest. -/
theorem exists_selectedF0Within
    {r b : ℕ} (F : OrderedBranchForest r b)
    (available : Finset (Fin b))
    (target slack : ℕ) (hslack : 0 < slack)
    (hsmall : ∀ j, F.branches.size j ≤ slack)
    (hmass : target ≤
      ∑ j ∈ available.filter (fun j ↦ 3 ≤ F.branches.size j),
        F.branches.size j) :
    Nonempty (SelectedF0Within F available target slack) := by
  classical
  let largeAvailable :=
    available.filter (fun j ↦ 3 ≤ F.branches.size j)
  obtain ⟨s, hsLarge, hsLower, hsUpper⟩ :=
    exists_subset_sum_between_target_and_target_add largeAvailable
      F.branches.size target slack hslack
      (fun j _ ↦ hsmall j) (by simpa [largeAvailable] using hmass)
  refine ⟨
    { selected := s
      selected_large := ?_
      lower := by simpa using hsLower
      upper := by simpa using hsUpper
      selected_available := ?_ }⟩
  · intro j hj
    have hj' := hsLarge hj
    have hsize := (Finset.mem_filter.mp hj').2
    exact (OrderedBranchForest.mem_largeBranches F j).mpr hsize
  · intro j hj
    exact (Finset.mem_filter.mp (hsLarge hj)).1

theorem exists_selectedF0
    {r b : ℕ} (F : OrderedBranchForest r b)
    (target slack : ℕ) (hslack : 0 < slack)
    (hsmall : ∀ j, F.branches.size j ≤ slack)
    (hmass : target ≤ OrderedBranchForest.largeBranchMass F) :
    Nonempty (SelectedF0 F target slack) := by
  classical
  obtain ⟨s, hsLarge, hsLower, hsUpper⟩ :=
    exists_subset_sum_between_target_and_target_add
      (OrderedBranchForest.largeBranches F)
      F.branches.size target slack hslack
      (fun j _ => hsmall j) (by simpa [OrderedBranchForest.largeBranchMass] using hmass)
  refine ⟨
    { selected := s
      selected_large := hsLarge
      lower := ?_
      upper := ?_ }⟩
  · simpa using hsLower
  · simpa using hsUpper

namespace SelectedF0

variable {r b target slack : ℕ} {F : OrderedBranchForest r b}

abbrev forest (S : SelectedF0 F target slack) :
    OrderedBranchForest r S.selected.card :=
  OrderedBranchForest.restrict F S.selected

/-- Every chosen root-deleted tree has at least three vertices. -/
theorem branch_size_ge_three (S : SelectedF0 F target slack)
    (j : Fin S.selected.card) :
    3 ≤ S.forest.branches.size j := by
  let z := OrderedBranchForest.selectedEquiv S.selected j
  have hzLarge : (z : Fin b) ∈ OrderedBranchForest.largeBranches F :=
    S.selected_large z.property
  simpa [forest, z] using (OrderedBranchForest.mem_largeBranches F z).mp hzLarge

/-- In the selected `F₀`, three vertices pay for every Level1 vertex. -/
theorem three_mul_levelOne_le_edgeDemand
    (S : SelectedF0 F target slack) :
    3 * levelOneDemand S.forest ≤
      OrderedBranchForest.edgeDemand S.forest := by
  classical
  rw [OrderedBranchForest.edgeDemand]
  change 3 * S.selected.card ≤
    ∑ j : Fin S.selected.card, S.forest.branches.size j
  calc
    3 * S.selected.card =
        ∑ _j : Fin S.selected.card, 3 := by simp [Nat.mul_comm]
    _ ≤ ∑ j : Fin S.selected.card, S.forest.branches.size j := by
      exact sum_le_sum fun j _ => S.branch_size_ge_three j

/-- The Level1 budget used immediately before invoking Lemma 5.9(2). -/
theorem levelOne_le_of_three_mul_upper
    (S : SelectedF0 F target slack) (capacity : ℕ)
    (hcap : target + slack ≤ 3 * capacity + 1) :
    levelOneDemand S.forest ≤ capacity := by
  have hthree := S.three_mul_levelOne_le_edgeDemand
  have hu : OrderedBranchForest.edgeDemand S.forest < target + slack := by
    simpa [forest] using S.upper
  omega

/-- The deep demand is bounded by the edge demand, since every selected
branch is nonempty. -/
theorem deepDemand_le_edgeDemand (S : SelectedF0 F target slack) :
    deepDemand S.forest ≤ OrderedBranchForest.edgeDemand S.forest := by
  classical
  simp only [deepDemand, OrderedBranchForest.edgeDemand]
  apply sum_le_sum
  intro j _
  omega

/-- The Level>=2 budget used for the available matching `M₂`. -/
theorem deepDemand_le_of_target_add
    (S : SelectedF0 F target slack) (matchingCapacity : ℕ)
    (hcap : target + slack ≤ matchingCapacity + 1) :
    deepDemand S.forest ≤ matchingCapacity := by
  have hd := S.deepDemand_le_edgeDemand
  have hu : OrderedBranchForest.edgeDemand S.forest < target + slack := by
    simpa [forest] using S.upper
  omega

/-- Each selected branch tail obeys the same small-tree bound as the
original branch. -/
theorem tail_small (S : SelectedF0 F target slack)
    (hsmall : ∀ j, F.branches.size j ≤ slack)
    (j : Fin S.selected.card) :
    S.forest.branches.size j - 1 ≤ slack := by
  exact (Nat.sub_le _ 1).trans (by
    simpa [forest] using hsmall
      (OrderedBranchForest.selectedEquiv S.selected j))

end SelectedF0

end Erdos547b.ZhaoClaim616SourceBridge

#print axioms Erdos547b.ZhaoClaim616SourceBridge.exists_subset_sum_between_target_and_target_add
#print axioms Erdos547b.ZhaoClaim616SourceBridge.exists_selectedF0
#print axioms Erdos547b.ZhaoClaim616SourceBridge.exists_selectedF0Within
#print axioms Erdos547b.ZhaoClaim616SourceBridge.SelectedF0.levelOne_le_of_three_mul_upper
#print axioms Erdos547b.ZhaoClaim616SourceBridge.SelectedF0.deepDemand_le_of_target_add
