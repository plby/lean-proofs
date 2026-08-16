import ErdosProblems.Erdos920.PoorChildren
import ErdosProblems.Erdos920.PopularChildren

/-!
# Uniform marked-degree bound for the projective container

This file combines the poor-child mixing estimate and the popular-child
span estimate.  It is separate from `MarkedChildren` only to keep the two
specialized counting modules downstream of the definition of the marking.
-/

open scoped LinearAlgebra.Projectivization

namespace Erdos920.MarkedChildrenBound

noncomputable section

open Erdos920.Container
open Erdos920.MarkedChildren
open Erdos920.PoorChildren
open Erdos920.PopularChildren
open Erdos920.Projective
open Erdos920.ProjectiveContainer

attribute [local instance] Classical.propDecidable Classical.decEq

variable {q t : ℕ} [Fact q.Prime]

abbrev PT (q t : ℕ) [Fact q.Prime] := MarkedChildren.PointT q t

local instance pointFintype : Fintype (PT q t) := Fintype.ofFinite _
local instance orthogonalDecidable :
    DecidableRel (@Orthogonal (ZMod q) _ (t + 1)) := Classical.decRel _

/-- All poor children, with the pivot selected from the rank of the second
coordinate. -/
def poorChildren (q t : ℕ) [Fact q.Prime]
    (sigma : List (PT q t × PT q t)) :
    Finset (PT q t × PT q t) :=
  (projectiveChildren q t sigma).filter fun p =>
    PoorQ (Finset.univ : Finset (PT q t)) (projectiveRankClosure q t)
      Orthogonal q sigma
        (chosenPivot (Finset.univ : Finset (PT q t))
          (projectiveRankClosure q t) Orthogonal sigma p) p.1

/-- Sum the fixed-rank poor estimates over the `t+1` possible child ranks. -/
theorem poorChildren_card_le (ht : 2 ≤ t)
    (sigma : List (PT q t × PT q t)) :
    (poorChildren q t sigma).card ≤ 2048 * (t + 1) * q ^ t := by
  let S := poorChildren q t sigma
  let Sj := fun j : ℕ => PoorChildren.poorChildrenAtRank q t sigma j
  have hsub : S ⊆ (Finset.range (t + 1)).biUnion Sj := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hj : PopularChildren.childRank q t sigma p ≤ t :=
      PopularChildren.childRank_le_t_of_mem_children q t sigma p hp'.1
    apply Finset.mem_biUnion.mpr
    refine ⟨PopularChildren.childRank q t sigma p,
      Finset.mem_range.mpr (by omega), ?_⟩
    apply (PoorChildren.mem_poorChildrenAtRank_iff q t sigma
      (PopularChildren.childRank q t sigma p) p).mpr
    refine ⟨?_, rfl, ?_⟩
    · simpa [projectiveChildren_eq_extensionChildren] using hp'.1
    · simpa [PopularChildren.childRank, PopularChildren.pivotForRank,
        chosenPivot] using hp'.2
  calc
    (poorChildren q t sigma).card = S.card := rfl
    _ ≤ ((Finset.range (t + 1)).biUnion Sj).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (t + 1), (Sj j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (t + 1), 2048 * q ^ t := by
      exact Finset.sum_le_sum fun j _ =>
        PoorChildren.card_poorChildrenAtRank_le q t ht sigma j
    _ = 2048 * (t + 1) * q ^ t := by simp; ring

/-- The children marked by either cleared exceptional predicate. -/
def markedChildren (q t : ℕ) [Fact q.Prime]
    (sigma : List (PT q t × PT q t)) :
    Finset (PT q t × PT q t) :=
  (projectiveChildren q t sigma).filter fun p =>
    projectiveMarked q t sigma p = true

/-- The concrete marked degree is at most `2112*(t+1)*q^t`. -/
theorem markedChildren_card_le (ht : 2 ≤ t)
    (sigma : List (PT q t × PT q t)) :
    (markedChildren q t sigma).card ≤ 2112 * (t + 1) * q ^ t := by
  have hsub : markedChildren q t sigma ⊆
      poorChildren q t sigma ∪ PopularChildren.popularChildren q t sigma := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hor :
        PoorQ (Finset.univ : Finset (PT q t)) (projectiveRankClosure q t)
            Orthogonal q sigma
              (chosenPivot (Finset.univ : Finset (PT q t))
                (projectiveRankClosure q t) Orthogonal sigma p) p.1 ∨
        PopularQ (Finset.univ : Finset (PT q t)) (projectiveRankClosure q t)
            Orthogonal q sigma
              (chosenPivot (Finset.univ : Finset (PT q t))
                (projectiveRankClosure q t) Orthogonal sigma p) p.2 := by
      simpa [projectiveMarked, marked] using hp'.2
    rcases hor with hpoor | hpopular
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp'.1, hpoor⟩)
    · apply Finset.mem_union_right
      rw [PopularChildren.popularChildren_eq_markedPopular]
      exact Finset.mem_filter.mpr ⟨hp'.1, hpopular⟩
  calc
    (markedChildren q t sigma).card ≤
        (poorChildren q t sigma ∪ PopularChildren.popularChildren q t sigma).card :=
      Finset.card_le_card hsub
    _ ≤ (poorChildren q t sigma).card +
        (PopularChildren.popularChildren q t sigma).card :=
      Finset.card_union_le _ _
    _ ≤ 2048 * (t + 1) * q ^ t + 64 * (t + 1) * q ^ t :=
      Nat.add_le_add (poorChildren_card_le ht sigma)
        (PopularChildren.popularChildren_card_le q t sigma)
    _ = 2112 * (t + 1) * q ^ t := by ring

end

end Erdos920.MarkedChildrenBound
