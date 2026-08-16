import ErdosProblems.Erdos920.DesignAdapter
import ErdosProblems.Erdos920.MarkedChildren

/-!
# Poor children in the projective container

This file is the combinatorial bridge between the projective mixing estimate
in `DesignAdapter` and the marked-child count.  At a fixed rank `j`, a poor
extension `(a,b)` has `a` in the poor set defined by the pivot stratum and
`b` in the exact-rank stratum `Z_j`; incidence of the extension says that
`a` and `b` form an ordered orthogonality edge.  The pivot property gives
`|Z_j| <= |Z_pivot|`, so the second mixing estimate bounds the whole fibre.
-/

open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.PoorChildren

noncomputable section

open Erdos920.Container
open Erdos920.DesignAdapter
open Erdos920.MarkedChildren
open Erdos920.Mixing
open Erdos920.Pivot
open Erdos920.Projective
open Erdos920.ProjectiveContainer

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## A finite edge-pair cover -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Ordered relation pairs with first coordinate in `A` and second coordinate
in `B`.  This is deliberately a `Finset (X x X)`, so subsets of container
children map into it by the identity map. -/
def edgePairs (R : X -> X -> Prop) [DecidableRel R]
    (A B : Finset X) : Finset (X × X) :=
  A.biUnion fun a => (B.filter (R a)).image fun b => (a, b)

@[simp] theorem mem_edgePairs_iff (R : X -> X -> Prop) [DecidableRel R]
    (A B : Finset X) (p : X × X) :
    p ∈ edgePairs R A B <-> p.1 ∈ A ∧ p.2 ∈ B ∧ R p.1 p.2 := by
  classical
  constructor
  · intro hp
    obtain ⟨a, ha, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hp
    have hb' := Finset.mem_filter.mp hb
    cases hab
    exact ⟨ha, hb'.1, hb'.2⟩
  · rintro ⟨ha, hb, hp⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1, ha, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨p.2, Finset.mem_filter.mpr ⟨hb, hp⟩, Prod.ext rfl rfl⟩

/-- The number of explicit relation pairs is bounded by the corresponding
ordered-edge sum.  (`edgePairs` is in fact a disjoint union in its first
coordinate, but the upper bound is the only direction needed below.) -/
theorem card_edgePairs_le_orderedEdges
    (R : X -> X -> Prop) [DecidableRel R] (A B : Finset X) :
    (edgePairs R A B).card ≤ orderedEdges R A B := by
  classical
  calc
    (edgePairs R A B).card ≤
        ∑ a ∈ A, ((B.filter (R a)).image fun b => (a, b)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ a ∈ A, (B.filter (R a)).card := by
      exact Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = orderedEdges R A B := by
      rfl

theorem card_le_orderedEdges_of_subset_edgePairs
    (R : X -> X -> Prop) [DecidableRel R] (A B : Finset X)
    (S : Finset (X × X)) (hS : S ⊆ edgePairs R A B) :
    S.card ≤ orderedEdges R A B :=
  (Finset.card_le_card hS).trans (card_edgePairs_le_orderedEdges R A B)

/-! ## Fixed-rank poor children -/

abbrev PointT (q t : ℕ) [Fact q.Prime] :=
  Point (ZMod q) (t + 1)

local instance pointFintype (q t : ℕ) [Fact q.Prime] :
    Fintype (PointT q t) := Fintype.ofFinite _

local instance orthogonalDecidable (q t : ℕ) [Fact q.Prime] :
    DecidableRel (@Orthogonal (ZMod q) _ (t + 1)) := Classical.decRel _

/-- Extension children of exact second-coordinate rank `j` whose first
coordinate is poor with respect to the canonical pivot below `j`. -/
def poorChildrenAtRank (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) (j : ℕ) :
    Finset (PointT q t × PointT q t) :=
  let points : Finset (PointT q t) := Finset.univ
  let C := projectiveRankClosure q t
  (extensionChildren points Orthogonal sigma).filter fun p =>
    prefixRank C Orthogonal sigma p.2 = j ∧
      PoorQ points C Orthogonal q sigma
        (pivotLevel points C Orthogonal sigma j) p.1

@[simp] theorem mem_poorChildrenAtRank_iff
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) (j : ℕ)
    (p : PointT q t × PointT q t) :
    p ∈ poorChildrenAtRank q t sigma j <->
      p ∈ extensionChildren (Finset.univ : Finset (PointT q t))
        Orthogonal sigma ∧
      prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2 = j ∧
      PoorQ (Finset.univ : Finset (PointT q t))
        (projectiveRankClosure q t) Orthogonal q sigma
        (pivotLevel (Finset.univ : Finset (PointT q t))
          (projectiveRankClosure q t) Orthogonal sigma j) p.1 := by
  rw [poorChildrenAtRank, Finset.mem_filter]

/-- At a fixed rank, poor children are covered by the ordered edges from the
canonical poor set to the exact-rank stratum. -/
theorem poorChildrenAtRank_subset_edgePairs
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) (j : ℕ) :
    let points : Finset (PointT q t) := Finset.univ
    let C := projectiveRankClosure q t
    let l := pivotLevel points C Orthogonal sigma j
    poorChildrenAtRank q t sigma j ⊆
      edgePairs Orthogonal
        (poorSet q t (Z points C Orthogonal sigma l))
        (Z points C Orthogonal sigma j) := by
  classical
  dsimp only
  intro p hp
  have hp' := (mem_poorChildrenAtRank_iff q t sigma j p).mp hp
  have hrel := extensionChildren_subset_relationPairs
    (Finset.univ : Finset (PointT q t)) Orthogonal sigma hp'.1
  have hrel' := (mem_relationPairs_iff
    (Finset.univ : Finset (PointT q t)) Orthogonal p).mp hrel
  apply (mem_edgePairs_iff Orthogonal _ _ p).mpr
  refine ⟨?_, ?_, hrel'.2.2⟩
  · apply (mem_poorSet_iff q t _ p.1).mpr
    simpa [PoorQ, neighborsInStratum] using hp'.2.2
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp'.2.1⟩

/-- The pivot stratum is at least as large as the exact-rank stratum it was
chosen below. -/
theorem card_rankStratum_le_card_pivotStratum
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) (j : ℕ) :
    let points : Finset (PointT q t) := Finset.univ
    let C := projectiveRankClosure q t
    (Z points C Orthogonal sigma j).card ≤
      (Z points C Orthogonal sigma
        (pivotLevel points C Orthogonal sigma j)).card := by
  dsimp only
  exact Z_card_le_pivot (Finset.univ : Finset (PointT q t))
    (projectiveRankClosure q t) Orthogonal sigma (le_refl j)

/-- Bradač's two-mixing estimate in the exact container vocabulary: for
every history and every rank, at most `2048*q^t` extension children at that
rank have poor first coordinate. -/
theorem card_poorChildrenAtRank_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (sigma : List (PointT q t × PointT q t)) (j : ℕ) :
    (poorChildrenAtRank q t sigma j).card ≤ 2048 * q ^ t := by
  let points : Finset (PointT q t) := Finset.univ
  let C := projectiveRankClosure q t
  let l := pivotLevel points C Orthogonal sigma j
  let A := poorSet q t (Z points C Orthogonal sigma l)
  let B := Z points C Orthogonal sigma j
  calc
    (poorChildrenAtRank q t sigma j).card ≤
        orderedEdges Orthogonal A B := by
      apply card_le_orderedEdges_of_subset_edgePairs
      simpa [points, C, l, A, B] using
        poorChildrenAtRank_subset_edgePairs q t sigma j
    _ ≤ 2048 * q ^ t := by
      apply poorSet_edges_le q t ht
      simpa [points, C, l, B] using
        card_rankStratum_le_card_pivotStratum q t sigma j

/-! ## Summing the rank fibres -/

/-- Compatibility of an extension forces its first coordinate to be
orthogonal to every generator selected at its second coordinate. -/
theorem orthogonal_generators_of_canExtend
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t)
    (hp : CanExtend Orthogonal p sigma) :
    ∀ z ∈ generators Orthogonal sigma p.2, Orthogonal p.1 z := by
  intro z hz
  rw [generators] at hz
  obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hz
  have hold' := Finset.mem_filter.mp hold
  exact hp.2 old (by simpa using hold'.1) hold'.2

/-- Hence the selected generator span has vector rank at most `t`: it lies
in the polar hyperplane of the prospective first coordinate. -/
theorem prefixRank_second_le_of_canExtend
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t)
    (hp : CanExtend Orthogonal p sigma) :
    prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2 ≤ t := by
  let S := generators Orthogonal sigma p.2
  have hspan : pointSpan S ≤ orthSpace p.1 := by
    unfold pointSpan
    exact Finset.sup_le fun z hz =>
      (orthogonal_iff_submodule_le p.1 z).mp
        (orthogonal_generators_of_canExtend q t sigma p hp z hz)
  change Module.finrank (ZMod q) (pointSpan S) ≤ t
  calc
    Module.finrank (ZMod q) (pointSpan S) ≤
        Module.finrank (ZMod q) (orthSpace p.1) :=
      Submodule.finrank_mono hspan
    _ = t := by simpa using finrank_orthSpace p.1

/-- Rank cap specialized to an actual extension child. -/
theorem prefixRank_second_le_of_mem_extensionChildren
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t)
    (hp : p ∈ extensionChildren
      (Finset.univ : Finset (PointT q t)) Orthogonal sigma) :
    prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2 ≤ t := by
  have hp' := Finset.mem_filter.mp hp
  exact prefixRank_second_le_of_canExtend q t sigma p hp'.2

/-- All poor extension children, with the pivot chosen from the rank of the
second coordinate. -/
def poorChildren (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) :
    Finset (PointT q t × PointT q t) :=
  let points : Finset (PointT q t) := Finset.univ
  let C := projectiveRankClosure q t
  (extensionChildren points Orthogonal sigma).filter fun p =>
    PoorQ points C Orthogonal q sigma
      (pivotLevel points C Orthogonal sigma
        (prefixRank C Orthogonal sigma p.2)) p.1

@[simp] theorem mem_poorChildren_iff
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t) :
    p ∈ poorChildren q t sigma <->
      p ∈ extensionChildren (Finset.univ : Finset (PointT q t))
        Orthogonal sigma ∧
      PoorQ (Finset.univ : Finset (PointT q t))
        (projectiveRankClosure q t) Orthogonal q sigma
        (pivotLevel (Finset.univ : Finset (PointT q t))
          (projectiveRankClosure q t) Orthogonal sigma
          (prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2)) p.1 := by
  rw [poorChildren, Finset.mem_filter]

/-- The poor children are the union of the fixed-rank fibres `0,...,t`. -/
theorem poorChildren_subset_biUnion_rank
    (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) :
    poorChildren q t sigma ⊆
      (Finset.range (t + 1)).biUnion fun j =>
        poorChildrenAtRank q t sigma j := by
  intro p hp
  have hp' := (mem_poorChildren_iff q t sigma p).mp hp
  let j := prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ?_), ?_⟩
  · exact prefixRank_second_le_of_mem_extensionChildren q t sigma p hp'.1
  · apply (mem_poorChildrenAtRank_iff q t sigma j p).mpr
    exact ⟨hp'.1, rfl, hp'.2⟩

/-- Uniform per-history poor-child bound, obtained by summing the `t+1`
rank fibres.  This is the poor half of the marked branching estimate. -/
theorem card_poorChildren_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (sigma : List (PointT q t × PointT q t)) :
    (poorChildren q t sigma).card ≤
      2048 * (t + 1) * q ^ t := by
  calc
    (poorChildren q t sigma).card ≤
        ((Finset.range (t + 1)).biUnion fun j =>
          poorChildrenAtRank q t sigma j).card :=
      Finset.card_le_card (poorChildren_subset_biUnion_rank q t sigma)
    _ ≤ ∑ j ∈ Finset.range (t + 1),
        (poorChildrenAtRank q t sigma j).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (t + 1), 2048 * q ^ t := by
      exact Finset.sum_le_sum fun j _ =>
        card_poorChildrenAtRank_le q t ht sigma j
    _ = 2048 * (t + 1) * q ^ t := by
      simp
      ring

end

end Erdos920.PoorChildren
