/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalOnlineCandidates

/-!
# Coordinate-sensitive occupancy for hierarchical embeddings

The earlier unified-pool backend assigns one physical interior pool to an
entire segment.  A segment embedded across a matching edge alternates between
its two endpoint clusters, so that accounting charges its full order to both
endpoint degree budgets.  Zhao's Lemma 5.8 instead charges the actual colour
class on each endpoint, with one extra small-component carry per bin.

This file contains the graph-independent accounting for that correction.
An interior coordinate chooses its own physical pool.  The used-set bound is
the literal endpoint load; adding the current segment order costs only the
single global `small` carry.  No embedding, copy, or continuation is an input.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalCoordinatePools

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest

universe u

namespace HierarchicalSegmentForest

variable {r s : ℕ} {B : Type u} {Pool : Type*} [DecidableEq Pool]

/-- Coordinates of segment `i` which are nonroots and occupy physical pool
`e`. -/
def interiorCoordinatesAtPool (F : HierarchicalSegmentForest r s)
    (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
    (i : Fin s) (e : Pool) : Finset (Fin (F.segments.size i)) :=
  Finset.univ.filter fun a ↦
    a ≠ F.segments.root i ∧ interiorPool i a = e

/-- Exact occupancy contributed by one segment to one endpoint pool. -/
def coordinatePoolWeight (F : HierarchicalSegmentForest r s)
    (rootPool : Fin s → Pool)
    (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
    (i : Fin s) (e : Pool) : ℕ :=
  (if rootPool i = e then 1 else 0) +
    #(interiorCoordinatesAtPool F interiorPool i e)

/-- Total literal endpoint occupancy over all hierarchy segments. -/
def coordinatePoolLoad (F : HierarchicalSegmentForest r s)
    (rootPool : Fin s → Pool)
    (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
    (e : Pool) : ℕ :=
  ∑ i, coordinatePoolWeight F rootPool interiorPool i e

/-- All hierarchy coordinates whose actual image is charged to pool `e`.
The segment root uses `rootPool`; every other coordinate uses its own
`interiorPool`. -/
def coordinatesAtPool (F : HierarchicalSegmentForest r s)
    (rootPool : Fin s → Pool)
    (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
    (e : Pool) : Finset (Σ i, Fin (F.segments.size i)) :=
  Finset.univ.filter fun z ↦
    if z.2 = F.segments.root z.1 then rootPool z.1 = e
    else interiorPool z.1 z.2 = e

theorem coordinatePoolWeight_eq_card_filter
    (F : HierarchicalSegmentForest r s)
    (rootPool : Fin s → Pool)
    (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
    (i : Fin s) (e : Pool) :
    coordinatePoolWeight F rootPool interiorPool i e =
      #(Finset.univ.filter fun a : Fin (F.segments.size i) ↦
        if a = F.segments.root i then rootPool i = e
        else interiorPool i a = e) := by
  classical
  let R : Finset (Fin (F.segments.size i)) :=
    if rootPool i = e then {F.segments.root i} else ∅
  let I := interiorCoordinatesAtPool F interiorPool i e
  have hdisj : Disjoint R I := by
    rw [Finset.disjoint_left]
    intro a haR haI
    have haNe := (Finset.mem_filter.mp haI).2.1
    by_cases heq : rootPool i = e
    · have haEq : a = F.segments.root i := by
        simpa only [R, heq, if_pos, Finset.mem_singleton] using haR
      exact haNe haEq
    · have hempty : R = ∅ := by simp [R, heq]
      rw [hempty] at haR
      simpa using haR
  have hunion : R ∪ I =
      Finset.univ.filter fun a : Fin (F.segments.size i) ↦
        if a = F.segments.root i then rootPool i = e
        else interiorPool i a = e := by
    ext a
    by_cases haroot : a = F.segments.root i
    · subst a
      by_cases heq : rootPool i = e <;>
        simp [R, I, interiorCoordinatesAtPool, heq]
    · by_cases heq : rootPool i = e <;>
        simp [R, I, interiorCoordinatesAtPool, haroot, heq]
  rw [coordinatePoolWeight, ← hunion,
    Finset.card_union_of_disjoint hdisj]
  by_cases heq : rootPool i = e <;> simp [R, I, heq]

noncomputable def coordinatesAtPoolEquiv
    (F : HierarchicalSegmentForest r s)
    (rootPool : Fin s → Pool)
    (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
    (e : Pool) :
    ↑(coordinatesAtPool F rootPool interiorPool e) ≃
      Σ i : Fin s,
        ↑(Finset.univ.filter fun a : Fin (F.segments.size i) ↦
          if a = F.segments.root i then rootPool i = e
          else interiorPool i a = e) where
  toFun z := by
    have hz := (Finset.mem_filter.mp z.2).2
    exact ⟨z.1.1, ⟨z.1.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩⟩
  invFun z :=
    ⟨⟨z.1, z.2.1⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp z.2.2).2⟩⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (Subtype.ext rfl)

/-- The sum definition of coordinate occupancy is exactly the cardinality
of the corresponding set of dependent hierarchy coordinates. -/
theorem coordinatePoolLoad_eq_card_coordinatesAtPool
    (F : HierarchicalSegmentForest r s)
    (rootPool : Fin s → Pool)
    (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
    (e : Pool) :
    coordinatePoolLoad F rootPool interiorPool e =
      #(coordinatesAtPool F rootPool interiorPool e) := by
  classical
  have hcard := Fintype.card_congr
    (coordinatesAtPoolEquiv F rootPool interiorPool e)
  simp only [Fintype.card_coe, Fintype.card_sigma] at hcard
  rw [coordinatePoolLoad]
  calc
    (∑ i, coordinatePoolWeight F rootPool interiorPool i e) =
        ∑ i, #(Finset.univ.filter fun a : Fin (F.segments.size i) ↦
          if a = F.segments.root i then rootPool i = e
          else interiorPool i a = e) := by
      apply Finset.sum_congr rfl
      intro i _
      exact coordinatePoolWeight_eq_card_filter F rootPool interiorPool i e
    _ = #(coordinatesAtPool F rootPool interiorPool e) := hcard.symm

section Used

variable [Fintype B] [DecidableEq B]
  (F : HierarchicalSegmentForest r s)
  (G : SimpleGraph B)
  (rootPool : Fin s → Pool)
  (interiorPool : (i : Fin s) → Fin (F.segments.size i) → Pool)
  (rootCandidate : Fin s → Finset B)
  (interiorCandidate : (i : Fin s) →
    Fin (F.segments.size i) → Finset B)

/-- Images of one realized segment which occupy physical pool `e`. -/
def coordinateUsedPiece (j : Fin s) (e : Pool)
    (R : SegmentRealization F G rootCandidate interiorCandidate j) : Finset B :=
  (if rootPool j = e then {R.rootImage} else ∅) ∪
    (interiorCoordinatesAtPool F interiorPool j e).image R.copy

/-- Images of all earlier segments which occupy physical pool `e`. -/
def coordinateUsedPool (i : Fin s) (e : Pool)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) : Finset B :=
  (Finset.Iio i).attach.biUnion fun j ↦
    coordinateUsedPiece F G rootPool interiorPool rootCandidate
      interiorCandidate j.1 e
      (prior j.1 (Fin.mk_lt_mk.mp (Finset.mem_Iio.mp j.2)))

theorem card_coordinateUsedPiece_le_weight (j : Fin s) (e : Pool)
    (R : SegmentRealization F G rootCandidate interiorCandidate j) :
    #(coordinateUsedPiece F G rootPool interiorPool rootCandidate
        interiorCandidate j e R) ≤
      coordinatePoolWeight F rootPool interiorPool j e := by
  classical
  rw [coordinateUsedPiece, coordinatePoolWeight]
  calc
    #((if rootPool j = e then {R.rootImage} else ∅) ∪
        (interiorCoordinatesAtPool F interiorPool j e).image R.copy) ≤
        #(if rootPool j = e then {R.rootImage} else ∅) +
          #((interiorCoordinatesAtPool F interiorPool j e).image R.copy) :=
      Finset.card_union_le _ _
    _ ≤ (if rootPool j = e then 1 else 0) +
        #(interiorCoordinatesAtPool F interiorPool j e) := by
      gcongr
      · split <;> simp
      · exact Finset.card_image_le

theorem card_coordinateUsedPool_le_load (i : Fin s) (e : Pool)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) :
    #(coordinateUsedPool F G rootPool interiorPool rootCandidate
        interiorCandidate i e prior) ≤
      coordinatePoolLoad F rootPool interiorPool e := by
  classical
  calc
    #(coordinateUsedPool F G rootPool interiorPool rootCandidate
        interiorCandidate i e prior) ≤
        ∑ j ∈ (Finset.Iio i).attach,
          #(coordinateUsedPiece F G rootPool interiorPool rootCandidate
            interiorCandidate j.1 e
            (prior j.1 (Fin.mk_lt_mk.mp (Finset.mem_Iio.mp j.2)))) :=
      Finset.card_biUnion_le
    _ ≤ ∑ j ∈ (Finset.Iio i).attach,
        coordinatePoolWeight F rootPool interiorPool j.1 e := by
      exact Finset.sum_le_sum fun j _ ↦
        card_coordinateUsedPiece_le_weight F G rootPool interiorPool
          rootCandidate interiorCandidate j.1 e _
    _ = ∑ j ∈ Finset.Iio i,
        coordinatePoolWeight F rootPool interiorPool j e :=
      Finset.sum_attach (Finset.Iio i)
        (fun j ↦ coordinatePoolWeight F rootPool interiorPool j e)
    _ ≤ ∑ j, coordinatePoolWeight F rootPool interiorPool j e := by
      have hsub : Finset.Iio i ⊆ (Finset.univ : Finset (Fin s)) :=
        Finset.subset_univ (Finset.Iio i)
      exact Finset.sum_le_sum_of_subset hsub
    _ = coordinatePoolLoad F rootPool interiorPool e := rfl

/-- The one-carry form used by a rooted-tree embedding step.  Earlier exact
endpoint occupancy plus the full current segment fits inside endpoint load
plus one global small-component allowance. -/
theorem card_coordinateUsedPool_add_size_le_load_add_small
    (small : ℕ) (hsmall : ∀ j, F.segments.size j ≤ small)
    (i : Fin s) (e : Pool)
    (prior : ∀ j : Fin s, j.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate j) :
    #(coordinateUsedPool F G rootPool interiorPool rootCandidate
        interiorCandidate i e prior) + F.segments.size i ≤
      coordinatePoolLoad F rootPool interiorPool e + small := by
  exact Nat.add_le_add
    (card_coordinateUsedPool_le_load F G rootPool interiorPool rootCandidate
      interiorCandidate i e prior) (hsmall i)

theorem root_mem_coordinateUsedPool (i j : Fin s) (hj : j.val < i.val)
    (e : Pool) (he : rootPool j = e)
    (prior : ∀ t : Fin s, t.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate t) :
    (prior j hj).rootImage ∈
      coordinateUsedPool F G rootPool interiorPool rootCandidate
        interiorCandidate i e prior := by
  classical
  apply Finset.mem_biUnion.mpr
  let jm : {j // j ∈ Finset.Iio i} := ⟨j, by simpa using hj⟩
  refine ⟨jm, Finset.mem_attach _ _, ?_⟩
  rw [coordinateUsedPiece, if_pos he]
  exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

theorem coordinate_mem_coordinateUsedPool
    (i j : Fin s) (hj : j.val < i.val)
    (b : Fin (F.segments.size j))
    (hb : b ≠ F.segments.root j) (e : Pool)
    (he : interiorPool j b = e)
    (prior : ∀ t : Fin s, t.val < i.val →
      SegmentRealization F G rootCandidate interiorCandidate t) :
    (prior j hj).copy b ∈
      coordinateUsedPool F G rootPool interiorPool rootCandidate
        interiorCandidate i e prior := by
  classical
  apply Finset.mem_biUnion.mpr
  let jm : {j // j ∈ Finset.Iio i} := ⟨j, by simpa using hj⟩
  refine ⟨jm, Finset.mem_attach _ _, ?_⟩
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨b, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, he⟩

end Used

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalCoordinatePools

#print axioms Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest.card_coordinateUsedPool_le_load
#print axioms Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest.card_coordinateUsedPool_add_size_le_load_add_small
