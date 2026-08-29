/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceAppend

/-!
# Cutting and cross-splicing finite coloured occurrence words

An open component in a simultaneous owner-gap repair changes the pairing of
two routes at a common ambient occurrence.  At word level this is a suffix
swap: keep the prefix of each route and attach the suffix of the other one.

This file constructs that operation.  It deliberately proves only literal
occurrence-word facts.  In particular, interval safeness is not postulated
for either cross-spliced word; that is the separate decreasing-gap argument.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace FiniteColouredOccurrenceWord

variable {W Y : Set Gamma.DPath}

private theorem cut_le_length (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) : k.1 ≤ Q.length := by omega

private def prefixVertexIndex (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) (i : Fin (k.1 + 1)) : Fin (Q.length + 1) :=
  i.castLE (Nat.succ_le_succ (cut_le_length Q k))

private def prefixEdgeIndex (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) (i : Fin k.1) : Fin Q.length :=
  i.castLE (cut_le_length Q k)

private theorem prefixVertexIndex_castSucc
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) (i : Fin k.1) :
    prefixVertexIndex Q k i.castSucc = (prefixEdgeIndex Q k i).castSucc := by
  apply Fin.ext
  rfl

private theorem prefixVertexIndex_succ
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) (i : Fin k.1) :
    prefixVertexIndex Q k i.succ = (prefixEdgeIndex Q k i).succ := by
  apply Fin.ext
  rfl

private def suffixVertexIndex (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) (i : Fin (Q.length - k.1 + 1)) :
    Fin (Q.length + 1) := ⟨k.1 + i.1, by omega⟩

private def suffixEdgeIndex (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) (i : Fin (Q.length - k.1)) : Fin Q.length :=
  ⟨k.1 + i.1, by omega⟩

private theorem suffixVertexIndex_castSucc
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) (i : Fin (Q.length - k.1)) :
    suffixVertexIndex Q k i.castSucc = (suffixEdgeIndex Q k i).castSucc := by
  apply Fin.ext
  rfl

private theorem suffixVertexIndex_succ
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) (i : Fin (Q.length - k.1)) :
    suffixVertexIndex Q k i.succ = (suffixEdgeIndex Q k i).succ := by
  apply Fin.ext
  simp [suffixVertexIndex, suffixEdgeIndex, Nat.add_assoc]

/-- The prefix ending at occurrence `k`. -/
def prefixAt (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) : FiniteColouredOccurrenceWord W Y where
  length := k.1
  vertex := fun i ↦ Q.vertex (prefixVertexIndex Q k i)
  direction := fun i ↦ Q.direction (prefixEdgeIndex Q k i)
  actualEdge_spec := by
    intro i
    rw [prefixVertexIndex_castSucc, prefixVertexIndex_succ]
    exact Q.actualEdge_spec (prefixEdgeIndex Q k i)
  occurrence_injective := by
    intro i j hij
    have hmap : prefixEdgeIndex Q k i = prefixEdgeIndex Q k j := by
      apply Q.occurrence_injective
      simpa only [actualEdge, prefixVertexIndex_castSucc,
        prefixVertexIndex_succ] using hij
    exact Fin.ext (by
      simpa [prefixEdgeIndex] using congrArg Fin.val hmap)

/-- The suffix starting at occurrence `k`. -/
def suffixFrom (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) : FiniteColouredOccurrenceWord W Y where
  length := Q.length - k.1
  vertex := fun i ↦ Q.vertex (suffixVertexIndex Q k i)
  direction := fun i ↦ Q.direction (suffixEdgeIndex Q k i)
  actualEdge_spec := by
    intro i
    rw [suffixVertexIndex_castSucc, suffixVertexIndex_succ]
    exact Q.actualEdge_spec (suffixEdgeIndex Q k i)
  occurrence_injective := by
    intro i j hij
    have hmap : suffixEdgeIndex Q k i = suffixEdgeIndex Q k j := by
      apply Q.occurrence_injective
      simpa only [actualEdge, suffixVertexIndex_castSucc,
        suffixVertexIndex_succ] using hij
    exact Fin.ext (by
      simpa [suffixEdgeIndex] using congrArg Fin.val hmap)

@[simp] theorem prefixAt_length (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) : (Q.prefixAt k).length = k.1 := rfl

@[simp] theorem suffixFrom_length (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    (Q.suffixFrom k).length = Q.length - k.1 := rfl

@[simp] theorem prefixAt_first (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    (Q.prefixAt k).vertex 0 = Q.vertex 0 := rfl

@[simp] theorem prefixAt_last (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    (Q.prefixAt k).vertex (Fin.last (Q.prefixAt k).length) = Q.vertex k := by
  have hidx : prefixVertexIndex Q k (Fin.last (Q.prefixAt k).length) = k := by
    apply Fin.ext
    simp [prefixAt, prefixVertexIndex]
  exact congrArg Q.vertex hidx

@[simp] theorem suffixFrom_first (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    (Q.suffixFrom k).vertex 0 = Q.vertex k := by
  have hidx : suffixVertexIndex Q k 0 = k := by
    apply Fin.ext
    simp [suffixFrom, suffixVertexIndex]
  exact congrArg Q.vertex hidx

@[simp] theorem suffixFrom_last (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    (Q.suffixFrom k).vertex (Fin.last (Q.suffixFrom k).length) =
      Q.vertex (Fin.last Q.length) := by
  have hidx :
      suffixVertexIndex Q k (Fin.last (Q.suffixFrom k).length) =
        Fin.last Q.length := by
    apply Fin.ext
    simp [suffixFrom, suffixVertexIndex]
    omega
  exact congrArg Q.vertex hidx

private theorem prefixAt_actualEdge
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) (i : Fin k.1) :
    (Q.prefixAt k).actualEdge i =
      Q.actualEdge (prefixEdgeIndex Q k i) := by
  unfold actualEdge
  change (match Q.direction (prefixEdgeIndex Q k i) with
    | .forward =>
        (Q.vertex (prefixVertexIndex Q k i.castSucc),
          Q.vertex (prefixVertexIndex Q k i.succ))
    | .backward =>
        (Q.vertex (prefixVertexIndex Q k i.succ),
          Q.vertex (prefixVertexIndex Q k i.castSucc))) = _
  rw [prefixVertexIndex_castSucc, prefixVertexIndex_succ]
  rfl

private theorem suffixFrom_actualEdge
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) (i : Fin (Q.length - k.1)) :
    (Q.suffixFrom k).actualEdge i =
      Q.actualEdge (suffixEdgeIndex Q k i) := by
  unfold actualEdge
  change (match Q.direction (suffixEdgeIndex Q k i) with
    | .forward =>
        (Q.vertex (suffixVertexIndex Q k i.castSucc),
          Q.vertex (suffixVertexIndex Q k i.succ))
    | .backward =>
        (Q.vertex (suffixVertexIndex Q k i.succ),
          Q.vertex (suffixVertexIndex Q k i.castSucc))) = _
  rw [suffixVertexIndex_castSucc, suffixVertexIndex_succ]
  rfl

theorem prefixAt_forwardEdges_subset
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    (Q.prefixAt k).forwardEdges ⊆ Q.forwardEdges := by
  rintro e ⟨i, rfl⟩
  let i' : Fin k.1 := ⟨i.1.1, by simpa using i.1.2⟩
  have hii : i.1 = i' := Fin.ext rfl
  let j : Fin Q.length := prefixEdgeIndex Q k i'
  refine ⟨⟨j, ?_⟩, ?_⟩
  · simpa [prefixAt, j, i'] using i.2
  · simp only [forwardEdge]
    rw [hii, Q.prefixAt_actualEdge k i']

theorem prefixAt_backwardEdges_subset
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    (Q.prefixAt k).backwardEdges ⊆ Q.backwardEdges := by
  rintro e ⟨i, rfl⟩
  let i' : Fin k.1 := ⟨i.1.1, by simpa using i.1.2⟩
  have hii : i.1 = i' := Fin.ext rfl
  let j : Fin Q.length := prefixEdgeIndex Q k i'
  refine ⟨⟨j, ?_⟩, ?_⟩
  · simpa [prefixAt, j, i'] using i.2
  · simp only [backwardEdge]
    rw [hii, Q.prefixAt_actualEdge k i']

theorem suffixFrom_forwardEdges_subset
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    (Q.suffixFrom k).forwardEdges ⊆ Q.forwardEdges := by
  rintro e ⟨i, rfl⟩
  let i' : Fin (Q.length - k.1) := ⟨i.1.1, by simpa using i.1.2⟩
  have hii : i.1 = i' := Fin.ext rfl
  let j : Fin Q.length := suffixEdgeIndex Q k i'
  refine ⟨⟨j, ?_⟩, ?_⟩
  · simpa [suffixFrom, j, i'] using i.2
  · simp only [forwardEdge]
    rw [hii, Q.suffixFrom_actualEdge k i']

theorem suffixFrom_backwardEdges_subset
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    (Q.suffixFrom k).backwardEdges ⊆ Q.backwardEdges := by
  rintro e ⟨i, rfl⟩
  let i' : Fin (Q.length - k.1) := ⟨i.1.1, by simpa using i.1.2⟩
  have hii : i.1 = i' := Fin.ext rfl
  let j : Fin Q.length := suffixEdgeIndex Q k i'
  refine ⟨⟨j, ?_⟩, ?_⟩
  · simpa [suffixFrom, j, i'] using i.2
  · simp only [backwardEdge]
    rw [hii, Q.suffixFrom_actualEdge k i']

/-- Cutting at an occurrence partitions the ambient vertex carrier.  The cut
occurrence itself belongs to both pieces. -/
theorem vertexSet_eq_prefixAt_union_suffixFrom
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    Q.vertexSet = (Q.prefixAt k).vertexSet ∪ (Q.suffixFrom k).vertexSet := by
  apply Set.Subset.antisymm
  · rintro x ⟨i, rfl⟩
    by_cases hik : i.1 ≤ k.1
    · left
      let j : Fin (k.1 + 1) := ⟨i.1, by omega⟩
      refine ⟨j, ?_⟩
      have hindex : prefixVertexIndex Q k j = i := Fin.ext rfl
      exact congrArg Q.vertex hindex
    · right
      let j : Fin (Q.length - k.1 + 1) := ⟨i.1 - k.1, by omega⟩
      refine ⟨j, ?_⟩
      have hindex : suffixVertexIndex Q k j = i := by
        apply Fin.ext
        simp [suffixVertexIndex, j]
        omega
      exact congrArg Q.vertex hindex
  · rintro x (hx | hx)
    · rcases hx with ⟨i, rfl⟩
      exact ⟨prefixVertexIndex Q k i, rfl⟩
    · rcases hx with ⟨i, rfl⟩
      exact ⟨suffixVertexIndex Q k i, rfl⟩

theorem forwardEdges_eq_prefixAt_union_suffixFrom
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    Q.forwardEdges =
      (Q.prefixAt k).forwardEdges ∪ (Q.suffixFrom k).forwardEdges := by
  apply Set.Subset.antisymm
  · rintro e ⟨i, rfl⟩
    by_cases hik : i.1.1 < k.1
    · left
      let j : Fin k.1 := ⟨i.1.1, hik⟩
      have hmap : prefixEdgeIndex Q k j = i.1 := Fin.ext rfl
      refine ⟨⟨j, ?_⟩, ?_⟩
      · simpa [prefixAt, hmap] using i.2
      · simp only [forwardEdge]
        rw [Q.prefixAt_actualEdge k j, hmap]
    · right
      let j : Fin (Q.length - k.1) := ⟨i.1.1 - k.1, by omega⟩
      have hmap : suffixEdgeIndex Q k j = i.1 := by
        apply Fin.ext
        simp [suffixEdgeIndex, j]
        omega
      refine ⟨⟨j, ?_⟩, ?_⟩
      · simpa [suffixFrom, hmap] using i.2
      · simp only [forwardEdge]
        rw [Q.suffixFrom_actualEdge k j, hmap]
  · exact Set.union_subset (Q.prefixAt_forwardEdges_subset k)
      (Q.suffixFrom_forwardEdges_subset k)

theorem backwardEdges_eq_prefixAt_union_suffixFrom
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    Q.backwardEdges =
      (Q.prefixAt k).backwardEdges ∪ (Q.suffixFrom k).backwardEdges := by
  apply Set.Subset.antisymm
  · rintro e ⟨i, rfl⟩
    by_cases hik : i.1.1 < k.1
    · left
      let j : Fin k.1 := ⟨i.1.1, hik⟩
      have hmap : prefixEdgeIndex Q k j = i.1 := Fin.ext rfl
      refine ⟨⟨j, ?_⟩, ?_⟩
      · simpa [prefixAt, hmap] using i.2
      · simp only [backwardEdge]
        rw [Q.prefixAt_actualEdge k j, hmap]
    · right
      let j : Fin (Q.length - k.1) := ⟨i.1.1 - k.1, by omega⟩
      have hmap : suffixEdgeIndex Q k j = i.1 := by
        apply Fin.ext
        simp [suffixEdgeIndex, j]
        omega
      refine ⟨⟨j, ?_⟩, ?_⟩
      · simpa [suffixFrom, hmap] using i.2
      · simp only [backwardEdge]
        rw [Q.suffixFrom_actualEdge k j, hmap]
  · exact Set.union_subset (Q.prefixAt_backwardEdges_subset k)
      (Q.suffixFrom_backwardEdges_subset k)

private theorem prefixAt_suffixFrom_no_common_occurrence
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1))
    (i : Fin (Q.prefixAt k).length)
    (j : Fin (Q.suffixFrom k).length)
    (hdir : (Q.prefixAt k).direction i = (Q.suffixFrom k).direction j)
    (hedge : (Q.prefixAt k).actualEdge i =
      (Q.suffixFrom k).actualEdge j) : False := by
  let i' : Fin k.1 := ⟨i.1, by simpa using i.2⟩
  let j' : Fin (Q.length - k.1) := ⟨j.1, by simpa using j.2⟩
  have hii : i = i' := Fin.ext rfl
  have hjj : j = j' := Fin.ext rfl
  have hmap : prefixEdgeIndex Q k i' = suffixEdgeIndex Q k j' := by
    apply Q.occurrence_injective
    apply Prod.ext
    · simpa [prefixAt, suffixFrom, hii, hjj] using hdir
    · change Q.actualEdge (prefixEdgeIndex Q k i') =
        Q.actualEdge (suffixEdgeIndex Q k j')
      simpa only [hii, hjj, Q.prefixAt_actualEdge k i',
        Q.suffixFrom_actualEdge k j'] using hedge
  have hv : i'.1 = k.1 + j'.1 := by
    simpa [prefixEdgeIndex, suffixEdgeIndex] using congrArg Fin.val hmap
  have hi := i'.2
  omega

theorem prefixAt_forwardEdges_disjoint_suffixFrom
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    Disjoint (Q.prefixAt k).forwardEdges (Q.suffixFrom k).forwardEdges := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hji⟩
  apply Q.prefixAt_suffixFrom_no_common_occurrence k i.1 j.1
  · exact i.2.trans j.2.symm
  · simpa only [forwardEdge] using hji.symm

theorem prefixAt_backwardEdges_disjoint_suffixFrom
    (Q : FiniteColouredOccurrenceWord W Y)
    (k : Fin (Q.length + 1)) :
    Disjoint (Q.prefixAt k).backwardEdges (Q.suffixFrom k).backwardEdges := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hji⟩
  apply Q.prefixAt_suffixFrom_no_common_occurrence k i.1 j.1
  · exact (Q.prefixAt k).backwardIndex_direction i |>.trans
      ((Q.suffixFrom k).backwardIndex_direction j).symm
  · simpa only [backwardEdge] using hji.symm

/-- Recombine the prefix of `Q` and the suffix of `P` at equal ambient
occurrences.  Global same-colour freshness implies the freshness needed by
the literal append operation. -/
def crossSplice (Q P : FiniteColouredOccurrenceWord W Y)
    (i : Fin (Q.length + 1)) (j : Fin (P.length + 1))
    (hmeet : Q.vertex i = P.vertex j)
    (hforward : Disjoint Q.forwardEdges P.forwardEdges)
    (hbackward : Disjoint Q.backwardEdges P.backwardEdges) :
    FiniteColouredOccurrenceWord W Y :=
  (Q.prefixAt i).append (P.suffixFrom j)
    (by simpa only [prefixAt_last, suffixFrom_first] using hmeet)
    (hforward.mono (Q.prefixAt_forwardEdges_subset i)
      (P.suffixFrom_forwardEdges_subset j))
    (hbackward.mono (Q.prefixAt_backwardEdges_subset i)
      (P.suffixFrom_backwardEdges_subset j))

@[simp] theorem crossSplice_first
    (Q P : FiniteColouredOccurrenceWord W Y)
    (i : Fin (Q.length + 1)) (j : Fin (P.length + 1))
    (hmeet hforward hbackward) :
    (Q.crossSplice P i j hmeet hforward hbackward).vertex 0 = Q.vertex 0 := by
  unfold crossSplice
  rw [append_first, prefixAt_first]

@[simp] theorem crossSplice_last
    (Q P : FiniteColouredOccurrenceWord W Y)
    (i : Fin (Q.length + 1)) (j : Fin (P.length + 1))
    (hmeet hforward hbackward) :
    (Q.crossSplice P i j hmeet hforward hbackward).vertex
        (Fin.last (Q.crossSplice P i j hmeet hforward hbackward).length) =
      P.vertex (Fin.last P.length) := by
  unfold crossSplice
  change ((Q.prefixAt i).append (P.suffixFrom j) _ _ _).vertex
      (Fin.last ((Q.prefixAt i).length + (P.suffixFrom j).length)) = _
  rw [append_last, suffixFrom_last]

theorem crossSplice_forwardEdges
    (Q P : FiniteColouredOccurrenceWord W Y)
    (i : Fin (Q.length + 1)) (j : Fin (P.length + 1))
    (hmeet hforward hbackward) :
    (Q.crossSplice P i j hmeet hforward hbackward).forwardEdges =
      (Q.prefixAt i).forwardEdges ∪ (P.suffixFrom j).forwardEdges := by
  apply append_forwardEdges

theorem crossSplice_backwardEdges
    (Q P : FiniteColouredOccurrenceWord W Y)
    (i : Fin (Q.length + 1)) (j : Fin (P.length + 1))
    (hmeet hforward hbackward) :
    (Q.crossSplice P i j hmeet hforward hbackward).backwardEdges =
      (Q.prefixAt i).backwardEdges ∪ (P.suffixFrom j).backwardEdges := by
  apply append_backwardEdges

/-- Swapping both suffixes preserves the exact aggregate forward relation.
The two output terminals are exchanged, but no forward occurrence is lost or
created. -/
theorem crossSplice_pair_forwardEdges
    (Q P : FiniteColouredOccurrenceWord W Y)
    (i : Fin (Q.length + 1)) (j : Fin (P.length + 1))
    (hmeet : Q.vertex i = P.vertex j)
    (hforward : Disjoint Q.forwardEdges P.forwardEdges)
    (hbackward : Disjoint Q.backwardEdges P.backwardEdges) :
    (Q.crossSplice P i j hmeet hforward hbackward).forwardEdges ∪
        (P.crossSplice Q j i hmeet.symm hforward.symm hbackward.symm).forwardEdges =
      Q.forwardEdges ∪ P.forwardEdges := by
  rw [Q.crossSplice_forwardEdges P i j,
    P.crossSplice_forwardEdges Q j i,
    Q.forwardEdges_eq_prefixAt_union_suffixFrom i,
    P.forwardEdges_eq_prefixAt_union_suffixFrom j]
  ext e
  simp only [Set.mem_union]
  tauto

/-- Swapping both suffixes preserves the exact aggregate removed-reference
relation. -/
theorem crossSplice_pair_backwardEdges
    (Q P : FiniteColouredOccurrenceWord W Y)
    (i : Fin (Q.length + 1)) (j : Fin (P.length + 1))
    (hmeet : Q.vertex i = P.vertex j)
    (hforward : Disjoint Q.forwardEdges P.forwardEdges)
    (hbackward : Disjoint Q.backwardEdges P.backwardEdges) :
    (Q.crossSplice P i j hmeet hforward hbackward).backwardEdges ∪
        (P.crossSplice Q j i hmeet.symm hforward.symm hbackward.symm).backwardEdges =
      Q.backwardEdges ∪ P.backwardEdges := by
  rw [Q.crossSplice_backwardEdges P i j,
    P.crossSplice_backwardEdges Q j i,
    Q.backwardEdges_eq_prefixAt_union_suffixFrom i,
    P.backwardEdges_eq_prefixAt_union_suffixFrom j]
  ext e
  simp only [Set.mem_union]
  tauto

#print axioms crossSplice_first
#print axioms crossSplice_last
#print axioms crossSplice_forwardEdges
#print axioms crossSplice_backwardEdges
#print axioms crossSplice_pair_forwardEdges
#print axioms crossSplice_pair_backwardEdges

end FiniteColouredOccurrenceWord
end Alternating
end Erdos599
