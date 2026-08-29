/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Basic

/-!
# Flattening an omega sequence of finite blocks

An infinite concatenation of finite walks is most conveniently indexed by
the number of edges already traversed.  The terminal vertex of one block is
identified with the initial vertex of the next, so a block of `m + 1`
vertices contributes `m` new indices.  This file packages that elementary
arithmetic once and for all.

The positive-edge hypothesis is essential: nonempty singleton blocks alone
need not produce an `ℕ`-indexed stream.  In applications it follows from
distinct consecutive macro-chain vertices.
-/

namespace Erdos599
namespace Alternating

open Set

universe u

/-- An omega sequence of finite vertex blocks, joined at their displayed
endpoints.  Each block has at least one edge. -/
structure OmegaBlocks (A : Type u) where
  block : ℕ → List A
  length_pos : ∀ n, 2 ≤ (block n).length
  joins : ∀ n,
    (block n).getLast (by
      have := length_pos n
      exact List.ne_nil_of_length_pos (by omega)) =
      (block (n + 1)).head (by
        have := length_pos (n + 1)
        exact List.ne_nil_of_length_pos (by omega))

namespace OmegaBlocks

variable {A : Type u} (B : OmegaBlocks A)

/-- `List.get` is insensitive to the proof fields in its finite indices. -/
theorem listGet_congr {l₁ l₂ : List A}
    (i₁ : Fin l₁.length) (i₂ : Fin l₂.length)
    (hl : l₁ = l₂) (hi : i₁.1 = i₂.1) :
    l₁.get i₁ = l₂.get i₂ := by
  subst l₂
  exact congrArg l₁.get (Fin.ext hi)

/-- Number of edges contributed by a block. -/
def edgeLength (n : ℕ) : ℕ := (B.block n).length - 1

theorem edgeLength_pos (n : ℕ) : 0 < B.edgeLength n := by
  simp only [edgeLength]
  have := B.length_pos n
  omega

theorem edgeLength_add_one (n : ℕ) :
    B.edgeLength n + 1 = (B.block n).length := by
  simp only [edgeLength]
  have := B.length_pos n
  omega

/-- Cumulative number of edges before block `n`. -/
def boundary (B : OmegaBlocks A) : ℕ → ℕ
  | 0 => 0
  | n + 1 => boundary B n + B.edgeLength n

@[simp]
theorem boundary_zero : B.boundary 0 = 0 := rfl

@[simp]
theorem boundary_succ (n : ℕ) :
    B.boundary (n + 1) = B.boundary n + B.edgeLength n := rfl

theorem boundary_lt_succ (n : ℕ) :
    B.boundary n < B.boundary (n + 1) := by
  rw [B.boundary_succ]
  exact Nat.lt_add_of_pos_right (B.edgeLength_pos n)

theorem boundary_strictMono : StrictMono B.boundary := by
  exact strictMono_nat_of_lt_succ B.boundary_lt_succ

theorem add_le_boundary_add (n k : ℕ) :
    B.boundary n + k ≤ B.boundary (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by omega,
        B.boundary_succ]
      have hpos := B.edgeLength_pos (n + k)
      omega

theorem le_boundary (n : ℕ) : n ≤ B.boundary n := by
  simpa using B.add_le_boundary_add 0 n

theorem exists_lt_boundary_succ (k : ℕ) :
    ∃ n, k < B.boundary (n + 1) := by
  refine ⟨k, ?_⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self k) (B.le_boundary (k + 1))

/-- The unique block whose half-open edge interval contains `k`. -/
noncomputable def locateBlock (k : ℕ) : ℕ :=
  Nat.find (B.exists_lt_boundary_succ k)

theorem lt_boundary_succ_locateBlock (k : ℕ) :
    k < B.boundary (B.locateBlock k + 1) :=
  Nat.find_spec (B.exists_lt_boundary_succ k)

theorem boundary_locateBlock_le (k : ℕ) :
    B.boundary (B.locateBlock k) ≤ k := by
  by_cases hzero : B.locateBlock k = 0
  · simp [hzero]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    rw [hn]
    apply Nat.le_of_not_gt
    intro h
    have hlt : n < B.locateBlock k := by rw [hn]; omega
    exact (Nat.find_min (B.exists_lt_boundary_succ k) hlt) h

theorem locateBlock_eq_iff (k n : ℕ) :
    B.locateBlock k = n ↔
      B.boundary n ≤ k ∧ k < B.boundary (n + 1) := by
  constructor
  · rintro rfl
    exact ⟨B.boundary_locateBlock_le k,
      B.lt_boundary_succ_locateBlock k⟩
  · rintro ⟨hleft, hright⟩
    apply le_antisymm
    · exact Nat.find_min' (B.exists_lt_boundary_succ k) hright
    · by_contra hnot
      have hlt : B.locateBlock k < n := Nat.lt_of_not_ge hnot
      have hbound : B.boundary (B.locateBlock k + 1) ≤ B.boundary n :=
        (B.boundary_strictMono.monotone (by omega))
      exact (Nat.not_lt_of_ge (hbound.trans hleft))
        (B.lt_boundary_succ_locateBlock k)

@[simp]
theorem locateBlock_boundary (n : ℕ) :
    B.locateBlock (B.boundary n) = n := by
  rw [B.locateBlock_eq_iff]
  exact ⟨le_rfl, B.boundary_lt_succ n⟩

/-- Offset of a raw index inside its containing block. -/
noncomputable def blockOffset (k : ℕ) : ℕ :=
  k - B.boundary (B.locateBlock k)

theorem boundary_add_blockOffset (k : ℕ) :
    B.boundary (B.locateBlock k) + B.blockOffset k = k := by
  simp only [blockOffset]
  exact Nat.add_sub_of_le (B.boundary_locateBlock_le k)

theorem blockOffset_lt_edgeLength (k : ℕ) :
    B.blockOffset k < B.edgeLength (B.locateBlock k) := by
  have h := B.lt_boundary_succ_locateBlock k
  rw [B.boundary_succ] at h
  have hle := B.boundary_locateBlock_le k
  simp only [blockOffset]
  omega

theorem blockOffset_lt_length (k : ℕ) :
    B.blockOffset k < (B.block (B.locateBlock k)).length := by
  rw [← B.edgeLength_add_one]
  exact Nat.lt_succ_of_lt (B.blockOffset_lt_edgeLength k)

@[simp]
theorem blockOffset_boundary (n : ℕ) :
    B.blockOffset (B.boundary n) = 0 := by
  simp [blockOffset]

/-- The vertex stream obtained by identifying adjacent block endpoints. -/
noncomputable def rawVertex (k : ℕ) : A :=
  (B.block (B.locateBlock k)).get
    ⟨B.blockOffset k, B.blockOffset_lt_length k⟩

@[simp]
theorem rawVertex_boundary (n : ℕ) :
    B.rawVertex (B.boundary n) =
      (B.block n).head (by
        have := B.length_pos n
        exact List.ne_nil_of_length_pos (by omega)) := by
  simp only [rawVertex, B.locateBlock_boundary, B.blockOffset_boundary,
    List.get_eq_getElem, List.head_eq_getElem]

theorem rawVertex_boundary_succ (n : ℕ) :
    B.rawVertex (B.boundary (n + 1)) =
      (B.block n).getLast (by
        have := B.length_pos n
        exact List.ne_nil_of_length_pos (by omega)) := by
  rw [B.rawVertex_boundary]
  exact (B.joins n).symm

theorem locateBlock_boundary_add_of_lt
    (n j : ℕ) (hj : j < B.edgeLength n) :
    B.locateBlock (B.boundary n + j) = n := by
  rw [B.locateBlock_eq_iff]
  constructor
  · omega
  · rw [B.boundary_succ]
    omega

theorem blockOffset_boundary_add_of_lt
    (n j : ℕ) (hj : j < B.edgeLength n) :
    B.blockOffset (B.boundary n + j) = j := by
  simp [blockOffset, B.locateBlock_boundary_add_of_lt n j hj]

/-- Every proper edge-offset reads directly from the corresponding block. -/
theorem rawVertex_boundary_add_of_lt
    (n j : ℕ) (hj : j < B.edgeLength n) :
    B.rawVertex (B.boundary n + j) =
      (B.block n).get ⟨j, by
        rw [← B.edgeLength_add_one]
        omega⟩ := by
  have hloc := B.locateBlock_boundary_add_of_lt n j hj
  have hoff := B.blockOffset_boundary_add_of_lt n j hj
  unfold rawVertex
  exact listGet_congr _ _ (congrArg B.block hloc) hoff

/-- The closed vertex interval of a block is represented exactly in the raw
stream, including its terminal vertex at the next cumulative boundary. -/
theorem rawVertex_boundary_add
    (n j : ℕ) (hj : j ≤ B.edgeLength n) :
    B.rawVertex (B.boundary n + j) =
      (B.block n).get ⟨j, by
        rw [← B.edgeLength_add_one]
        omega⟩ := by
  rcases lt_or_eq_of_le hj with hjlt | rfl
  · exact B.rawVertex_boundary_add_of_lt n j hjlt
  · rw [← B.boundary_succ, B.rawVertex_boundary_succ]
    rw [List.get_eq_getElem, List.getLast_eq_getElem]
    simp only [edgeLength]

/-- If a vertex belongs to only finitely many blocks, then it occurs at only
finitely many raw indices.  The proof covers the fiber by the finite union
of the corresponding half-open cumulative intervals. -/
theorem rawVertex_fiber_finite
    (hblocks : ∀ x : A, {n | x ∈ B.block n}.Finite) (x : A) :
    {k | B.rawVertex k = x}.Finite := by
  let S : Set ℕ := {n | x ∈ B.block n}
  let U : Set ℕ := ⋃ n ∈ S, Set.Ico (B.boundary n) (B.boundary (n + 1))
  have hS : S.Finite := hblocks x
  have hU : U.Finite := by
    exact hS.biUnion fun n _ ↦ Set.finite_Ico _ _
  apply hU.subset
  intro k hk
  have hkx : B.rawVertex k = x := hk
  have hxblock : x ∈ B.block (B.locateBlock k) := by
    rw [← hkx]
    exact List.get_mem _ _
  refine Set.mem_iUnion.2 ⟨B.locateBlock k,
    Set.mem_iUnion.2 ⟨hxblock, ?_⟩⟩
  exact ⟨B.boundary_locateBlock_le k,
    B.lt_boundary_succ_locateBlock k⟩

/-- A useful finite-set criterion: if among any three members two coincide,
then the set has at most two members. -/
theorem finite_of_triple_eq {S : Set ℕ}
    (h : ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S,
      i = j ∨ i = k ∨ j = k) : S.Finite := by
  classical
  by_cases hSne : S.Nonempty
  · obtain ⟨i, hiS⟩ := hSne
    by_cases hsecond : ∃ j ∈ S, j ≠ i
    · obtain ⟨j, hjS, hji⟩ := hsecond
      apply ((Set.finite_singleton j).insert i).subset
      intro k hkS
      have hpairs := h i hiS j hjS k hkS
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hpairs with hij | hik | hjk
      · exact (hji hij.symm).elim
      · exact Or.inl hik.symm
      · exact Or.inr hjk.symm
    · apply (Set.finite_singleton i).subset
      intro k hkS
      simp only [Set.mem_singleton_iff]
      by_contra hki
      exact hsecond ⟨k, hkS, hki⟩
  · simpa [Set.not_nonempty_iff_eq_empty.mp hSne]

/-- A generic edge predicate carried by every adjacent pair in every
block is carried by every adjacent pair in the flattened raw stream. -/
theorem rawVertex_rel
    (R : A → A → Prop)
    (hR : ∀ n j (hj : j + 1 < (B.block n).length),
      R ((B.block n).get ⟨j, by omega⟩)
        ((B.block n).get ⟨j + 1, hj⟩))
    (k : ℕ) :
    R (B.rawVertex k) (B.rawVertex (k + 1)) := by
  let n := B.locateBlock k
  let j := B.blockOffset k
  have hj : j < B.edgeLength n := B.blockOffset_lt_edgeLength k
  have hk : k = B.boundary n + j :=
    (B.boundary_add_blockOffset k).symm
  have hjlen : j + 1 < (B.block n).length := by
    rw [← B.edgeLength_add_one]
    omega
  rw [hk, B.rawVertex_boundary_add_of_lt n j hj,
    show B.boundary n + j + 1 = B.boundary n + (j + 1) by omega,
    B.rawVertex_boundary_add n (j + 1) (by omega)]
  exact hR n j hjlen

/-- The raw directed edge occurrence at index `k`. -/
noncomputable def rawEdge
    (R : A → A → Prop)
    (hR : ∀ n j (hj : j + 1 < (B.block n).length),
      R ((B.block n).get ⟨j, by omega⟩)
        ((B.block n).get ⟨j + 1, hj⟩))
    (k : ℕ) : {e : A × A // R e.1 e.2} :=
  ⟨(B.rawVertex k, B.rawVertex (k + 1)), B.rawVertex_rel R hR k⟩

@[simp]
theorem rawEdge_fst
    (R : A → A → Prop)
    (hR : ∀ n j (hj : j + 1 < (B.block n).length),
      R ((B.block n).get ⟨j, by omega⟩)
        ((B.block n).get ⟨j + 1, hj⟩))
    (k : ℕ) : (B.rawEdge R hR k).1.1 = B.rawVertex k := rfl

@[simp]
theorem rawEdge_snd
    (R : A → A → Prop)
    (hR : ∀ n j (hj : j + 1 < (B.block n).length),
      R ((B.block n).get ⟨j, by omega⟩)
        ((B.block n).get ⟨j + 1, hj⟩))
    (k : ℕ) : (B.rawEdge R hR k).1.2 = B.rawVertex (k + 1) := rfl

end OmegaBlocks

end Alternating
end Erdos599
