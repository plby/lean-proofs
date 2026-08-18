/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.BlockMatching
import ErdosProblems.Erdos1124.Flow

/-!
# Finite lattice blocks in free additive orbits

This file supplies the bookkeeping bridge between a bounded flow on the
graph of a free `ℤ^d`-action and the block matching argument.  It first makes
a classical, but fixed, choice of one representative in every orbit and uses
freeness to assign an unambiguous lattice coordinate to every point.  The
coordinate cubes of a fixed positive side length give a partition into finite
blocks.  The final section aggregates a point flow across any such finite
partition into the antisymmetric integer block flow expected by
`BlockMatching`.
-/

open Function Set
open scoped BigOperators

namespace Erdos1124.OrbitBlocks

noncomputable section

abbrev Lattice (d : ℕ) := Flow.Lattice d

section OrbitCoordinates

variable {d : ℕ} {X : Type*} [AddAction (Lattice d) X]

/-- The type of orbits of the lattice action. -/
abbrev Orbit := AddAction.orbitRel.Quotient (Lattice d) X

/-- The orbit containing a point. -/
def orbitClass (x : X) : Orbit (d := d) (X := X) := Quotient.mk'' x

/-- A fixed classical representative of an orbit. -/
def orbitRep (ω : Orbit (d := d) (X := X)) : X := ω.out

@[simp]
lemma orbitClass_orbitRep (ω : Orbit (d := d) (X := X)) :
    orbitClass (d := d) (orbitRep (d := d) ω) = ω := by
  exact Quotient.out_eq' ω

lemma exists_vadd_orbitRep (x : X) :
    ∃ n : Lattice d,
      n +ᵥ orbitRep (d := d) (orbitClass (d := d) x) = x := by
  have hq : orbitClass (d := d) x =
      orbitClass (d := d) (orbitRep (d := d) (orbitClass (d := d) x)) := by simp
  have hr := Quotient.exact hq
  exact AddAction.mem_orbit_iff.mp hr

/-- The lattice coordinate of a point relative to the chosen representative
of its orbit. -/
def orbitCoord (x : X) : Lattice d :=
  Classical.choose (exists_vadd_orbitRep (d := d) x)

@[simp]
lemma orbitCoord_vadd_orbitRep (x : X) :
    orbitCoord (d := d) x +ᵥ
      orbitRep (d := d) (orbitClass (d := d) x) = x :=
  Classical.choose_spec (exists_vadd_orbitRep (d := d) x)

/-- Pointwise freeness, in the form most convenient for orbit coordinates. -/
def FreeAction : Prop :=
  ∀ x : X, Function.Injective (fun n : Lattice d ↦ n +ᵥ x)

lemma orbitClass_vadd (n : Lattice d) (x : X) :
    orbitClass (d := d) (n +ᵥ x) = orbitClass (d := d) x := by
  exact AddAction.orbitRel.Quotient.quotient_vadd_eq

lemma orbitCoord_vadd (hfree : FreeAction (d := d) (X := X))
    (n : Lattice d) (x : X) :
    orbitCoord (d := d) (n +ᵥ x) = n + orbitCoord (d := d) x := by
  apply hfree (orbitRep (d := d) (orbitClass (d := d) x))
  change orbitCoord (d := d) (n +ᵥ x) +ᵥ
      orbitRep (d := d) (orbitClass (d := d) x) =
    (n + orbitCoord (d := d) x) +ᵥ
      orbitRep (d := d) (orbitClass (d := d) x)
  calc
    orbitCoord (d := d) (n +ᵥ x) +ᵥ
        orbitRep (d := d) (orbitClass (d := d) x) =
      orbitCoord (d := d) (n +ᵥ x) +ᵥ
        orbitRep (d := d) (orbitClass (d := d) (n +ᵥ x)) := by
          rw [orbitClass_vadd (d := d)]
    _ = n +ᵥ x := orbitCoord_vadd_orbitRep (d := d) (n +ᵥ x)
    _ = (n + orbitCoord (d := d) x) +ᵥ
        orbitRep (d := d) (orbitClass (d := d) x) := by
          rw [add_vadd, orbitCoord_vadd_orbitRep (d := d)]

lemma orbitCoordinate_injective :
    Function.Injective (fun x : X ↦
      (orbitClass (d := d) x, orbitCoord (d := d) x)) := by
  intro x y h
  have hc : orbitClass x = orbitClass y := congrArg Prod.fst h
  have hn : orbitCoord x = orbitCoord y := congrArg Prod.snd h
  rw [← orbitCoord_vadd_orbitRep (d := d) x,
    ← orbitCoord_vadd_orbitRep (d := d) y, hc, hn]

lemma orbitCoord_orbitRep_eq_zero
    (hfree : FreeAction (d := d) (X := X))
    (ω : Orbit (d := d) (X := X)) :
    orbitCoord (d := d) (orbitRep (d := d) ω) = 0 := by
  apply hfree (orbitRep (d := d) ω)
  change orbitCoord (d := d) (orbitRep (d := d) ω) +ᵥ orbitRep (d := d) ω =
    (0 : Lattice d) +ᵥ orbitRep (d := d) ω
  rw [zero_vadd]
  simpa using orbitCoord_vadd_orbitRep (d := d) (orbitRep (d := d) ω)

/-- A free action is (classically) the product of its orbit space and one
copy of the acting lattice. -/
def orbitCoordinateEquiv (hfree : FreeAction (d := d) (X := X)) :
    X ≃ Orbit (d := d) (X := X) × Lattice d where
  toFun x := (orbitClass (d := d) x, orbitCoord (d := d) x)
  invFun p := p.2 +ᵥ orbitRep (d := d) p.1
  left_inv x := orbitCoord_vadd_orbitRep (d := d) x
  right_inv p := by
    apply Prod.ext
    · simp [orbitClass_vadd (d := d)]
    · change orbitCoord (d := d) (p.2 +ᵥ orbitRep (d := d) p.1) = p.2
      rw [orbitCoord_vadd (d := d) hfree,
        orbitCoord_orbitRep_eq_zero (d := d) hfree, add_zero]

end OrbitCoordinates

section LatticeBlocks

variable {d : ℕ} {X : Type*} [AddAction (Lattice d) X]

/-- Coordinatewise quotient and remainder by a positive natural side length. -/
def latticeDivMod (M : ℕ) [NeZero M] :
    Lattice d ≃ Lattice d × (Fin d → Fin M) where
  toFun n :=
    (fun i ↦ ((Int.divModEquiv M) (n i)).1,
      fun i ↦ ((Int.divModEquiv M) (n i)).2)
  invFun p := fun i ↦ (Int.divModEquiv M).symm (p.1 i, p.2 i)
  left_inv n := by
    funext i
    exact (Int.divModEquiv M).symm_apply_apply (n i)
  right_inv p := by
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst ((Int.divModEquiv M).apply_symm_apply (p.1 i, p.2 i))
    · exact congrArg Prod.snd ((Int.divModEquiv M).apply_symm_apply (p.1 i, p.2 i))

/-- One block is specified by its orbit and its coarse lattice coordinate. -/
abbrev BlockIndex := Orbit (d := d) (X := X) × Lattice d

/-- The point in a block with a prescribed finite remainder coordinate. -/
def blockPoint (M : ℕ) [NeZero M]
    (i : BlockIndex (d := d) (X := X)) (q : Fin d → Fin M) : X :=
  (latticeDivMod (d := d) M).symm (i.2, q) +ᵥ
    orbitRep (d := d) i.1

/-- The finite coordinate cube underlying a block. -/
def blockPoints (M : ℕ) [NeZero M]
    (i : BlockIndex (d := d) (X := X)) : Finset X := by
  classical
  exact Finset.univ.image (blockPoint (d := d) M i)

/-- The block containing a point. -/
def blockOf (M : ℕ) [NeZero M] (x : X) : BlockIndex (d := d) (X := X) :=
  (orbitClass (d := d) x,
    ((latticeDivMod (d := d) M) (orbitCoord (d := d) x)).1)

/-- The remainder coordinate of a point inside its block. -/
def blockOffset (M : ℕ) [NeZero M] (x : X) : Fin d → Fin M :=
  ((latticeDivMod (d := d) M) (orbitCoord (d := d) x)).2

lemma orbitCoord_blockPoint (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M] (i : BlockIndex (d := d) (X := X))
    (q : Fin d → Fin M) :
    orbitCoord (d := d) (blockPoint (d := d) M i q) =
      (latticeDivMod (d := d) M).symm (i.2, q) := by
  rw [blockPoint, orbitCoord_vadd (d := d) hfree,
    orbitCoord_orbitRep_eq_zero (d := d) hfree, add_zero]

@[simp]
lemma orbitClass_blockPoint (M : ℕ) [NeZero M]
    (i : BlockIndex (d := d) (X := X)) (q : Fin d → Fin M) :
    orbitClass (d := d) (blockPoint (d := d) M i q) = i.1 := by
  simp [blockPoint, orbitClass_vadd (d := d)]

@[simp]
lemma blockOf_blockPoint (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M] (i : BlockIndex (d := d) (X := X))
    (q : Fin d → Fin M) :
    blockOf (d := d) M (blockPoint (d := d) M i q) = i := by
  apply Prod.ext
  · exact orbitClass_blockPoint (d := d) M i q
  · rw [blockOf, orbitCoord_blockPoint (d := d) hfree]
    simp

lemma blockPoint_blockOf_offset
    (M : ℕ) [NeZero M] (x : X) :
    blockPoint (d := d) M (blockOf (d := d) M x)
      (blockOffset (d := d) M x) = x := by
  rw [blockPoint, blockOf, blockOffset]
  have hdm := (latticeDivMod (d := d) M).symm_apply_apply
    (orbitCoord (d := d) x)
  change (latticeDivMod (d := d) M).symm
      (((latticeDivMod (d := d) M) (orbitCoord (d := d) x)).1,
        ((latticeDivMod (d := d) M) (orbitCoord (d := d) x)).2) +ᵥ
      orbitRep (d := d) (orbitClass (d := d) x) = x
  rw [show (((latticeDivMod (d := d) M) (orbitCoord (d := d) x)).1,
        ((latticeDivMod (d := d) M) (orbitCoord (d := d) x)).2) =
      (latticeDivMod (d := d) M) (orbitCoord (d := d) x) from rfl,
    hdm, orbitCoord_vadd_orbitRep]

lemma blockPoint_injective (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M] (i : BlockIndex (d := d) (X := X)) :
    Function.Injective (blockPoint (d := d) M i) := by
  intro q r hqr
  have hc := congrArg (orbitCoord (d := d)) hqr
  rw [orbitCoord_blockPoint (d := d) hfree,
    orbitCoord_blockPoint (d := d) hfree] at hc
  exact congrArg Prod.snd ((latticeDivMod (d := d) M).symm.injective hc)

lemma mem_blockPoints_iff (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M] (i : BlockIndex (d := d) (X := X)) (x : X) :
    x ∈ blockPoints (d := d) M i ↔ blockOf (d := d) M x = i := by
  classical
  rw [blockPoints, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact blockOf_blockPoint (d := d) hfree M i q
  · intro hx
    refine ⟨blockOffset (d := d) M x, Finset.mem_univ _, ?_⟩
    rw [← hx]
    exact blockPoint_blockOf_offset (d := d) M x

lemma card_blockPoints (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M] (i : BlockIndex (d := d) (X := X)) :
    (blockPoints (d := d) M i).card = M ^ d := by
  classical
  rw [blockPoints, Finset.card_image_of_injective _
    (blockPoint_injective (d := d) hfree M i), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- The elements of a set which lie in one canonical orbit block. -/
def pointsInBlock (E : Set X) (M : ℕ) [NeZero M]
    (i : BlockIndex (d := d) (X := X)) : Finset E := by
  classical
  exact (blockPoints (d := d) M i).subtype (fun x ↦ x ∈ E)

lemma mem_pointsInBlock (hfree : FreeAction (d := d) (X := X))
    (E : Set X) (M : ℕ) [NeZero M]
    (i : BlockIndex (d := d) (X := X)) (x : E) :
    x ∈ pointsInBlock (d := d) E M i ↔ blockOf (d := d) M (x : X) = i := by
  classical
  rw [pointsInBlock, Finset.mem_subtype]
  exact mem_blockPoints_iff (d := d) hfree M i x

/-- The canonical finite-block data used by the block Hall theorem. -/
def pointBlockData (hfree : FreeAction (d := d) (X := X))
    (A B : Set X) (M : ℕ) [NeZero M] :
    BlockMatching.PointBlockData A B (BlockIndex (d := d) (X := X)) where
  blockA a := blockOf (d := d) M a
  blockB b := blockOf (d := d) M b
  pointsA i := pointsInBlock (d := d) A M i
  pointsB i := pointsInBlock (d := d) B M i
  mem_pointsA i a := mem_pointsInBlock (d := d) hfree A M i a
  mem_pointsB i b := mem_pointsInBlock (d := d) hfree B M i b

end LatticeBlocks

section FinitePartitions

variable {X I : Type*}

/-- A finite partition, presented by its block map and complete finite fibers. -/
structure FiniteBlockPartition (X I : Type*) where
  block : X → I
  points : I → Finset X
  mem_points : ∀ (i : I) (x : X), x ∈ points i ↔ block x = i

/-- The canonical lattice cubes form a finite partition. -/
def orbitBlockPartition {d : ℕ} [AddAction (Lattice d) X]
    (hfree : FreeAction (d := d) (X := X)) (M : ℕ) [NeZero M] :
    FiniteBlockPartition X (BlockIndex (d := d) (X := X)) where
  block := blockOf (d := d) M
  points := blockPoints (d := d) M
  mem_points := mem_blockPoints_iff (d := d) hfree M

namespace FiniteBlockPartition

variable (P : FiniteBlockPartition X I)

lemma pairwiseDisjoint_points [DecidableEq I] (s : Finset I) :
    (↑s : Set I).PairwiseDisjoint P.points := by
  classical
  intro i hi j hj hij
  change Disjoint (P.points i) (P.points j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  exact hij ((P.mem_points i x).mp hxi |>.symm.trans
    ((P.mem_points j x).mp hxj))

end FiniteBlockPartition

end FinitePartitions

section Aggregation

variable {X I ι : Type*} [Fintype ι]

/-- Blocks reached by one directed edge starting in a given block. -/
def outgoingBlocks (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (i : I) : Finset I := by
  classical
  exact (P.points i).biUnion fun x ↦
    Finset.univ.image fun g ↦ P.block (move g x)

/-- Blocks from which one directed edge can enter a given block. -/
def incomingBlocks (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (i : I) : Finset I := by
  classical
  exact (P.points i).biUnion fun x ↦
    Finset.univ.image fun g ↦ P.block ((move g).symm x)

/-- The undirected block graph induced by finitely many edge permutations.
Loops are erased because they contribute zero to the antisymmetric block
flow. -/
def adjacentBlocks (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (i : I) : Finset I := by
  classical
  exact (outgoingBlocks P move i ∪ incomingBlocks P move i).erase i

lemma mem_outgoingBlocks_iff [DecidableEq I]
    {P : FiniteBlockPartition X I} {move : ι → Equiv.Perm X} {i j : I} :
    j ∈ outgoingBlocks P move i ↔
      ∃ x ∈ P.points i, ∃ g : ι, P.block (move g x) = j := by
  classical
  simp [outgoingBlocks]

lemma mem_incomingBlocks_iff [DecidableEq I]
    {P : FiniteBlockPartition X I} {move : ι → Equiv.Perm X} {i j : I} :
    j ∈ incomingBlocks P move i ↔
      ∃ x ∈ P.points i, ∃ g : ι, P.block ((move g).symm x) = j := by
  classical
  simp [incomingBlocks]

lemma mem_adjacentBlocks_iff [DecidableEq I]
    {P : FiniteBlockPartition X I} {move : ι → Equiv.Perm X} {i j : I} :
    j ∈ adjacentBlocks P move i ↔
      j ≠ i ∧
        ((∃ x ∈ P.points i, ∃ g : ι, P.block (move g x) = j) ∨
          ∃ x ∈ P.points i, ∃ g : ι, P.block ((move g).symm x) = j) := by
  classical
  simp only [adjacentBlocks, Finset.mem_erase, Finset.mem_union,
    mem_outgoingBlocks_iff, mem_incomingBlocks_iff]

lemma adjacentBlocks_symm [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    {i j : I} (hji : j ∈ adjacentBlocks P move i) :
    i ∈ adjacentBlocks P move j := by
  classical
  rw [mem_adjacentBlocks_iff] at hji ⊢
  refine ⟨hji.1.symm, ?_⟩
  rcases hji.2 with hout | hin
  · rcases hout with ⟨x, hxi, g, hg⟩
    right
    refine ⟨move g x, ?_, g, ?_⟩
    · exact (P.mem_points j (move g x)).mpr hg
    · simpa using (P.mem_points i x).mp hxi
  · rcases hin with ⟨x, hxi, g, hg⟩
    left
    refine ⟨(move g).symm x, ?_, g, ?_⟩
    · exact (P.mem_points j ((move g).symm x)).mpr hg
    · simpa using (P.mem_points i x).mp hxi

lemma card_outgoingBlocks_le (P : FiniteBlockPartition X I)
    (move : ι → Equiv.Perm X) (i : I) :
    (outgoingBlocks P move i).card ≤ (P.points i).card * Fintype.card ι := by
  classical
  calc
    (outgoingBlocks P move i).card ≤
        ∑ x ∈ P.points i,
          (Finset.univ.image fun g : ι ↦ P.block (move g x)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ P.points i, (Finset.univ : Finset ι).card := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.card_image_le
    _ = (P.points i).card * Fintype.card ι := by simp

lemma card_incomingBlocks_le (P : FiniteBlockPartition X I)
    (move : ι → Equiv.Perm X) (i : I) :
    (incomingBlocks P move i).card ≤ (P.points i).card * Fintype.card ι := by
  classical
  calc
    (incomingBlocks P move i).card ≤
        ∑ x ∈ P.points i,
          (Finset.univ.image fun g : ι ↦ P.block ((move g).symm x)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ P.points i, (Finset.univ : Finset ι).card := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.card_image_le
    _ = (P.points i).card * Fintype.card ι := by simp

lemma card_adjacentBlocks_le (P : FiniteBlockPartition X I)
    (move : ι → Equiv.Perm X) (K : ℕ)
    (hcard : ∀ i, (P.points i).card ≤ K) (i : I) :
    (adjacentBlocks P move i).card ≤ 2 * K * Fintype.card ι := by
  classical
  calc
    (adjacentBlocks P move i).card ≤
        (outgoingBlocks P move i ∪ incomingBlocks P move i).card :=
      Finset.card_erase_le
    _ ≤ (outgoingBlocks P move i).card + (incomingBlocks P move i).card :=
      Finset.card_union_le _ _
    _ ≤ (P.points i).card * Fintype.card ι +
        (P.points i).card * Fintype.card ι :=
      Nat.add_le_add (card_outgoingBlocks_le P move i)
        (card_incomingBlocks_le P move i)
    _ ≤ K * Fintype.card ι + K * Fintype.card ι := by
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (hcard i))
        (Nat.mul_le_mul_right _ (hcard i))
    _ = 2 * K * Fintype.card ι := by
      rw [two_mul, add_mul]

/-- Total directed flow carried by edges from block `i` to block `j`. -/
def rawBlockFlow [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (φ : X → ι → ℤ) (i j : I) : ℤ :=
  ∑ x ∈ P.points i, ∑ g : ι,
    if P.block (move g x) = j then φ x g else 0

/-- The same edges, indexed by their endpoint in `i`. -/
def incomingRawBlockFlow [DecidableEq I]
    (P : FiniteBlockPartition X I)
    (move : ι → Equiv.Perm X) (φ : X → ι → ℤ) (i j : I) : ℤ :=
  ∑ x ∈ P.points i, ∑ g : ι,
    if P.block ((move g).symm x) = j then φ ((move g).symm x) g else 0

/-- Net outgoing flow between two blocks. -/
def netBlockFlow [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (φ : X → ι → ℤ) (i j : I) : ℤ :=
  rawBlockFlow P move φ i j - rawBlockFlow P move φ j i

lemma netBlockFlow_antisymm [DecidableEq I] (P : FiniteBlockPartition X I)
    (move : ι → Equiv.Perm X) (φ : X → ι → ℤ) (i j : I) :
    netBlockFlow P move φ i j + netBlockFlow P move φ j i = 0 := by
  simp only [netBlockFlow]
  ring

/-- A uniform point-edge bound gives a uniform (coarse) raw block-flow
bound.  Geometry can improve this volume bound to a boundary-area bound for
canonical cubes, but this estimate is useful independently of that step. -/
lemma abs_rawBlockFlow_le [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (φ : X → ι → ℤ) (K b : ℕ)
    (hcard : ∀ i, (P.points i).card ≤ K)
    (hbound : ∀ x g, |φ x g| ≤ (b : ℤ)) (i j : I) :
    |rawBlockFlow P move φ i j| ≤ (K * Fintype.card ι * b : ℕ) := by
  classical
  rw [rawBlockFlow]
  calc
    |∑ x ∈ P.points i, ∑ g : ι,
        if P.block (move g x) = j then φ x g else 0| ≤
        ∑ x ∈ P.points i,
          |∑ g : ι, if P.block (move g x) = j then φ x g else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ P.points i, ∑ g : ι,
        |if P.block (move g x) = j then φ x g else 0| := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ P.points i, ∑ _g : ι, (b : ℤ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro g hg
      split_ifs
      · exact hbound x g
      · simp
    _ = ((P.points i).card * Fintype.card ι * b : ℕ) := by
      simp
      ring
    _ ≤ (K * Fintype.card ι * b : ℕ) := by
      exact_mod_cast Nat.mul_le_mul_right b
        (Nat.mul_le_mul_right (Fintype.card ι) (hcard i))

/-- The corresponding net block flow is bounded by twice the raw bound. -/
lemma netBlockFlow_le_of_bound [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (φ : X → ι → ℤ) (K b : ℕ)
    (hcard : ∀ i, (P.points i).card ≤ K)
    (hbound : ∀ x g, |φ x g| ≤ (b : ℤ)) (i j : I) :
    netBlockFlow P move φ i j ≤ 2 * K * Fintype.card ι * b := by
  have hi := abs_rawBlockFlow_le P move φ K b hcard hbound i j
  have hj := abs_rawBlockFlow_le P move φ K b hcard hbound j i
  rw [netBlockFlow]
  have hsub : rawBlockFlow P move φ i j - rawBlockFlow P move φ j i ≤
      |rawBlockFlow P move φ i j| + |rawBlockFlow P move φ j i| := by
    linarith [le_abs_self (rawBlockFlow P move φ i j),
      neg_le_abs (rawBlockFlow P move φ j i)]
  calc
    rawBlockFlow P move φ i j - rawBlockFlow P move φ j i ≤
        |rawBlockFlow P move φ i j| + |rawBlockFlow P move φ j i| := hsub
    _ ≤ (K * Fintype.card ι * b : ℕ) +
        (K * Fintype.card ι * b : ℕ) := add_le_add hi hj
    _ = (2 * K * Fintype.card ι * b : ℕ) := by
      push_cast
      ring

private lemma sum_move_filter_eq [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (φ : X → ι → ℤ) (i j : I) (g : ι) :
    (∑ x ∈ P.points j,
        if P.block (move g x) = i then φ x g else 0) =
      ∑ y ∈ P.points i,
        if P.block ((move g).symm y) = j
          then φ ((move g).symm y) g else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij'
      (fun x _ ↦ move g x) (fun y _ ↦ (move g).symm y)
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    refine ⟨(P.mem_points i (move g x)).mpr hx.2, ?_⟩
    simpa using (P.mem_points j x).mp hx.1
  · intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    refine ⟨(P.mem_points j ((move g).symm y)).mpr hy.2, ?_⟩
    simpa using (P.mem_points i y).mp hy.1
  · intro x hx
    exact (move g).symm_apply_apply x
  · intro y hy
    exact (move g).apply_symm_apply y
  · intro x hx
    simp

lemma rawBlockFlow_eq_incoming [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (φ : X → ι → ℤ) (i j : I) :
    rawBlockFlow P move φ j i = incomingRawBlockFlow P move φ i j := by
  classical
  rw [rawBlockFlow, incomingRawBlockFlow]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  convert sum_move_filter_eq P move φ i j g using 1

/-- Incoming-minus-outgoing point divergence. -/
def pointDivergence (move : ι → Equiv.Perm X) (φ : X → ι → ℤ)
    (x : X) : ℤ :=
  ∑ g : ι, (φ ((move g).symm x) g - φ x g)

private lemma sum_adjacent_ite_out [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (i : I) (x : X) (hx : x ∈ P.points i) (g : ι) (z : ℤ) :
    (∑ j ∈ adjacentBlocks P move i,
      if P.block (move g x) = j then z else 0) =
      z - if P.block (move g x) = i then z else 0 := by
  classical
  by_cases hsame : P.block (move g x) = i
  · have hnot : i ∉ adjacentBlocks P move i := by simp [adjacentBlocks]
    simp [hsame, hnot]
  · have hmem : P.block (move g x) ∈ adjacentBlocks P move i := by
      rw [mem_adjacentBlocks_iff]
      exact ⟨hsame, Or.inl ⟨x, hx, g, rfl⟩⟩
    simp [hsame, hmem]

private lemma sum_adjacent_ite_in [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (i : I) (x : X) (hx : x ∈ P.points i) (g : ι) (z : ℤ) :
    (∑ j ∈ adjacentBlocks P move i,
      if P.block ((move g).symm x) = j then z else 0) =
      z - if P.block ((move g).symm x) = i then z else 0 := by
  classical
  by_cases hsame : P.block ((move g).symm x) = i
  · have hnot : i ∉ adjacentBlocks P move i := by simp [adjacentBlocks]
    simp [hsame, hnot]
  · have hmem : P.block ((move g).symm x) ∈ adjacentBlocks P move i := by
      rw [mem_adjacentBlocks_iff]
      exact ⟨hsame, Or.inr ⟨x, hx, g, rfl⟩⟩
    simp [hsame, hmem]

lemma sum_rawBlockFlow_adjacent [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (φ : X → ι → ℤ) (i : I) :
    (∑ j ∈ adjacentBlocks P move i, rawBlockFlow P move φ i j) =
      (∑ x ∈ P.points i, ∑ g : ι, φ x g) - rawBlockFlow P move φ i i := by
  classical
  simp only [rawBlockFlow]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := adjacentBlocks P move i)]
  rw [Finset.sum_comm]
  calc
    (∑ g : ι, ∑ x ∈ P.points i, ∑ j ∈ adjacentBlocks P move i,
        if P.block (move g x) = j then φ x g else 0) =
        ∑ g : ι, ∑ x ∈ P.points i,
          (φ x g - if P.block (move g x) = i then φ x g else 0) := by
      apply Finset.sum_congr rfl
      intro g hg
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_adjacent_ite_out P move i x hx g (φ x g)
    _ = (∑ x ∈ P.points i, ∑ g : ι, φ x g) -
        ∑ x ∈ P.points i, ∑ g : ι,
          if P.block (move g x) = i then φ x g else 0 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_sub_distrib]

lemma sum_incomingRawBlockFlow_adjacent [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (φ : X → ι → ℤ) (i : I) :
    (∑ j ∈ adjacentBlocks P move i, incomingRawBlockFlow P move φ i j) =
      (∑ x ∈ P.points i, ∑ g : ι, φ ((move g).symm x) g) -
        incomingRawBlockFlow P move φ i i := by
  classical
  simp only [incomingRawBlockFlow]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := adjacentBlocks P move i)]
  rw [Finset.sum_comm]
  calc
    (∑ g : ι, ∑ x ∈ P.points i, ∑ j ∈ adjacentBlocks P move i,
        if P.block ((move g).symm x) = j
          then φ ((move g).symm x) g else 0) =
        ∑ g : ι, ∑ x ∈ P.points i,
          (φ ((move g).symm x) g -
            if P.block ((move g).symm x) = i
              then φ ((move g).symm x) g else 0) := by
      apply Finset.sum_congr rfl
      intro g hg
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_adjacent_ite_in P move i x hx g (φ ((move g).symm x) g)
    _ = (∑ x ∈ P.points i, ∑ g : ι, φ ((move g).symm x) g) -
        ∑ x ∈ P.points i, ∑ g : ι,
          if P.block ((move g).symm x) = i
            then φ ((move g).symm x) g else 0 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_sub_distrib]

lemma sum_netBlockFlow_adjacent [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (φ : X → ι → ℤ) (i : I) :
    (∑ j ∈ adjacentBlocks P move i, netBlockFlow P move φ i j) =
      -∑ x ∈ P.points i, pointDivergence move φ x := by
  classical
  simp only [netBlockFlow, Finset.sum_sub_distrib]
  simp_rw [rawBlockFlow_eq_incoming P move φ i]
  rw [sum_rawBlockFlow_adjacent, sum_incomingRawBlockFlow_adjacent]
  have hloop : rawBlockFlow P move φ i i =
      incomingRawBlockFlow P move φ i i :=
    rawBlockFlow_eq_incoming P move φ i i
  rw [hloop]
  simp only [pointDivergence, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

/-- Restrict a finite partition fiber to a subset. -/
def partitionPointsIn (P : FiniteBlockPartition X I) (E : Set X)
    (i : I) : Finset E := by
  classical
  exact (P.points i).subtype (fun x ↦ x ∈ E)

lemma mem_partitionPointsIn
    (P : FiniteBlockPartition X I) (E : Set X) (i : I) (x : E) :
    x ∈ partitionPointsIn P E i ↔ P.block (x : X) = i := by
  classical
  rw [partitionPointsIn, Finset.mem_subtype]
  exact P.mem_points i x

/-- Every finite partition supplies the data format used by `BlockMatching`. -/
def partitionPointBlockData (P : FiniteBlockPartition X I)
    (A B : Set X) : BlockMatching.PointBlockData A B I where
  blockA a := P.block a
  blockB b := P.block b
  pointsA i := partitionPointsIn P A i
  pointsB i := partitionPointsIn P B i
  mem_pointsA i a := mem_partitionPointsIn P A i a
  mem_pointsB i b := mem_partitionPointsIn P B i b

/-- The integer indicator of a set. -/
def intIndicator (E : Set X) (x : X) : ℤ := by
  classical
  exact if x ∈ E then 1 else 0

lemma sum_intIndicator_eq_card (P : FiniteBlockPartition X I)
    (E : Set X) (i : I) :
    ∑ x ∈ P.points i, intIndicator E x =
      ((partitionPointsIn P E i).card : ℤ) := by
  classical
  rw [partitionPointsIn, Finset.card_subtype, Finset.card_filter]
  simp only [intIndicator]
  push_cast
  rfl

/-- The aggregation constructor with a user-supplied uniform degree bound.
For canonical lattice blocks one normally proves the sharper `3^d - 1`
bound, instead of using the coarse finite-partition estimate below. -/
def boundedBlockFlowOfPointFlowWithDegree [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (A B : Set X) (degree capacity : ℕ) (φ : X → ι → ℤ)
    (hdegree : ∀ i, (adjacentBlocks P move i).card ≤ degree)
    (hcapacity : ∀ i j, netBlockFlow P move φ i j ≤ capacity)
    (hdiv : ∀ x, pointDivergence move φ x =
      intIndicator B x - intIndicator A x) :
    BlockMatching.BoundedBlockFlow
      (fun i ↦ ((partitionPointBlockData P A B).pointsA i).card)
      (fun i ↦ ((partitionPointBlockData P A B).pointsB i).card) where
  neighbors := adjacentBlocks P move
  degree := degree
  capacity := capacity
  flow := netBlockFlow P move φ
  neighbors_symm := adjacentBlocks_symm P move
  degree_le := hdegree
  antisymm := netBlockFlow_antisymm P move φ
  flow_le := hcapacity
  divergence_eq := by
    intro i
    rw [sum_netBlockFlow_adjacent]
    simp_rw [hdiv]
    rw [Finset.sum_sub_distrib, sum_intIndicator_eq_card,
      sum_intIndicator_eq_card]
    change ((partitionPointsIn P A i).card : ℤ) -
        ((partitionPointsIn P B i).card : ℤ) =
      -(((partitionPointsIn P B i).card : ℤ) -
        ((partitionPointsIn P A i).card : ℤ))
    ring

/-- Aggregate a bounded integer point flow into the exact antisymmetric block
flow required by the Hall argument.  The capacity hypothesis is stated on the
actual net cut flow; separate geometric counting estimates can therefore be
plugged in without changing this algebraic bridge. -/
def boundedBlockFlowOfPointFlow [DecidableEq I]
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (A B : Set X) (K capacity : ℕ) (φ : X → ι → ℤ)
    (hcard : ∀ i, (P.points i).card ≤ K)
    (hcapacity : ∀ i j, netBlockFlow P move φ i j ≤ capacity)
    (hdiv : ∀ x, pointDivergence move φ x =
      intIndicator B x - intIndicator A x) :
    BlockMatching.BoundedBlockFlow
      (fun i ↦ ((partitionPointBlockData P A B).pointsA i).card)
      (fun i ↦ ((partitionPointBlockData P A B).pointsB i).card) :=
  boundedBlockFlowOfPointFlowWithDegree P move A B
    (2 * K * Fintype.card ι) capacity φ
    (card_adjacentBlocks_le P move K hcard) hcapacity hdiv

section Equidecomposition

variable [AddGroup X] [DecidableEq I]

/-- Point-flow-to-matching in one theorem.  The two room estimates are the
positive-density input; `hallowed` records the finite displacement set for
points in equal or adjacent blocks. -/
theorem exists_equidecomp_of_pointFlow
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (A B : Set X) (D : Finset X) (K capacity : ℕ) (φ : X → ι → ℤ)
    (hcard : ∀ i, (P.points i).card ≤ K)
    (hcapacity : ∀ i j, netBlockFlow P move φ i j ≤ capacity)
    (hdiv : ∀ x, pointDivergence move φ x =
      intIndicator B x - intIndicator A x)
    (hroomA : ∀ i,
      (2 * K * Fintype.card ι) * capacity ≤
        ((partitionPointBlockData P A B).pointsA i).card)
    (hroomB : ∀ i,
      (2 * K * Fintype.card ι) * capacity ≤
        ((partitionPointBlockData P A B).pointsB i).card)
    (hallowed : ∀ (a : A) (b : B),
      (partitionPointBlockData P A B).blockB b =
          (partitionPointBlockData P A B).blockA a ∨
        (partitionPointBlockData P A B).blockB b ∈
          adjacentBlocks P move ((partitionPointBlockData P A B).blockA a) →
      (b : X) - (a : X) ∈ D) :
    ∃ e : Equidecomp X (Multiplicative X),
      e.source = A ∧ e.target = B ∧
        Equidecomp.IsDecompOn e A (multiplicativeDisplacements D) := by
  let F := boundedBlockFlowOfPointFlow P move A B K capacity φ
    hcard hcapacity hdiv
  exact BlockMatching.exists_equidecomp_of_boundedBlockFlow
    (partitionPointBlockData P A B) F hroomA hroomB hallowed

/-- A sharper version in which the geometry supplies the uniform degree
bound for the block graph. -/
theorem exists_equidecomp_of_pointFlowWithDegree
    (P : FiniteBlockPartition X I) (move : ι → Equiv.Perm X)
    (A B : Set X) (D : Finset X) (degree capacity : ℕ) (φ : X → ι → ℤ)
    (hdegree : ∀ i, (adjacentBlocks P move i).card ≤ degree)
    (hcapacity : ∀ i j, netBlockFlow P move φ i j ≤ capacity)
    (hdiv : ∀ x, pointDivergence move φ x =
      intIndicator B x - intIndicator A x)
    (hroomA : ∀ i, degree * capacity ≤
      ((partitionPointBlockData P A B).pointsA i).card)
    (hroomB : ∀ i, degree * capacity ≤
      ((partitionPointBlockData P A B).pointsB i).card)
    (hallowed : ∀ (a : A) (b : B),
      (partitionPointBlockData P A B).blockB b =
          (partitionPointBlockData P A B).blockA a ∨
        (partitionPointBlockData P A B).blockB b ∈
          adjacentBlocks P move ((partitionPointBlockData P A B).blockA a) →
      (b : X) - (a : X) ∈ D) :
    ∃ e : Equidecomp X (Multiplicative X),
      e.source = A ∧ e.target = B ∧
        Equidecomp.IsDecompOn e A (multiplicativeDisplacements D) := by
  let F := boundedBlockFlowOfPointFlowWithDegree P move A B degree capacity φ
    hdegree hcapacity hdiv
  exact BlockMatching.exists_equidecomp_of_boundedBlockFlow
    (partitionPointBlockData P A B) F hroomA hroomB hallowed

end Equidecomposition

section LatticeMoves

variable {d : ℕ} [AddAction (Lattice d) X]

/-- Translation by a lattice vector, as a permutation of the acted-on type. -/
def latticeMove (n : Lattice d) : Equiv.Perm X where
  toFun x := n +ᵥ x
  invFun x := -n +ᵥ x
  left_inv x := by simp only [← add_vadd, neg_add_cancel, zero_vadd]
  right_inv x := by simp only [← add_vadd, add_neg_cancel, zero_vadd]

/-- The diagonal bit moves occurring in the dyadic flow construction. -/
def bitMoves : Flow.BitDirection d → Equiv.Perm X :=
  fun g ↦ latticeMove (d := d) (Flow.bitVector g)

@[simp]
lemma bitMoves_apply (g : Flow.BitDirection d) (x : X) :
    bitMoves (d := d) g x = Flow.bitVector g +ᵥ x := rfl

@[simp]
lemma bitMoves_symm_apply (g : Flow.BitDirection d) (x : X) :
    (bitMoves (d := d) g).symm x = -Flow.bitVector g +ᵥ x := rfl

/-- Integer directional flows have the same shape as the real dyadic flow,
without imposing the field hypothesis of the analytic API. -/
abbrev IntegerDirectionalFlow := Flow.BitDirection d → X → ℤ

/-- Incoming-minus-outgoing divergence for an integer bit-direction flow. -/
def bitDivergence (φ : IntegerDirectionalFlow (d := d) (X := X)) (x : X) : ℤ :=
  ∑ g : Flow.BitDirection d,
    (φ g (-Flow.bitVector g +ᵥ x) - φ g x)

lemma pointDivergence_bitMoves
    (φ : IntegerDirectionalFlow (d := d) (X := X)) (x : X) :
    pointDivergence (bitMoves (d := d)) (fun x g ↦ φ g x) x =
      bitDivergence (d := d) φ x := by
  rfl

/-- The canonical block graph for the diagonal bit moves. -/
def orbitAdjacentBlocks (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M] (i : BlockIndex (d := d) (X := X)) :
    Finset (BlockIndex (d := d) (X := X)) :=
  adjacentBlocks (orbitBlockPartition hfree M) (bitMoves (d := d)) i

/-- Net block flow obtained by aggregating an integer bit-direction flow. -/
def orbitNetBlockFlow (hfree : FreeAction (d := d) (X := X))
    (M : ℕ) [NeZero M] (φ : IntegerDirectionalFlow (d := d) (X := X))
    (i j : BlockIndex (d := d) (X := X)) : ℤ := by
  classical
  exact netBlockFlow (orbitBlockPartition hfree M) (bitMoves (d := d))
    (fun x g ↦ φ g x) i j

lemma partitionPointBlockData_orbitBlockPartition
    (hfree : FreeAction (d := d) (X := X))
    (A B : Set X) (M : ℕ) [NeZero M] :
    partitionPointBlockData (orbitBlockPartition hfree M) A B =
      pointBlockData hfree A B M := by
  rfl

section OrbitEquidecomposition

variable [AddGroup X]

/-- End-to-end canonical-orbit specialization of
`exists_equidecomp_of_pointFlowWithDegree`.  Analytic/integral rounding
provides `φ`; geometric block counting provides the degree, capacity, room,
and finite-displacement hypotheses. -/
theorem exists_equidecomp_of_orbitBitFlow
    (hfree : FreeAction (d := d) (X := X))
    (A B : Set X) (D : Finset X) (M : ℕ) [NeZero M]
    (degree capacity : ℕ)
    (φ : IntegerDirectionalFlow (d := d) (X := X))
    (hdegree : ∀ i, (orbitAdjacentBlocks hfree M i).card ≤ degree)
    (hcapacity : ∀ i j, orbitNetBlockFlow hfree M φ i j ≤ capacity)
    (hdiv : ∀ x, bitDivergence (d := d) φ x =
      intIndicator B x - intIndicator A x)
    (hroomA : ∀ i, degree * capacity ≤
      (pointsInBlock (d := d) A M i).card)
    (hroomB : ∀ i, degree * capacity ≤
      (pointsInBlock (d := d) B M i).card)
    (hallowed : ∀ (a : A) (b : B),
      blockOf (d := d) M (b : X) = blockOf (d := d) M (a : X) ∨
        blockOf (d := d) M (b : X) ∈
          orbitAdjacentBlocks hfree M (blockOf (d := d) M (a : X)) →
      (b : X) - (a : X) ∈ D) :
    ∃ e : Equidecomp X (Multiplicative X),
      e.source = A ∧ e.target = B ∧
        Equidecomp.IsDecompOn e A (multiplicativeDisplacements D) := by
  classical
  let P := orbitBlockPartition hfree M
  apply exists_equidecomp_of_pointFlowWithDegree P (bitMoves (d := d))
    A B D degree capacity (fun x g ↦ φ g x)
  · simpa only [P, orbitAdjacentBlocks] using hdegree
  · simpa only [P, orbitNetBlockFlow] using hcapacity
  · intro x
    rw [pointDivergence_bitMoves]
    exact hdiv x
  · simpa only [P, partitionPointBlockData_orbitBlockPartition,
      pointBlockData] using hroomA
  · simpa only [P, partitionPointBlockData_orbitBlockPartition,
      pointBlockData] using hroomB
  · intro a b hab
    apply hallowed a b
    simpa only [P, partitionPointBlockData_orbitBlockPartition,
      pointBlockData, orbitAdjacentBlocks] using hab

end OrbitEquidecomposition

end LatticeMoves

end Aggregation

end

end Erdos1124.OrbitBlocks
