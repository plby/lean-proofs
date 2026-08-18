/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.Hall

/-!
# Matching finite blocks along a bounded graph

This file contains the last, combinatorial, step in the bounded-flow proof of
circle squaring.  Points are partitioned into finite blocks.  If every finite
family of blocks contains no more `A`-points than there are `B`-points in the
same or adjacent blocks (and conversely), then the point-level finite Hall
conditions hold.  Consequently there is a translation equidecomposition whose
displacements belong to one prescribed finite set.

The second half of the file records the numerical estimate used to obtain the
block inequalities from a bounded integral flow: a cut can transport at most
`capacity * degree` units into each new boundary block, while the positive
density estimate supplies at least that many points in every block.
-/

open Function Set

namespace Erdos1124.BlockMatching

section PointBlocks

variable {X I : Type*} [AddGroup X]

/-- The closed neighborhood of a finite set of block indices. -/
noncomputable def closedBlockNeighborhood (neighbors : I → Finset I)
    (s : Finset I) : Finset I := by
  classical
  exact s ∪ s.biUnion neighbors

@[simp]
lemma mem_closedBlockNeighborhood [DecidableEq I] {neighbors : I → Finset I}
    {s : Finset I} {j : I} :
    j ∈ closedBlockNeighborhood neighbors s ↔
      j ∈ s ∨ ∃ i ∈ s, j ∈ neighbors i := by
  classical
  simp [closedBlockNeighborhood]

/-- Finite enumerations of the intersections of `A` and `B` with every
block.  The two membership equivalences say both that no point is omitted and
that an enumerated point occurs in exactly its assigned block. -/
structure PointBlockData (A B : Set X) (I : Type*) where
  blockA : A → I
  blockB : B → I
  pointsA : I → Finset A
  pointsB : I → Finset B
  mem_pointsA : ∀ (i : I) (a : A), a ∈ pointsA i ↔ blockA a = i
  mem_pointsB : ∀ (i : I) (b : B), b ∈ pointsB i ↔ blockB b = i

namespace PointBlockData

variable {A B : Set X} (P : PointBlockData A B I)

/-- The `A`-points in a finite family of blocks. -/
noncomputable def pointsAUnion (s : Finset I) : Finset A := by
  classical
  exact s.biUnion P.pointsA

/-- The `B`-points in a finite family of blocks. -/
noncomputable def pointsBUnion (s : Finset I) : Finset B := by
  classical
  exact s.biUnion P.pointsB

lemma pairwiseDisjoint_pointsA [DecidableEq I] (s : Finset I) :
    (↑s : Set I).PairwiseDisjoint P.pointsA := by
  classical
  intro i hi j hj hij
  change Disjoint (P.pointsA i) (P.pointsA j)
  rw [Finset.disjoint_left]
  intro a hai haj
  have hia : P.blockA a = i := (P.mem_pointsA i a).mp hai
  have hja : P.blockA a = j := (P.mem_pointsA j a).mp haj
  exact hij (hia.symm.trans hja)

lemma pairwiseDisjoint_pointsB [DecidableEq I] (s : Finset I) :
    (↑s : Set I).PairwiseDisjoint P.pointsB := by
  classical
  intro i hi j hj hij
  change Disjoint (P.pointsB i) (P.pointsB j)
  rw [Finset.disjoint_left]
  intro b hbi hbj
  have hib : P.blockB b = i := (P.mem_pointsB i b).mp hbi
  have hjb : P.blockB b = j := (P.mem_pointsB j b).mp hbj
  exact hij (hib.symm.trans hjb)

lemma card_biUnion_pointsA [DecidableEq I] (s : Finset I) :
    (P.pointsAUnion s).card = ∑ i ∈ s, (P.pointsA i).card :=
  by
    classical
    rw [pointsAUnion]
    exact Finset.card_biUnion (P.pairwiseDisjoint_pointsA s)

lemma card_biUnion_pointsB [DecidableEq I] (s : Finset I) :
    (P.pointsBUnion s).card = ∑ i ∈ s, (P.pointsB i).card :=
  by
    classical
    rw [pointsBUnion]
    exact Finset.card_biUnion (P.pairwiseDisjoint_pointsB s)

end PointBlockData

/-- Lift two block-level Hall inequalities to the exact point-level finite
Hall conditions used by `Erdos1124.exists_equidecomp_of_hall`.

The compatibility hypothesis is deliberately stated using the actual
displacement finset.  It is therefore equally useful for abstract block
partitions and for the standard `n`-cube tiling of every free `ℤ^d` orbit. -/
theorem finiteDisplacementHall_of_blockHall [DecidableEq I]
    {A B : Set X} {D : Finset X} {neighbors : I → Finset I}
    (P : PointBlockData A B I)
    (hforward : ∀ t : Finset I,
      (P.pointsAUnion t).card ≤
        (P.pointsBUnion (closedBlockNeighborhood neighbors t)).card)
    (hbackward : ∀ t : Finset I,
      (P.pointsBUnion t).card ≤
        (P.pointsAUnion (closedBlockNeighborhood neighbors t)).card)
    (hneighbors_symm : ∀ {i j : I}, j ∈ neighbors i → i ∈ neighbors j)
    (hallowed : ∀ (a : A) (b : B),
      P.blockB b = P.blockA a ∨ P.blockB b ∈ neighbors (P.blockA a) →
        (b : X) - (a : X) ∈ D) :
    FiniteDisplacementHall A B D := by
  classical
  constructor
  · intro s
    let t : Finset I := s.image P.blockA
    have hsA : s ⊆ P.pointsAUnion t := by
      intro a ha
      rw [PointBlockData.pointsAUnion]
      rw [Finset.mem_biUnion]
      exact ⟨P.blockA a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
        (P.mem_pointsA (P.blockA a) a).mpr rfl⟩
    have hBneighbors :
        P.pointsBUnion (closedBlockNeighborhood neighbors t) ⊆
          s.biUnion (fun a ↦ forwardNeighbors B D (a : X)) := by
      intro b hb
      rw [PointBlockData.pointsBUnion] at hb
      rw [Finset.mem_biUnion] at hb
      obtain ⟨j, hj, hbj⟩ := hb
      rw [mem_closedBlockNeighborhood] at hj
      obtain hjt | ⟨i, hit, hji⟩ := hj
      · have hblockB : P.blockB b = j := (P.mem_pointsB j b).mp hbj
        obtain ⟨a, ha, hablock⟩ := Finset.mem_image.mp hjt
        rw [Finset.mem_biUnion]
        refine ⟨a, ha, mem_forwardNeighbors b |>.mpr ?_⟩
        exact hallowed a b (Or.inl (hblockB.trans hablock.symm))
      · obtain ⟨a, ha, hablock⟩ := Finset.mem_image.mp hit
        have hblockB : P.blockB b = j := (P.mem_pointsB j b).mp hbj
        rw [Finset.mem_biUnion]
        refine ⟨a, ha, mem_forwardNeighbors b |>.mpr ?_⟩
        exact hallowed a b (Or.inr (hablock ▸ hblockB ▸ hji))
    exact (Finset.card_le_card hsA).trans
      ((hforward t).trans (Finset.card_le_card hBneighbors))
  · intro s
    let t : Finset I := s.image P.blockB
    have hsB : s ⊆ P.pointsBUnion t := by
      intro b hb
      rw [PointBlockData.pointsBUnion]
      rw [Finset.mem_biUnion]
      exact ⟨P.blockB b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
        (P.mem_pointsB (P.blockB b) b).mpr rfl⟩
    have hAneighbors :
        P.pointsAUnion (closedBlockNeighborhood neighbors t) ⊆
          s.biUnion (fun b ↦ backwardNeighbors A D (b : X)) := by
      intro a ha
      rw [PointBlockData.pointsAUnion] at ha
      rw [Finset.mem_biUnion] at ha
      obtain ⟨i, hi, hai⟩ := ha
      rw [mem_closedBlockNeighborhood] at hi
      obtain hit | ⟨j, hjt, hij⟩ := hi
      · have hblockA : P.blockA a = i := (P.mem_pointsA i a).mp hai
        obtain ⟨b, hb, hbblock⟩ := Finset.mem_image.mp hit
        rw [Finset.mem_biUnion]
        refine ⟨b, hb, mem_backwardNeighbors a |>.mpr ?_⟩
        exact hallowed a b (Or.inl (hbblock.trans hblockA.symm))
      · obtain ⟨b, hb, hbblock⟩ := Finset.mem_image.mp hjt
        have hblockA : P.blockA a = i := (P.mem_pointsA i a).mp hai
        rw [Finset.mem_biUnion]
        refine ⟨b, hb, mem_backwardNeighbors a |>.mpr ?_⟩
        -- Here `i` is adjacent to `j`; reverse symmetry is needed in the
        -- point-to-block compatibility, so it is made explicit below.
        exact hallowed a b
          (Or.inr (hneighbors_symm (hbblock ▸ hblockA ▸ hij)))
    exact (Finset.card_le_card hsB).trans
      ((hbackward t).trans (Finset.card_le_card hAneighbors))

end PointBlocks

section BoundedBlockFlow

variable {I : Type*}

/-- An integer flow on a uniformly locally finite undirected graph of blocks.

`divergence_eq` uses the outgoing-minus-incoming convention.  Antisymmetry
then makes the sum of divergences over a finite set equal the flow through its
edge boundary.  Only a one-sided capacity bound is stored: antisymmetry gives
the other side automatically. -/
structure BoundedBlockFlow (aCount bCount : I → ℕ) where
  neighbors : I → Finset I
  degree : ℕ
  capacity : ℕ
  flow : I → I → ℤ
  neighbors_symm : ∀ {i j : I}, j ∈ neighbors i → i ∈ neighbors j
  degree_le : ∀ i : I, (neighbors i).card ≤ degree
  antisymm : ∀ i j : I, flow i j + flow j i = 0
  flow_le : ∀ i j : I, flow i j ≤ capacity
  divergence_eq : ∀ i : I,
    (aCount i : ℤ) - (bCount i : ℤ) = ∑ j ∈ neighbors i, flow i j

/-- The blocks outside `s` which share an edge with a block in `s`. -/
def outerBlockBoundary [DecidableEq I] (neighbors : I → Finset I)
    (s : Finset I) : Finset I :=
  s.biUnion neighbors \ s

@[simp]
lemma mem_outerBlockBoundary [DecidableEq I] {neighbors : I → Finset I}
    {s : Finset I} {j : I} :
    j ∈ outerBlockBoundary neighbors s ↔
      j ∉ s ∧ ∃ i ∈ s, j ∈ neighbors i := by
  classical
  simp only [outerBlockBoundary, Finset.mem_sdiff, Finset.mem_biUnion]
  tauto

namespace BoundedBlockFlow

variable {aCount bCount : I → ℕ} (F : BoundedBlockFlow aCount bCount)

/-- Directed internal edges of a finite family of blocks. -/
def internalEdges [DecidableEq I] (s : Finset I) :
    Finset (Sigma fun _ : I ↦ I) :=
  s.sigma fun i ↦ (F.neighbors i).filter (fun j ↦ j ∈ s)

/-- Directed edges leaving a finite family of blocks. -/
def outgoingEdges [DecidableEq I] (s : Finset I) :
    Finset (Sigma fun _ : I ↦ I) :=
  s.sigma fun i ↦ (F.neighbors i).filter (fun j ↦ j ∉ s)

/-- The same cut edges, indexed first by their endpoint outside the set. -/
def incomingBoundaryEdges [DecidableEq I] (s : Finset I) :
    Finset (Sigma fun _ : I ↦ I) :=
  (outerBlockBoundary F.neighbors s).sigma fun j ↦
    (F.neighbors j).filter (fun i ↦ i ∈ s)

private def swapEdge (p : Sigma fun _ : I ↦ I) : Sigma fun _ : I ↦ I :=
  ⟨p.2, p.1⟩

/-- Antisymmetry cancels every flow along an edge internal to a finite set. -/
lemma sum_internalEdges_eq_zero [DecidableEq I] (s : Finset I) :
    ∑ p ∈ F.internalEdges s, F.flow p.1 p.2 = 0 := by
  classical
  apply Finset.sum_involution (fun p _ ↦ swapEdge p)
  · intro p hp
    exact F.antisymm p.1 p.2
  · intro p hp hflow hfixed
    have hcoord : p.1 = p.2 := by
      have := congrArg Sigma.fst hfixed
      exact this.symm
    have hdiag := F.antisymm p.2 p.2
    apply hflow
    rw [hcoord]
    omega
  · intro p hp
    simp only [internalEdges, Finset.mem_sigma, Finset.mem_filter] at hp ⊢
    simpa only [swapEdge] using
      (show p.2 ∈ s ∧ p.1 ∈ F.neighbors p.2 ∧ p.1 ∈ s from
        ⟨hp.2.2, F.neighbors_symm hp.2.1, hp.1⟩)
  · intro p hp
    rfl

/-- Summing the divergence over a finite set leaves exactly its outgoing cut
flow. -/
lemma sum_divergence_eq_outgoing [DecidableEq I] (s : Finset I) :
    ∑ i ∈ s, ((aCount i : ℤ) - (bCount i : ℤ)) =
      ∑ p ∈ F.outgoingEdges s, F.flow p.1 p.2 := by
  classical
  simp_rw [F.divergence_eq]
  have hsplit :
      (∑ i ∈ s, ∑ j ∈ F.neighbors i, F.flow i j) =
        (∑ p ∈ F.internalEdges s, F.flow p.1 p.2) +
          ∑ p ∈ F.outgoingEdges s, F.flow p.1 p.2 := by
    rw [internalEdges, outgoingEdges, Finset.sum_sigma, Finset.sum_sigma]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (Finset.sum_filter_add_sum_filter_not
      (F.neighbors i) (fun j ↦ j ∈ s) (F.flow i)).symm
  rw [hsplit, F.sum_internalEdges_eq_zero s, zero_add]

/-- Reindex a cut by its outside endpoint.  This is the combinatorial step
which lets the capacity cost be charged once to each outside block, rather
than once to every block already in the set. -/
lemma sum_outgoing_eq_incomingBoundary [DecidableEq I] (s : Finset I) :
    ∑ p ∈ F.outgoingEdges s, F.flow p.1 p.2 =
      ∑ p ∈ F.incomingBoundaryEdges s, F.flow p.2 p.1 := by
  classical
  apply Finset.sum_bij' (fun p _ ↦ swapEdge p) (fun p _ ↦ swapEdge p)
  · intro p hp
    simp only [outgoingEdges, incomingBoundaryEdges, Finset.mem_sigma,
      Finset.mem_filter] at hp ⊢
    have hp2 := hp.2
    refine ⟨?_, ?_⟩
    · rw [mem_outerBlockBoundary]
      exact ⟨hp2.2, ⟨p.1, hp.1, hp2.1⟩⟩
    · simpa only [swapEdge] using
        (show p.1 ∈ F.neighbors p.2 ∧ p.1 ∈ s from
          ⟨F.neighbors_symm hp2.1, hp.1⟩)
  · intro p hp
    simp only [outgoingEdges, incomingBoundaryEdges, Finset.mem_sigma,
      Finset.mem_filter] at hp ⊢
    have hp1 := (mem_outerBlockBoundary.mp hp.1)
    have hp2 := hp.2
    refine ⟨hp2.2, ?_⟩
    simpa only [swapEdge] using
      (show p.1 ∈ F.neighbors p.2 ∧ p.1 ∉ s from
        ⟨F.neighbors_symm hp2.1, hp1.1⟩)
  · intro p hp
    rfl
  · intro p hp
    rfl
  · intro p hp
    rfl

/-- A capacity/degree bound controls the total cut flow by the number of
`B`-points in the outside boundary blocks. -/
lemma sum_outgoing_le_boundary_bCount [DecidableEq I]
    (hroomB : ∀ i : I, F.degree * F.capacity ≤ bCount i)
    (s : Finset I) :
    ∑ p ∈ F.outgoingEdges s, F.flow p.1 p.2 ≤
      ∑ j ∈ outerBlockBoundary F.neighbors s, (bCount j : ℤ) := by
  classical
  rw [F.sum_outgoing_eq_incomingBoundary s, incomingBoundaryEdges,
    Finset.sum_sigma]
  apply Finset.sum_le_sum
  intro j hj
  calc
    (∑ i ∈ (F.neighbors j).filter (fun i ↦ i ∈ s), F.flow i j) ≤
        ∑ _i ∈ (F.neighbors j).filter (fun i ↦ i ∈ s),
          (F.capacity : ℤ) := by
            apply Finset.sum_le_sum
            intro i hi
            exact F.flow_le i j
    _ = (((F.neighbors j).filter (fun i ↦ i ∈ s)).card : ℤ) *
          (F.capacity : ℤ) := by simp
    _ ≤ (F.degree : ℤ) * (F.capacity : ℤ) := by
      gcongr
      exact_mod_cast
        ((Finset.card_filter_le (F.neighbors j) (fun i ↦ i ∈ s)).trans
          (F.degree_le j))
    _ = (F.degree * F.capacity : ℕ) := by norm_num
    _ ≤ bCount j := by exact_mod_cast hroomB j

/-- The bounded integral flow and the positive-density room estimate imply
the forward block Hall inequality. -/
theorem sum_aCount_le_closedNeighborhood [DecidableEq I]
    (hroomB : ∀ i : I, F.degree * F.capacity ≤ bCount i)
    (s : Finset I) :
    ∑ i ∈ s, aCount i ≤
      ∑ j ∈ closedBlockNeighborhood F.neighbors s, bCount j := by
  classical
  have hcut :
      ∑ i ∈ s, ((aCount i : ℤ) - (bCount i : ℤ)) ≤
        ∑ j ∈ outerBlockBoundary F.neighbors s, (bCount j : ℤ) := by
    rw [F.sum_divergence_eq_outgoing s]
    exact F.sum_outgoing_le_boundary_bCount hroomB s
  have hclosed : closedBlockNeighborhood F.neighbors s =
      s ∪ outerBlockBoundary F.neighbors s := by
    ext j
    simp only [mem_closedBlockNeighborhood, mem_outerBlockBoundary,
      Finset.mem_union]
    tauto
  have hdisj : Disjoint s (outerBlockBoundary F.neighbors s) := by
    rw [Finset.disjoint_left]
    intro j hjs hjb
    exact (mem_outerBlockBoundary.mp hjb).1 hjs
  have hcut' :
      (∑ i ∈ s, (aCount i : ℤ)) ≤
        (∑ i ∈ s, (bCount i : ℤ)) +
          ∑ j ∈ outerBlockBoundary F.neighbors s, (bCount j : ℤ) := by
    rw [Finset.sum_sub_distrib] at hcut
    omega
  rw [hclosed, Finset.sum_union hdisj]
  exact_mod_cast hcut'

/-- Negating a bounded block flow exchanges its two divergence counts while
preserving the same graph, degree, and capacity. -/
def reverse : BoundedBlockFlow bCount aCount where
  neighbors := F.neighbors
  degree := F.degree
  capacity := F.capacity
  flow := fun i j ↦ F.flow j i
  neighbors_symm := F.neighbors_symm
  degree_le := F.degree_le
  antisymm := by
    intro i j
    simpa [add_comm] using F.antisymm i j
  flow_le := by
    intro i j
    exact F.flow_le j i
  divergence_eq := by
    intro i
    have hdiv := F.divergence_eq i
    have hanti : ∀ j ∈ F.neighbors i, F.flow j i = -F.flow i j := by
      intro j hj
      linarith [F.antisymm i j]
    calc
      (bCount i : ℤ) - (aCount i : ℤ) =
          -((aCount i : ℤ) - (bCount i : ℤ)) := by ring
      _ = -(∑ j ∈ F.neighbors i, F.flow i j) := by rw [← hdiv]
      _ = ∑ j ∈ F.neighbors i, F.flow j i := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        exact (hanti j hj).symm

/-- The reverse block Hall inequality, obtained by reversing the flow. -/
theorem sum_bCount_le_closedNeighborhood [DecidableEq I]
    (hroomA : ∀ i : I, F.degree * F.capacity ≤ aCount i)
    (s : Finset I) :
    ∑ i ∈ s, bCount i ≤
      ∑ j ∈ closedBlockNeighborhood F.neighbors s, aCount j := by
  simpa [reverse] using
    (F.reverse.sum_aCount_le_closedNeighborhood hroomA s)

end BoundedBlockFlow

end BoundedBlockFlow

section FlowToEquidecomposition

variable {X I : Type*} [AddGroup X] [DecidableEq I]
variable {A B : Set X} {D : Finset X}

/-- **Bounded integral block flow implies finite-displacement Hall.**

This is the complete flow-to-matching conversion used after tiling each free
`ℤ^d` orbit by sufficiently large cubes.  In that application the block graph
has degree `2*d`, the aggregated integral flow has capacity `b*n^(d-1)`,
and the discrepancy estimate supplies the two `hroom` inequalities.
-/
theorem finiteDisplacementHall_of_boundedBlockFlow
    (P : PointBlockData A B I)
    (F : BoundedBlockFlow (fun i ↦ (P.pointsA i).card)
      (fun i ↦ (P.pointsB i).card))
    (hroomA : ∀ i : I, F.degree * F.capacity ≤ (P.pointsA i).card)
    (hroomB : ∀ i : I, F.degree * F.capacity ≤ (P.pointsB i).card)
    (hallowed : ∀ (a : A) (b : B),
      P.blockB b = P.blockA a ∨ P.blockB b ∈ F.neighbors (P.blockA a) →
        (b : X) - (a : X) ∈ D) :
    FiniteDisplacementHall A B D := by
  apply finiteDisplacementHall_of_blockHall P
  · intro t
    rw [P.card_biUnion_pointsA, P.card_biUnion_pointsB]
    exact F.sum_aCount_le_closedNeighborhood hroomB t
  · intro t
    rw [P.card_biUnion_pointsB, P.card_biUnion_pointsA]
    exact F.sum_bCount_le_closedNeighborhood hroomA t
  · exact F.neighbors_symm
  · exact hallowed

/-- The direct equidecomposition conclusion of the bounded integral block
flow argument, with the finite displacement set retained as an explicit
decomposition witness. -/
theorem exists_equidecomp_of_boundedBlockFlow
    (P : PointBlockData A B I)
    (F : BoundedBlockFlow (fun i ↦ (P.pointsA i).card)
      (fun i ↦ (P.pointsB i).card))
    (hroomA : ∀ i : I, F.degree * F.capacity ≤ (P.pointsA i).card)
    (hroomB : ∀ i : I, F.degree * F.capacity ≤ (P.pointsB i).card)
    (hallowed : ∀ (a : A) (b : B),
      P.blockB b = P.blockA a ∨ P.blockB b ∈ F.neighbors (P.blockA a) →
        (b : X) - (a : X) ∈ D) :
    ∃ e : Equidecomp X (Multiplicative X),
      e.source = A ∧ e.target = B ∧
        Equidecomp.IsDecompOn e A (multiplicativeDisplacements D) :=
  exists_equidecomp_of_hall
    (finiteDisplacementHall_of_boundedBlockFlow P F hroomA hroomB hallowed)

end FlowToEquidecomposition

end Erdos1124.BlockMatching
