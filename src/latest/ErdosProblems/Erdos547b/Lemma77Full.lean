import ErdosProblems.Erdos547b.TreePartition
import ErdosProblems.Erdos547b.LeafImbalance
import Mathlib

/-!
# Zhao's ideal partitions (Lemma 7.7)

This file isolates the finite tree combinatorics on pages 43--47 of Yi Zhao,
"Proof of the (n/2-n/2-n/2) Conjecture for large n", EJC 18 (2011), P27.

The natural parameter `q` below represents the integer threshold obtained from
`sqrt(theta) * n` after the harmless rounding mentioned in footnote 11 of the
paper.  Thus `33*q`, `5*q`, and `2*q` are the three leaf thresholds in the
source statement.
-/

namespace Erdos547b.ZhaoLemma77

open Finset SimpleGraph
open scoped Classical

universe u

variable {V : Type u}

/-- A leaf is a vertex of degree one. -/
def IsLeaf (T : SimpleGraph V) [T.LocallyFinite] (v : V) : Prop :=
  T.degree v = 1

/-- The finite set of all leaves. -/
noncomputable def leaves [Fintype V] (T : SimpleGraph V) [T.LocallyFinite] : Finset V :=
  Finset.univ.filter (IsLeaf T)

/-- Leaves lying in a specified part. -/
noncomputable def leavesIn [Fintype V] (T : SimpleGraph V) [T.LocallyFinite]
    (U : Finset V) : Finset V :=
  U.filter (IsLeaf T)

@[simp] theorem mem_leaves [Fintype V] {T : SimpleGraph V} [T.LocallyFinite] {v : V} :
    v ∈ leaves T ↔ IsLeaf T v := by
  simp [leaves]

@[simp] theorem mem_leavesIn [Fintype V] {T : SimpleGraph V} [T.LocallyFinite]
    {U : Finset V} {v : V} :
    v ∈ leavesIn T U ↔ v ∈ U ∧ IsLeaf T v := by
  simp [leavesIn]

theorem leavesIn_eq_inter [Fintype V] (T : SimpleGraph V) [T.LocallyFinite]
    (U : Finset V) : leavesIn T U = U ∩ leaves T := by
  ext v
  simp

/-- A genuine bipartition covering every vertex of the tree. -/
structure IsVertexBipartition [Fintype V] (T : SimpleGraph V)
    (A B : Finset V) : Prop where
  bipartite : T.IsBipartiteWith (A : Set V) (B : Set V)
  cover : A ∪ B = Finset.univ

theorem IsVertexBipartition.disjoint [Fintype V] {T : SimpleGraph V}
    {A B : Finset V} (h : IsVertexBipartition T A B) : Disjoint A B :=
  Finset.disjoint_coe.mp h.bipartite.disjoint

theorem IsVertexBipartition.card_add_card [Fintype V] {T : SimpleGraph V}
    {A B : Finset V} (h : IsVertexBipartition T A B) :
    A.card + B.card = Fintype.card V := by
  rw [← Finset.card_univ, ← h.cover, Finset.card_union_of_disjoint h.disjoint]

theorem IsVertexBipartition.symm [Fintype V] {T : SimpleGraph V}
    {A B : Finset V} (h : IsVertexBipartition T A B) :
    IsVertexBipartition T B A :=
  ⟨h.bipartite.symm, by rw [Finset.union_comm, h.cover]⟩

theorem IsVertexBipartition.right_independent [Fintype V] {T : SimpleGraph V}
    {A B : Finset V} (h : IsVertexBipartition T A B) :
    T.IsIndepSet (B : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hxy
  intro hadj
  rcases h.bipartite.mem_of_adj hadj with hAB | hBA
  · exact (Set.disjoint_left.mp h.bipartite.disjoint hAB.1) hx
  · exact (Set.disjoint_left.mp h.bipartite.disjoint hBA.2) hy

theorem IsVertexBipartition.left_independent [Fintype V] {T : SimpleGraph V}
    {A B : Finset V} (h : IsVertexBipartition T A B) :
    T.IsIndepSet (A : Set V) := h.symm.right_independent

/-- Even root-distance class of a rooted tree. -/
noncomputable def evenPart [Fintype V] (T : SimpleGraph V) (r : V) : Finset V :=
  Finset.univ.filter fun v => T.dist r v % 2 = 0

/-- Odd root-distance class of a rooted tree. -/
noncomputable def oddPart [Fintype V] (T : SimpleGraph V) (r : V) : Finset V :=
  Finset.univ.filter fun v => T.dist r v % 2 = 1

theorem rootParity_ne_of_adj {T : SimpleGraph V} (hT : T.IsTree)
    (r : V) {x y : V} (hxy : T.Adj x y) :
    T.dist r x % 2 ≠ T.dist r y % 2 := by
  rcases hT.dist_eq_dist_add_one_of_adj r hxy with h | h
  · rw [h]
    omega
  · rw [h]
    omega

/-- Every rooted finite tree has the genuine even/odd bipartition used in
Zhao's definition of `g(T)`. -/
theorem rootBipartition [Fintype V] (T : SimpleGraph V) (hT : T.IsTree) (r : V) :
    IsVertexBipartition T (evenPart T r) (oddPart T r) := by
  constructor
  · constructor
    · rw [Set.disjoint_left]
      intro v hvE hvO
      simp [evenPart] at hvE
      simp [oddPart] at hvO
      omega
    · intro x y hxy
      have hne := rootParity_ne_of_adj hT r hxy
      have hxlt : T.dist r x % 2 < 2 := Nat.mod_lt _ (by omega)
      have hylt : T.dist r y % 2 < 2 := Nat.mod_lt _ (by omega)
      by_cases hx : T.dist r x % 2 = 0
      · left
        have hy : T.dist r y % 2 = 1 := by omega
        simpa [evenPart, oddPart, hx, hy]
      · right
        have hx' : T.dist r x % 2 = 1 := by omega
        have hy : T.dist r y % 2 = 0 := by omega
        simpa [evenPart, oddPart, hx', hy]
  · ext v
    simp only [Finset.mem_union, evenPart, oddPart, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact iff_true_intro (Nat.mod_two_eq_zero_or_one _)

/-- A leaf has a unique neighbour. -/
theorem existsUnique_neighbor_of_isLeaf [Fintype V] {T : SimpleGraph V} {v : V}
    (hv : IsLeaf T v) : ∃! w, T.Adj v w := by
  unfold IsLeaf at hv
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hv
  exact hv

/-- The unique neighbour of a leaf.  Its value away from leaves is immaterial. -/
noncomputable def leafParent [Fintype V] (T : SimpleGraph V) (v : V) : V :=
  if hv : IsLeaf T v then (existsUnique_neighbor_of_isLeaf hv).exists.choose else v

theorem leafParent_adj [Fintype V] {T : SimpleGraph V} {v : V}
    (hv : IsLeaf T v) : T.Adj v (leafParent T v) := by
  rw [leafParent, dif_pos hv]
  exact (existsUnique_neighbor_of_isLeaf hv).exists.choose_spec

theorem eq_leafParent_of_adj [Fintype V] {T : SimpleGraph V} {v w : V}
    (hv : IsLeaf T v) (hvw : T.Adj v w) : w = leafParent T v := by
  rw [leafParent, dif_pos hv]
  exact (existsUnique_neighbor_of_isLeaf hv).unique hvw
    (existsUnique_neighbor_of_isLeaf hv).exists.choose_spec

/-- Parents of a finite family of leaves. -/
noncomputable def leafParents [Fintype V] (T : SimpleGraph V) (W : Finset V) : Finset V :=
  W.image (leafParent T)

@[simp] theorem mem_leafParents [Fintype V] {T : SimpleGraph V} {W : Finset V} {y : V} :
    y ∈ leafParents T W ↔ ∃ z ∈ W, leafParent T z = y := by
  simp [leafParents]

/-- The second class after Zhao's Case-a flip: delete the parents of the
selected leaves from `B`, and insert the leaves themselves. -/
noncomputable def leafFlipRight [Fintype V] (T : SimpleGraph V)
    (B W : Finset V) : Finset V :=
  (B \ leafParents T W) ∪ W

/-- Complementary class after the same flip. -/
noncomputable def leafFlipLeft [Fintype V] (T : SimpleGraph V)
    (A B W : Finset V) : Finset V :=
  Finset.univ \ leafFlipRight T B W

theorem leafFlip_partition [Fintype V] (T : SimpleGraph V) (A B W : Finset V) :
    Disjoint (leafFlipLeft T A B W) (leafFlipRight T B W) ∧
      leafFlipLeft T A B W ∪ leafFlipRight T B W = Finset.univ := by
  constructor
  · rw [Finset.disjoint_left]
    intro x hx hxr
    change x ∈ leafFlipLeft T A B W at hx
    simp only [leafFlipLeft, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
    exact hx hxr
  · simp [leafFlipLeft]

/-- The key graph-theoretic point in Zhao's Case-a flip.  If `W` consists of
leaves in the left class of a bipartition, then replacing their parents in the
right class by the leaves leaves the right class independent. -/
theorem leafFlipRight_independent [Fintype V]
    (T : SimpleGraph V) (A B W : Finset V)
    (hpart : IsVertexBipartition T A B)
    (hW : W ⊆ leavesIn T A) :
    T.IsIndepSet (leafFlipRight T B W : Set V) := by
  classical
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hxy hAdj
  change x ∈ leafFlipRight T B W at hx
  change y ∈ leafFlipRight T B W at hy
  simp only [leafFlipRight, Finset.mem_union, Finset.mem_sdiff] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hpart.right_independent hx.1 hy.1 hxy hAdj
  · have hyLeaf : IsLeaf T y := (mem_leavesIn.mp (hW hy)).2
    have hpEq : x = leafParent T y := by
      exact eq_leafParent_of_adj hyLeaf hAdj.symm
    apply hx.2
    exact mem_leafParents.mpr ⟨y, hy, hpEq.symm⟩
  · have hxLeaf : IsLeaf T x := (mem_leavesIn.mp (hW hx)).2
    have hpEq : y = leafParent T x := eq_leafParent_of_adj hxLeaf hAdj
    apply hy.2
    exact mem_leafParents.mpr ⟨x, hx, hpEq.symm⟩
  · have hxA : x ∈ A := (mem_leavesIn.mp (hW hx)).1
    have hyA : y ∈ A := (mem_leavesIn.mp (hW hy)).1
    exact hpart.left_independent hxA hyA hxy hAdj

/-- No selected leaf is also one of the selected parents (the two sets lie in
opposite bipartition classes). -/
theorem disjoint_leafParents_selectedLeaves [Fintype V]
    (T : SimpleGraph V) (A B W : Finset V)
    (hpart : IsVertexBipartition T A B)
    (hW : W ⊆ leavesIn T A) :
    Disjoint (leafParents T W) W := by
  rw [Finset.disjoint_left]
  intro y hyP hyW
  obtain ⟨z, hzW, hp⟩ := mem_leafParents.mp hyP
  have hzA : z ∈ A := (mem_leavesIn.mp (hW hzW)).1
  have hzLeaf : IsLeaf T z := (mem_leavesIn.mp (hW hzW)).2
  have hyB : y ∈ B := by
    rw [← hp]
    exact hpart.bipartite.mem_of_mem_adj hzA (leafParent_adj hzLeaf)
  have hyA : y ∈ A := (mem_leavesIn.mp (hW hyW)).1
  exact (Finset.disjoint_left.mp hpart.disjoint hyA hyB)

theorem card_leafParents_le [Fintype V] (T : SimpleGraph V) (W : Finset V) :
    (leafParents T W).card ≤ W.card := by
  classical
  simpa only [leafParents] using (Finset.card_image_le (s := W) (f := leafParent T))

/-- The leaf flip never decreases the size of the right class: each removed
parent is paid for by at least one selected leaf. -/
theorem card_right_le_card_leafFlipRight [Fintype V]
    (T : SimpleGraph V) (A B W : Finset V)
    (hpart : IsVertexBipartition T A B)
    (hW : W ⊆ leavesIn T A) :
    B.card ≤ (leafFlipRight T B W).card := by
  classical
  have hBW : Disjoint B W := by
    apply Finset.disjoint_of_subset_right
      (fun w hw => (mem_leavesIn.mp (hW hw)).1)
    exact hpart.disjoint.symm
  have hPsubB : leafParents T W ⊆ B := by
    intro y hy
    obtain ⟨z, hzW, rfl⟩ := mem_leafParents.mp hy
    exact hpart.bipartite.mem_of_mem_adj
      (mem_leavesIn.mp (hW hzW)).1
      (leafParent_adj (mem_leavesIn.mp (hW hzW)).2)
  change B.card ≤ ((B \ leafParents T W) ∪ W).card
  rw [Finset.card_union_of_disjoint
    (Finset.disjoint_of_subset_left Finset.sdiff_subset hBW)]
  rw [Finset.card_sdiff]
  have hInter : leafParents T W ∩ B = leafParents T W :=
    Finset.inter_eq_left.mpr hPsubB
  rw [hInter]
  have hparents := card_leafParents_le T W
  omega

/-- Zhao Definition 7.6(1), with `q` standing for the rounded value of
`sqrt(theta) n`. -/
structure IsIdealPartition [Fintype V] (q : ℕ) (T : SimpleGraph V)
    (U₁ U₂ : Finset V) : Prop where
  partition : Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = Finset.univ
  card_le : U₁.card ≤ U₂.card
  right_independent : T.IsIndepSet (U₂ : Set V)
  left_leaves : 5 * q ≤ (leavesIn T U₁).card
  right_leaves : 2 * q ≤ (leavesIn T U₂).card

/-- Zhao Definition 7.6(2).  The last field is the root-free equivalent of
"a leaf `z` in `U₁` whose parent `y` in `U₂` has degree two": a leaf has a
unique neighbour, so that neighbour is its parent for every rooting away from
`z`. -/
structure IsNearIdealPartition [Fintype V] (q n : ℕ) (T : SimpleGraph V)
    (U₁ U₂ : Finset V) : Prop where
  partition : Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = Finset.univ
  n_even : Even n
  left_card : U₁.card = n / 2 + 1
  right_card : U₂.card = n / 2
  right_independent : T.IsIndepSet (U₂ : Set V)
  left_leaves : 5 * q ≤ (leavesIn T U₁).card
  right_leaves : 2 * q ≤ (leavesIn T U₂).card
  special_leaf : ∃ z ∈ U₁, IsLeaf T z ∧ ∃ y ∈ U₂, T.Adj y z ∧ T.degree y = 2

/-- The gap of a displayed bipartition.  For a connected bipartite graph the
two possible displayed bipartitions differ only by swapping the sides, hence
this is Zhao's `g(T)`. -/
def bipartitionGap (A B : Finset V) : ℕ := Nat.dist A.card B.card

/-- The canonical bipartition itself is ideal as soon as its smaller side and
larger side already contain the required numbers of leaves.  This is the
first branch of Zhao's proof of Lemma 7.7. -/
theorem ideal_of_bipartition_leaf_bounds [Fintype V]
    (q : ℕ) (T : SimpleGraph V) (A B : Finset V)
    (hpart : IsVertexBipartition T A B) (hcard : A.card ≤ B.card)
    (hA : 5 * q ≤ (leavesIn T A).card)
    (hB : 2 * q ≤ (leavesIn T B).card) :
    IsIdealPartition q T A B := by
  exact ⟨⟨hpart.disjoint, hpart.cover⟩, hcard, hpart.right_independent, hA, hB⟩

/-- The leaf sets in the two classes of a vertex bipartition partition the
full leaf set. -/
theorem leavesIn_union_leavesIn [Fintype V]
    (T : SimpleGraph V) (A B : Finset V)
    (hpart : IsVertexBipartition T A B) :
    leavesIn T A ∪ leavesIn T B = leaves T := by
  ext v
  constructor
  · simp only [Finset.mem_union, mem_leavesIn, mem_leaves]
    rintro (⟨_, hv⟩ | ⟨_, hv⟩) <;> exact hv
  · intro hv
    have hvLeaf : IsLeaf T v := mem_leaves.mp hv
    have hvAB : v ∈ A ∨ v ∈ B := by
      have : v ∈ A ∪ B := by simpa [hpart.cover]
      simpa using this
    simpa [hvLeaf] using hvAB

theorem disjoint_leavesIn_of_bipartition [Fintype V]
    (T : SimpleGraph V) (A B : Finset V)
    (hpart : IsVertexBipartition T A B) :
    Disjoint (leavesIn T A) (leavesIn T B) := by
  exact Finset.disjoint_of_subset_left (by intro v hv; exact (mem_leavesIn.mp hv).1) <|
    Finset.disjoint_of_subset_right (by intro v hv; exact (mem_leavesIn.mp hv).1)
      hpart.disjoint

theorem card_leaves_eq_card_leavesIn_add [Fintype V]
    (T : SimpleGraph V) (A B : Finset V)
    (hpart : IsVertexBipartition T A B) :
    (leaves T).card = (leavesIn T A).card + (leavesIn T B).card := by
  rw [← leavesIn_union_leavesIn T A B hpart,
    Finset.card_union_of_disjoint (disjoint_leavesIn_of_bipartition T A B hpart)]

/-- Zhao Lemma 7.7, Case (a): when the larger bipartition class has fewer
than `2q` leaves, flip `2q` leaves from the smaller class together with their
parents.  The generous constant `33` leaves more than enough leaves on the
left after the operation. -/
theorem exists_ideal_of_right_leaf_deficit [Fintype V]
    (q : ℕ) (T : SimpleGraph V) (A B : Finset V)
    (hpart : IsVertexBipartition T A B)
    (hcard : A.card ≤ B.card)
    (hmany : 33 * q ≤ (leaves T).card)
    (hdef : (leavesIn T B).card < 2 * q) :
    ∃ U₁ U₂, IsIdealPartition q T U₁ U₂ := by
  have hleafSum := card_leaves_eq_card_leavesIn_add T A B hpart
  have hAenough : 2 * q ≤ (leavesIn T A).card := by omega
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hAenough
  let U₂ := leafFlipRight T B W
  let U₁ := leafFlipLeft T A B W
  have hW : W ⊆ leavesIn T A := hWsub
  have hPartition := leafFlip_partition T A B W
  have hIndep : T.IsIndepSet (U₂ : Set V) := by
    exact leafFlipRight_independent T A B W hpart hW
  have hBcard : B.card ≤ U₂.card := by
    exact card_right_le_card_leafFlipRight T A B W hpart hW
  have hCardSumNew : U₁.card + U₂.card = Fintype.card V := by
    rw [← Finset.card_univ, ← hPartition.2,
      Finset.card_union_of_disjoint hPartition.1]
  have hCardSumOld := hpart.card_add_card
  have hUcard : U₁.card ≤ U₂.card := by omega
  have hWsubU₂ : W ⊆ U₂ := by
    intro w hw
    simp [U₂, leafFlipRight, hw]
  have hWleafU₂ : W ⊆ leavesIn T U₂ := by
    intro w hw
    exact mem_leavesIn.mpr ⟨hWsubU₂ hw, (mem_leavesIn.mp (hW hw)).2⟩
  have hRightLeaves : 2 * q ≤ (leavesIn T U₂).card := by
    calc
      2 * q = W.card := hWcard.symm
      _ ≤ (leavesIn T U₂).card := Finset.card_le_card hWleafU₂
  have hRemainSub : leavesIn T A \ W ⊆ leavesIn T U₁ := by
    intro v hv
    have hvA : v ∈ A := (mem_leavesIn.mp (Finset.mem_sdiff.mp hv).1).1
    have hvLeaf : IsLeaf T v := (mem_leavesIn.mp (Finset.mem_sdiff.mp hv).1).2
    have hvNotW : v ∉ W := (Finset.mem_sdiff.mp hv).2
    have hvNotB : v ∉ B := fun hvB =>
      Finset.disjoint_left.mp hpart.disjoint hvA hvB
    have hvNotU₂ : v ∉ U₂ := by
      simp [U₂, leafFlipRight, hvNotB, hvNotW]
    have hvU₁ : v ∈ U₁ := by
      change v ∈ Finset.univ \ U₂
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvNotU₂⟩
    exact mem_leavesIn.mpr ⟨hvU₁, hvLeaf⟩
  have hRemainCard : (leavesIn T A \ W).card = (leavesIn T A).card - 2 * q := by
    rw [Finset.card_sdiff_of_subset hW, hWcard]
  have hLeftLeaves : 5 * q ≤ (leavesIn T U₁).card := by
    have hle := Finset.card_le_card hRemainSub
    rw [hRemainCard] at hle
    omega
  exact ⟨U₁, U₂,
    ⟨hPartition, hUcard, hIndep, hLeftLeaves, hRightLeaves⟩⟩

/-- Complete, assumption-free reduction of Lemma 7.7 to Zhao's hard natural-
subtree branch.  Once the bipartition is oriented with `A` no larger than
`B`, every case except `A` having fewer than `5q` leaves is discharged by the
two constructive theorems above. -/
theorem lemma7_7_reduction_to_left_leaf_deficit [Fintype V]
    (q : ℕ) (T : SimpleGraph V) (A B : Finset V)
    (hpart : IsVertexBipartition T A B)
    (hcard : A.card ≤ B.card)
    (hmany : 33 * q ≤ (leaves T).card) :
    2 * q + 1 ≤ bipartitionGap A B ∨
      (∃ U₁ U₂, IsIdealPartition q T U₁ U₂) ∨
      ((leavesIn T A).card < 5 * q ∧
        2 * q ≤ (leavesIn T B).card ∧
        bipartitionGap A B < 2 * q + 1) := by
  by_cases hgap : 2 * q + 1 ≤ bipartitionGap A B
  · exact Or.inl hgap
  right
  have hgaplt : bipartitionGap A B < 2 * q + 1 := Nat.lt_of_not_ge hgap
  by_cases hB : 2 * q ≤ (leavesIn T B).card
  · by_cases hA : 5 * q ≤ (leavesIn T A).card
    · exact Or.inl ⟨A, B,
        ideal_of_bipartition_leaf_bounds q T A B hpart hcard hA hB⟩
    · exact Or.inr ⟨Nat.lt_of_not_ge hA, hB, hgaplt⟩
  · exact Or.inl (exists_ideal_of_right_leaf_deficit q T A B hpart hcard hmany
      (Nat.lt_of_not_ge hB))

end Erdos547b.ZhaoLemma77

#print axioms Erdos547b.ZhaoLemma77.ideal_of_bipartition_leaf_bounds
#print axioms Erdos547b.ZhaoLemma77.exists_ideal_of_right_leaf_deficit
#print axioms Erdos547b.ZhaoLemma77.lemma7_7_reduction_to_left_leaf_deficit
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
Finite rooted-tree ingredients for Zhao's Fact 7.9.  The graph remains a
genuine `SimpleGraph`; a natural subtree rooted at `x` consists of `x` and a
chosen collection of whole child branches.  Thus all edges from the chosen
part to the rest of the tree have their chosen endpoint at `x`.
-/

open scoped BigOperators

namespace Erdos547b.Lemma77Rooted

open SimpleGraph Finset
open Erdos547b.TreePartition

universe u

variable {V : Type u}

noncomputable local instance [Finite V] (T : SimpleGraph V) : T.LocallyFinite := fun _ =>
  Fintype.ofFinite _

/-- Ordinary (unrooted) leaves. -/
def IsLeaf [Fintype V] (T : SimpleGraph V) (v : V) : Prop := T.degree v = 1

noncomputable def leaves [Fintype V] (T : SimpleGraph V) : Finset V :=
  by classical exact Finset.univ.filter (IsLeaf T)

noncomputable def leavesIn [Fintype V] (T : SimpleGraph V) (U : Finset V) : Finset V :=
  by classical exact U.filter (IsLeaf T)

@[simp] theorem mem_leaves [Fintype V] {T : SimpleGraph V} {v : V} :
    v ∈ leaves T ↔ IsLeaf T v := by classical simp [leaves]

@[simp] theorem mem_leavesIn [Fintype V] {T : SimpleGraph V} {U : Finset V} {v : V} :
    v ∈ leavesIn T U ↔ v ∈ U ∧ IsLeaf T v := by classical simp [leavesIn]

theorem leavesIn_eq_inter [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (U : Finset V) :
    leavesIn T U = U ∩ leaves T := by
  classical
  ext v
  simp

/-- The children of `x` when the tree is oriented away from `r`. -/
noncomputable def children [Fintype V] (T : SimpleGraph V) (r x : V) : Finset V :=
  by classical exact Finset.univ.filter (IsChild T r x)

@[simp] theorem mem_children [Fintype V] {T : SimpleGraph V} {r x y : V} :
    y ∈ children T r x ↔ IsChild T r x y := by classical simp [children]

/-- A natural subtree vertex set: keep the root `x` and any chosen collection
of whole child branches. -/
noncomputable def naturalVertices [Fintype V] (T : SimpleGraph V) (r x : V)
    (kept : Finset V) : Finset V :=
  by classical exact {x} ∪ kept.biUnion (rootedDescendants T r)

def IsNaturalVertexSet [Fintype V] (T : SimpleGraph V) (r : V)
    (U : Finset V) : Prop :=
  ∃ x kept, kept ⊆ children T r x ∧ U = naturalVertices T r x kept

/-- The boundary condition used in Zhao's leaf-side flip: every crossing edge
has the same endpoint on the natural-subtree side. -/
def HasSingleBoundaryAttachment (T : SimpleGraph V) (U : Set V) (x : V) : Prop :=
  ∀ ⦃u v : V⦄, T.Adj u v → u ∈ U → v ∉ U → u = x

/-- Dual form used when the attachment vertex itself is not flipped. -/
def HasSingleOutsideBoundaryAttachment
    (T : SimpleGraph V) (U : Set V) (x : V) : Prop :=
  ∀ ⦃u v : V⦄, T.Adj u v → u ∈ U → v ∉ U → v = x

/-- Zhao's nonstandard `T - T'` keeps the attachment vertex. -/
noncomputable def naturalComplement [Fintype V] (U : Finset V) (x : V) : Finset V :=
  by classical exact insert x (Finset.univ \ U)

@[simp] theorem mem_naturalComplement [Fintype V] [DecidableEq V]
    {U : Finset V} {x v : V} :
    v ∈ naturalComplement U x ↔ v = x ∨ v ∉ U := by
  simp [naturalComplement]

/-- First-threshold crossing for a finite family of weights. -/
theorem exists_subset_sum_in_half_open_interval
    {α : Type*} [DecidableEq α] (q : ℕ) (hq : 0 < q)
    (s : Finset α) (w : α → ℕ)
    (hsmall : ∀ a ∈ s, w a < q)
    (htotal : q ≤ ∑ a ∈ s, w a) :
    ∃ t ⊆ s, q ≤ ∑ a ∈ t, w a ∧ ∑ a ∈ t, w a < 2 * q := by
  let xs := s.toList
  let weights := xs.map w
  let P : ℕ → Prop := fun i => q ≤ (weights.take i).sum
  have htotal' : q ≤ weights.sum := by
    simpa [weights, xs] using htotal
  have hex : ∃ i, P i := by
    refine ⟨weights.length, ?_⟩
    simpa [P] using htotal'
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
  have hnodup : chosenList.Nodup := by
    exact (Finset.nodup_toList s).take
  have hsum : ∑ a ∈ t, w a = (weights.take i).sum := by
    have htake : weights.take i = chosenList.map w := by
      simp [weights, chosenList, xs]
    rw [htake]
    simpa [t] using (List.sum_toFinset w hnodup)
  refine ⟨t, htSub, ?_, ?_⟩
  · rw [hsum]
    exact hi
  rw [hsum]
  by_cases hi0 : i = 0
  · have hq0 : q ≤ 0 := by simpa [P, hi0] using hi
    omega
  · let j := i - 1
    have hji : j < i := by simp [j]; omega
    have hjlt : (weights.take j).sum < q := by
      have := Nat.find_min hex hji
      simp only [P] at this
      omega
    have hjlen : j < weights.length := by omega
    have hisucc : j + 1 = i := by simp [j]; omega
    have hwmem : weights[j] ∈ weights := List.getElem_mem hjlen
    obtain ⟨a, ha, haw⟩ := List.mem_map.mp hwmem
    have haS : a ∈ s := by
      exact Finset.mem_toList.mp (by simpa [weights, xs] using ha)
    have hwlt : weights[j] < q := by simpa [haw] using hsmall a haS
    rw [← hisucc, List.sum_take_succ weights j hjlen]
    omega

/-- Every proper descendant lies in one of the immediate child branches. -/
theorem exists_child_of_mem_rootedDescendants [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x z : V}
    (hz : z ∈ rootedDescendants T r x) (hzx : z ≠ x) :
    ∃ y ∈ children T r x, z ∈ rootedDescendants T r y := by
  obtain ⟨p, hpPath, hpLength⟩ := hT.connected.exists_path_of_dist x z
  have hpNotNil : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hzx.symm
  let y := p.snd
  have hxy : T.Adj x y := p.adj_snd hpNotNil
  have htailLength : p.tail.length = T.dist y z :=
    SimpleGraph.length_eq_dist_of_subwalk hpLength
      ((SimpleGraph.Walk.isSubwalk_rfl p).tail)
  have hdistxz : T.dist x z = 1 + T.dist y z := by
    rw [← hpLength, ← htailLength]
    have := p.length_tail_add_one hpNotNil
    omega
  rw [mem_rootedDescendants] at hz
  have hLower : T.dist r x + 1 ≤ T.dist r y := by
    have htri := hT.connected.dist_triangle (u := r) (v := y) (w := z)
    omega
  have hUpper : T.dist r y ≤ T.dist r x + 1 := by
    have hxyDist : T.dist x y = 1 := T.dist_eq_one_iff_adj.mpr hxy
    simpa only [hxyDist] using hT.connected.dist_triangle (u := r) (v := x) (w := y)
  have hlevel : T.dist r y = T.dist r x + 1 := Nat.le_antisymm hUpper hLower
  refine ⟨y, mem_children.mpr ⟨hxy, hlevel⟩, ?_⟩
  rw [mem_rootedDescendants]
  omega

theorem pairwiseDisjoint_leavesIn_children [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) (r x : V) :
    (↑(children T r x) : Set V).PairwiseDisjoint
      (fun y => leavesIn T (rootedDescendants T r y)) := by
  classical
  intro y hy z hz hyz
  exact (disjoint_rootedDescendants_of_distinct_children hT
    (mem_children.mp hy) (mem_children.mp hz) hyz).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- A non-root ordinary leaf has no children. -/
theorem children_eq_empty_of_leaf_of_ne_root [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V}
    (hxLeaf : IsLeaf T x) (hxr : x ≠ r) : children T r x = ∅ := by
  classical
  apply Finset.Subset.antisymm
  · intro y hy
    have hxy := (mem_children.mp hy)
    have hxp : T.Adj x (parent hT r hxr) := (parent_adj hT r hxr).symm
    have hyEq : y = parent hT r hxr := by
      have hu := degree_eq_one_iff_existsUnique_adj.mp hxLeaf
      exact hu.unique hxy.1 hxp
    have hpLevel := parent_dist_add_one hT r hxr
    rw [hyEq] at hxy
    have hchildLevel := hxy.2
    omega
  · exact Finset.empty_subset _

theorem rootedDescendants_subset_singleton_of_leaf_of_ne_root [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V}
    (hxLeaf : IsLeaf T x) (hxr : x ≠ r) :
    rootedDescendants T r x ⊆ {x} := by
  classical
  intro z hz
  by_contra hzx
  have hzx' : z ≠ x := by simpa using hzx
  obtain ⟨y, hy, -⟩ := exists_child_of_mem_rootedDescendants hT hz hzx'
  rw [children_eq_empty_of_leaf_of_ne_root hT hxLeaf hxr] at hy
  simp at hy

theorem card_leavesIn_rootedDescendants_le_one_of_leaf_of_ne_root [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V}
    (hxLeaf : IsLeaf T x) (hxr : x ≠ r) :
    (leavesIn T (rootedDescendants T r x)).card ≤ 1 := by
  classical
  calc
    (leavesIn T (rootedDescendants T r x)).card ≤ ({x} : Finset V).card :=
      Finset.card_le_card <|
        (Finset.filter_subset _ _).trans
          (rootedDescendants_subset_singleton_of_leaf_of_ne_root hT hxLeaf hxr)
    _ = 1 := Finset.card_singleton x

/-- Leaves of a non-leaf rooted branch are partitioned by its child branches. -/
theorem leavesIn_rootedDescendants_eq_biUnion [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V}
    (hx : ¬IsLeaf T x) :
    leavesIn T (rootedDescendants T r x) =
      (children T r x).biUnion
        (fun y => leavesIn T (rootedDescendants T r y)) := by
  classical
  ext z
  constructor
  · intro hz
    have hzDesc := (mem_leavesIn.mp hz).1
    have hzx : z ≠ x := by
      intro h
      subst z
      exact hx (mem_leavesIn.mp hz).2
    obtain ⟨y, hyChild, hyDesc⟩ :=
      exists_child_of_mem_rootedDescendants hT hzDesc hzx
    simp only [Finset.mem_biUnion]
    exact ⟨y, hyChild, mem_leavesIn.mpr ⟨hyDesc, (mem_leavesIn.mp hz).2⟩⟩
  · intro hz
    simp only [Finset.mem_biUnion] at hz
    obtain ⟨y, hyChild, hzLeaf⟩ := hz
    refine mem_leavesIn.mpr ⟨?_, (mem_leavesIn.mp hzLeaf).2⟩
    exact rootedDescendants_mono_of_child hT (mem_children.mp hyChild)
      (mem_leavesIn.mp hzLeaf).1

theorem card_leavesIn_rootedDescendants_eq_sum [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V}
    (hx : ¬IsLeaf T x) :
    (leavesIn T (rootedDescendants T r x)).card =
      ∑ y ∈ children T r x,
        (leavesIn T (rootedDescendants T r y)).card := by
  classical
  rw [leavesIn_rootedDescendants_eq_biUnion hT hx]
  exact Finset.card_biUnion (pairwiseDisjoint_leavesIn_children hT r x)

/-- The leaf count of a natural subtree is the sum of the leaf counts of its
kept child branches, provided its attachment root is not itself a leaf. -/
theorem card_leavesIn_naturalVertices_eq_sum [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V}
    (hx : ¬IsLeaf T x) (kept : Finset V) (hkept : kept ⊆ children T r x) :
    (leavesIn T (naturalVertices T r x kept)).card =
      ∑ y ∈ kept, (leavesIn T (rootedDescendants T r y)).card := by
  classical
  have hpair : (↑kept : Set V).PairwiseDisjoint
      (fun y => leavesIn T (rootedDescendants T r y)) := by
    intro y hy z hz hyz
    exact pairwiseDisjoint_leavesIn_children hT r x (hkept hy) (hkept hz) hyz
  have heq : leavesIn T (naturalVertices T r x kept) =
      kept.biUnion (fun y => leavesIn T (rootedDescendants T r y)) := by
    ext z
    simp only [mem_leavesIn, naturalVertices, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_biUnion]
    constructor
    · rintro ⟨hz | hz, hzLeaf⟩
      · exact (hx (hz ▸ hzLeaf)).elim
      · obtain ⟨y, hy, hzDesc⟩ := hz
        exact ⟨y, hy, ⟨hzDesc, hzLeaf⟩⟩
    · rintro ⟨y, hy, hzDesc, hzLeaf⟩
      exact ⟨Or.inr ⟨y, hy, hzDesc⟩, hzLeaf⟩
  rw [heq]
  exact Finset.card_biUnion hpair

/-- A deepest rooted branch carrying at least `q` leaves has no child branch
carrying `q` leaves. -/
theorem exists_leaf_heavy_with_small_children [Fintype V]
    (T : SimpleGraph V) (r : V) (q : ℕ)
    (htotal : q ≤ (leaves T).card) :
    ∃ x : V,
      q ≤ (leavesIn T (rootedDescendants T r x)).card ∧
      ∀ y ∈ children T r x,
        (leavesIn T (rootedDescendants T r y)).card < q := by
  classical
  let large : Finset V := Finset.univ.filter fun x =>
    q ≤ (leavesIn T (rootedDescendants T r x)).card
  have hr : r ∈ large := by
    simp only [large, Finset.mem_filter, Finset.mem_univ, true_and,
      rootedDescendants_root]
    simpa [leavesIn, leaves] using htotal
  obtain ⟨x, hxLarge, hxMax⟩ :=
    Finset.exists_max_image large (fun z => T.dist r z) ⟨r, hr⟩
  refine ⟨x, (Finset.mem_filter.mp hxLarge).2, ?_⟩
  intro y hyChild
  by_contra hnot
  have hyLarge : y ∈ large := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_gt hnot⟩
  have hMax := hxMax y hyLarge
  have hLevel := (mem_children.mp hyChild).2
  omega

theorem mem_rootedDescendants_of_adj_deeper [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r y u v : V}
    (hu : u ∈ rootedDescendants T r y) (huv : T.Adj u v)
    (hlevel : T.dist r v = T.dist r u + 1) :
    v ∈ rootedDescendants T r y := by
  rw [mem_rootedDescendants] at hu ⊢
  rcases hT.dist_eq_dist_add_one_of_adj y huv with hbad | hyv
  · have htri := hT.connected.dist_triangle (u := r) (v := y) (w := v)
    omega
  · omega

/-- Away from the branch root, a rooted descendant branch is closed under
adjacency. -/
theorem mem_rootedDescendants_of_adj_of_ne_root [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r y u v : V}
    (hu : u ∈ rootedDescendants T r y) (huy : u ≠ y) (huv : T.Adj u v) :
    v ∈ rootedDescendants T r y := by
  rcases hT.dist_eq_dist_add_one_of_adj r huv with hlower | hdeeper
  · obtain ⟨p, hpPath, hpLength⟩ := hT.connected.exists_path_of_dist y u
    have hpNotNil : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne huy.symm
    let w := p.penultimate
    have hwu : T.Adj w u := p.adj_penultimate hpNotNil
    have hdropLength : p.dropLast.length = T.dist y w :=
      SimpleGraph.length_eq_dist_of_subwalk hpLength
        ((SimpleGraph.Walk.isSubwalk_rfl p).dropLast)
    have hywu : T.dist y w + 1 = T.dist y u := by
      rw [← hpLength, ← hdropLength]
      exact p.length_dropLast_add_one hpNotNil
    have huEq := (mem_rootedDescendants.mp hu)
    have hrwUpper : T.dist r w ≤ T.dist r u - 1 := by
      have htri := hT.connected.dist_triangle (u := r) (v := y) (w := w)
      omega
    have hrwu : T.dist r w + 1 = T.dist r u := by
      rcases hT.dist_eq_dist_add_one_of_adj r hwu with h | h
      · omega
      · exact h.symm
    have hvEqW : v = w := by
      have hur : u ≠ r := by
        intro h
        subst u
        simp at hlower
      have hvParent : v = parent hT r hur :=
        eq_parent_of_adj_of_dist_add_one hT r hur huv.symm hlower.symm
      have hwParent : w = parent hT r hur :=
        eq_parent_of_adj_of_dist_add_one hT r hur hwu hrwu
      exact hvParent.trans hwParent.symm
    rw [hvEqW, mem_rootedDescendants]
    omega
  · exact mem_rootedDescendants_of_adj_deeper hT hu huv hdeeper

/-- Every edge leaving a natural subtree has its inside endpoint at the
attachment root.  This is the precise graph form of Zhao's natural-subtree
boundary assertion. -/
theorem naturalVertices_hasSingleBoundaryAttachment [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V}
    (kept : Finset V) (hkept : kept ⊆ children T r x) :
    HasSingleBoundaryAttachment T (naturalVertices T r x kept : Set V) x := by
  classical
  intro u v huv huU hvU
  simp only [naturalVertices, Finset.coe_union, Finset.coe_singleton,
    Finset.coe_biUnion, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_iUnion] at huU
  rcases huU with rfl | huU
  · rfl
  · obtain ⟨y, hy⟩ := huU
    obtain ⟨hyKept, huDesc⟩ := hy
    by_cases huy : u = y
    · subst u
      have hyChild := mem_children.mp (hkept hyKept)
      rcases hT.dist_eq_dist_add_one_of_adj r huv with hlower | hdeeper
      · have hyr : y ≠ r := by
          intro h
          subst y
          have := hyChild.2
          simp at this
        have hvEq : v = x :=
          eq_parent_of_adj_of_dist_add_one hT r hyr huv.symm hlower.symm |>.trans
            (eq_parent_of_adj_of_dist_add_one hT r hyr hyChild.1
              hyChild.2.symm).symm
        exfalso
        apply (hvU (by
          change v ∈ naturalVertices T r x kept
          rw [hvEq]
          simp [naturalVertices]))
      · exfalso
        apply (hvU (by
          change v ∈ naturalVertices T r x kept
          simp only [naturalVertices, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_biUnion]
          exact Or.inr ⟨y, hyKept,
            mem_rootedDescendants_of_adj_deeper hT
              (self_mem_rootedDescendants T r y) huv hdeeper⟩))
    · exfalso
      apply (hvU (by
        change v ∈ naturalVertices T r x kept
        simp only [naturalVertices, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_biUnion]
        exact Or.inr ⟨y, hyKept,
          mem_rootedDescendants_of_adj_of_ne_root hT huDesc huy huv⟩))

/-- Removing the attachment root from the selected side gives the dual
boundary condition: every edge leaving `S \ {x}` ends at `x`. -/
theorem naturalVertices_sdiff_root_hasSingleOutsideBoundaryAttachment [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V}
    (kept : Finset V) (hkept : kept ⊆ children T r x) :
    HasSingleOutsideBoundaryAttachment T
      ((naturalVertices T r x kept : Set V) \ {x}) x := by
  intro u v huv hu hv
  have huS : u ∈ (naturalVertices T r x kept : Set V) := hu.1
  have hux : u ≠ x := by simpa using hu.2
  by_cases hvS : v ∈ (naturalVertices T r x kept : Set V)
  · by_contra hvx
    apply hv
    exact ⟨hvS, by simpa using hvx⟩
  · have huxEq := naturalVertices_hasSingleBoundaryAttachment hT kept hkept
      huv huS hvS
    exact (hux huxEq).elim

/-- The attachment root produced by the leaf form of Fact 7.9 is not an
ordinary leaf.  The non-leaf global root rules out the sole rooted exception. -/
theorem natural_root_not_leaf_of_eleven_leaves [Fintype V]
    {T : SimpleGraph V} (hT : T.IsTree) {r x : V}
    (hr : ¬IsLeaf T r) (l : ℕ) (hl : 0 < l)
    (kept : Finset V) (hkept : kept ⊆ children T r x)
    (hmany : 11 * l ≤ (leavesIn T (naturalVertices T r x kept)).card) :
    ¬IsLeaf T x := by
  classical
  intro hxLeaf
  have hxr : x ≠ r := by
    intro h
    exact hr (h ▸ hxLeaf)
  have hchildren := children_eq_empty_of_leaf_of_ne_root hT hxLeaf hxr
  have hkeptEmpty : kept = ∅ := by
    apply Finset.Subset.antisymm
    · rw [hchildren] at hkept
      exact hkept
    · exact Finset.empty_subset _
  subst kept
  have hnat : naturalVertices T r x (∅ : Finset V) = {x} := by
    simp [naturalVertices]
  have hone : (leavesIn T (naturalVertices T r x (∅ : Finset V))).card ≤ 1 := by
    rw [hnat]
    calc
      (leavesIn T {x}).card ≤ ({x} : Finset V).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 1 := Finset.card_singleton x
  omega

/-- Zhao Fact 7.9(2), in the exact numerical form used in Lemma 7.7.  The root
is chosen non-leaf (possible in the application, which has at least 33 leaves).
The selected natural subtree contains at least `11*l` and fewer than `22*l`
ordinary leaves, while at least `11*l` ordinary leaves remain outside it. -/
theorem fact79_leaf_natural_subtree [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V)
    (hr : ¬IsLeaf T r) (l : ℕ) (hl : 0 < l)
    (htotal : 33 * l ≤ (leaves T).card) :
    ∃ x kept U,
      kept ⊆ children T r x ∧
      U = naturalVertices T r x kept ∧
      IsNaturalVertexSet T r U ∧
      HasSingleBoundaryAttachment T (U : Set V) x ∧
      11 * l ≤ (leavesIn T U).card ∧
      (leavesIn T U).card < 22 * l ∧
      11 * l ≤ (leaves T \ U).card := by
  classical
  let q := 11 * l
  have hq : 0 < q := by simp [q]; omega
  have hqTwo : 2 ≤ q := by simp [q]; omega
  have hqTotal : q ≤ (leaves T).card := by
    simp only [q]
    omega
  obtain ⟨x, hxHeavy, hxSmall⟩ :=
    exists_leaf_heavy_with_small_children T r q hqTotal
  have hxNotLeaf : ¬IsLeaf T x := by
    intro hxLeaf
    have hxr : x ≠ r := by
      intro h
      exact hr (h ▸ hxLeaf)
    have hxOne :=
      card_leavesIn_rootedDescendants_le_one_of_leaf_of_ne_root hT hxLeaf hxr
    omega
  have hxSum :
      (leavesIn T (rootedDescendants T r x)).card =
        ∑ y ∈ children T r x,
          (leavesIn T (rootedDescendants T r y)).card :=
    card_leavesIn_rootedDescendants_eq_sum hT hxNotLeaf
  have hsumHeavy : q ≤ ∑ y ∈ children T r x,
      (leavesIn T (rootedDescendants T r y)).card := by
    rw [← hxSum]
    exact hxHeavy
  obtain ⟨kept, hkept, hkeptLower, hkeptUpper⟩ :=
    exists_subset_sum_in_half_open_interval q hq (children T r x)
      (fun y => (leavesIn T (rootedDescendants T r y)).card)
      hxSmall hsumHeavy
  let U := naturalVertices T r x kept
  have hcardU : (leavesIn T U).card =
      ∑ y ∈ kept, (leavesIn T (rootedDescendants T r y)).card := by
    exact card_leavesIn_naturalVertices_eq_sum hT hxNotLeaf kept hkept
  have hUlower : 11 * l ≤ (leavesIn T U).card := by
    rw [hcardU]
    simpa [q] using hkeptLower
  have hUupper : (leavesIn T U).card < 22 * l := by
    rw [hcardU]
    have := hkeptUpper
    simp only [q] at this
    omega
  have hleafSub : leavesIn T U ⊆ leaves T := by
    intro z hz
    exact mem_leaves.mpr (mem_leavesIn.mp hz).2
  have hdiff : leaves T \ U = leaves T \ leavesIn T U := by
    ext z
    simp only [Finset.mem_sdiff, mem_leaves, mem_leavesIn]
    tauto
  have houtCard : (leaves T \ U).card =
      (leaves T).card - (leavesIn T U).card := by
    rw [hdiff, Finset.card_sdiff_of_subset hleafSub]
  have houtLower : 11 * l ≤ (leaves T \ U).card := by
    rw [houtCard]
    omega
  refine ⟨x, kept, U, hkept, rfl, ?_, ?_, hUlower, hUupper, houtLower⟩
  · exact ⟨x, kept, hkept, rfl⟩
  · exact naturalVertices_hasSingleBoundaryAttachment hT kept hkept

end Erdos547b.Lemma77Rooted

#print axioms Erdos547b.Lemma77Rooted.exists_subset_sum_in_half_open_interval
#print axioms Erdos547b.Lemma77Rooted.exists_child_of_mem_rootedDescendants
#print axioms Erdos547b.Lemma77Rooted.naturalVertices_hasSingleBoundaryAttachment
#print axioms Erdos547b.Lemma77Rooted.naturalVertices_sdiff_root_hasSingleOutsideBoundaryAttachment
#print axioms Erdos547b.Lemma77Rooted.natural_root_not_leaf_of_eleven_leaves
#print axioms Erdos547b.Lemma77Rooted.fact79_leaf_natural_subtree

/-!
The natural-subtree flip algebra in Zhao's Lemma 7.7, Case (b).  It is
separated from Fact 7.9: the input `NaturalSplit` records precisely the
boundary and leaf facts delivered by the chosen natural subtree.
-/

namespace Erdos547b.ZhaoLemma77HardCase

open Finset SimpleGraph
open scoped Classical

noncomputable section

universe u
variable {V : Type u}

@[simp] theorem mem_leavesIn' [Fintype V] {T : SimpleGraph V}
    {U : Finset V} {x : V} : x ∈ leavesIn T U ↔ x ∈ U ∧ IsLeaf T x := by
  simp [leavesIn]

def flipFirst (E O S : Finset V) : Finset V :=
  (E \ S) ∪ (O ∩ S)

def flipSecond (E O S : Finset V) : Finset V :=
  (O \ S) ∪ (E ∩ S)

theorem flip_union (E O S : Finset V) :
    flipFirst E O S ∪ flipSecond E O S = E ∪ O := by
  ext x
  simp only [flipFirst, flipSecond, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_inter]
  tauto

theorem flip_disjoint {E O S : Finset V} (hEO : Disjoint E O) :
    Disjoint (flipFirst E O S) (flipSecond E O S) := by
  rw [Finset.disjoint_left] at hEO ⊢
  intro x hx₁ hx₂
  simp only [flipFirst, flipSecond, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_inter] at hx₁ hx₂
  rcases hx₁ with hxE | hxO <;> rcases hx₂ with hxO' | hxE'
  · exact hEO hxE.1 hxO'.1
  · exact hxE.2 hxE'.2
  · exact hxO'.2 hxO.2
  · exact hEO hxE'.1 hxO.1

theorem card_flipFirst {E O S : Finset V} (hEO : Disjoint E O) :
    (flipFirst E O S).card =
      E.card - (E ∩ S).card + (O ∩ S).card := by
  have hd : Disjoint (E \ S) (O ∩ S) := by
    rw [Finset.disjoint_left] at hEO ⊢
    intro x hxE hxO
    exact hEO (Finset.mem_sdiff.mp hxE).1 (Finset.mem_inter.mp hxO).1
  rw [flipFirst, Finset.card_union_of_disjoint hd, Finset.card_sdiff,
    Finset.inter_comm S E]

theorem card_flipSecond {E O S : Finset V} (hEO : Disjoint E O) :
    (flipSecond E O S).card =
      O.card - (O ∩ S).card + (E ∩ S).card := by
  have hd : Disjoint (O \ S) (E ∩ S) := by
    rw [Finset.disjoint_left] at hEO ⊢
    intro x hxO hxE
    exact hEO (Finset.mem_inter.mp hxE).1 (Finset.mem_sdiff.mp hxO).1
  rw [flipSecond, Finset.card_union_of_disjoint hd, Finset.card_sdiff,
    Finset.inter_comm S O]

theorem card_flip_difference {E O S : Finset V} (hEO : Disjoint E O) :
    ((flipFirst E O S).card : ℤ) - (flipSecond E O S).card =
      ((E.card : ℤ) - O.card) +
        2 * ((O ∩ S).card - (E ∩ S).card) := by
  rw [card_flipFirst hEO, card_flipSecond hEO]
  have hES : (E ∩ S).card ≤ E.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hOS : (O ∩ S).card ≤ O.card :=
    Finset.card_le_card Finset.inter_subset_left
  push_cast [Nat.cast_sub hES, Nat.cast_sub hOS]
  omega

theorem flipSecond_isIndepSet {T : SimpleGraph V} {E O S : Finset V}
    (hE : T.IsIndepSet (E : Set V)) (hO : T.IsIndepSet (O : Set V))
    (hcross : ∀ ⦃e o : V⦄, e ∈ E → e ∈ S → o ∈ O → o ∉ S → ¬T.Adj e o) :
    T.IsIndepSet (flipSecond E O S : Set V) := by
  rw [T.isIndepSet_iff] at hE hO ⊢
  intro x hx y hy hxy
  change x ∈ flipSecond E O S at hx
  change y ∈ flipSecond E O S at hy
  simp only [flipSecond, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at hx hy
  rcases hx with hxO | hxE <;> rcases hy with hyO | hyE
  · exact hO hxO.1 hyO.1 hxy
  · intro h
    exact hcross hyE.1 hyE.2 hxO.1 hxO.2 h.symm
  · exact hcross hxE.1 hxE.2 hyO.1 hyO.2
  · exact hE hxE.1 hyE.1 hxy

structure NaturalSplit [Fintype V] (l : ℕ) (T : SimpleGraph V)
    (E O S : Finset V) (r : V) : Prop where
  root_mem : r ∈ S
  root_not_leaf : ¬ IsLeaf T r
  inside_boundary : ∀ ⦃x y : V⦄, T.Adj x y → x ∈ S → y ∉ S → x = r
  outside_boundary_after_delete_root : ∀ ⦃x y : V⦄, T.Adj x y →
    x ∈ S \ {r} → y ∉ S \ {r} → y = r
  inner_odd_leaves : 6 * l + 1 ≤ (leavesIn T (O ∩ S)).card
  outer_odd_leaves : 6 * l + 1 ≤ (leavesIn T (O \ S)).card

structure IsIdealPartition [Fintype V] (l : ℕ) (T : SimpleGraph V)
    (U₁ U₂ : Finset V) : Prop where
  partition : Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = Finset.univ
  card_le : U₁.card ≤ U₂.card
  right_independent : T.IsIndepSet (U₂ : Set V)
  left_leaves : 5 * l ≤ (leavesIn T U₁).card
  right_leaves : 2 * l ≤ (leavesIn T U₂).card

/-- Everything in a near-ideal partition except the final special degree-two
leaf.  Zhao's Fact-6.9 pruning argument supplies that leaf or turns this core
into an ideal partition by the three-vertex flip. -/
structure NearIdealCore [Fintype V] (l n : ℕ) (T : SimpleGraph V)
    (U₁ U₂ : Finset V) : Prop where
  partition : Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = Finset.univ
  n_even : Even n
  left_card : U₁.card = n / 2 + 1
  right_card : U₂.card = n / 2
  right_independent : T.IsIndepSet (U₂ : Set V)
  left_leaves : 6 * l + 1 ≤ (leavesIn T U₁).card
  right_leaves : 6 * l + 1 ≤ (leavesIn T U₂).card

theorem leavesIn_mono [Fintype V] (T : SimpleGraph V) {A B : Finset V}
    (hAB : A ⊆ B) : leavesIn T A ⊆ leavesIn T B := by
  intro x hx
  have h := mem_leavesIn'.mp hx
  exact mem_leavesIn'.mpr ⟨hAB h.1, h.2⟩

theorem card_leavesIn_flipFirst_of_inner [Fintype V]
    (T : SimpleGraph V) (E O S : Finset V) :
    (leavesIn T (O ∩ S)).card ≤ (leavesIn T (flipFirst E O S)).card := by
  apply Finset.card_le_card
  apply leavesIn_mono T
  exact Finset.subset_union_right

theorem card_leavesIn_flipSecond_of_outer [Fintype V]
    (T : SimpleGraph V) (E O S : Finset V) :
    (leavesIn T (O \ S)).card ≤ (leavesIn T (flipSecond E O S)).card := by
  apply Finset.card_le_card
  apply leavesIn_mono T
  exact Finset.subset_union_left

theorem indep_of_bipartition_left [Fintype V] {T : SimpleGraph V}
    {E O : Finset V} (hpart : IsProperBipartition T E O) :
    T.IsIndepSet (E : Set V) := by
  rw [T.isIndepSet_iff]
  intro x hx y hy hxy hAdj
  have hyO := hpart.bipartite.mem_of_mem_adj hx hAdj
  exact Set.disjoint_left.mp hpart.bipartite.disjoint hy hyO

theorem indep_of_bipartition_right [Fintype V] {T : SimpleGraph V}
    {E O : Finset V} (hpart : IsProperBipartition T E O) :
    T.IsIndepSet (O : Set V) := by
  exact indep_of_bipartition_left
    { bipartite := hpart.bipartite.symm
      cover := by simpa [Set.union_comm] using hpart.cover
      left_nonempty := hpart.right_nonempty
      right_nonempty := hpart.left_nonempty }

theorem flipSecond_indep_of_inside_boundary [Fintype V]
    {T : SimpleGraph V} {E O S : Finset V} {r : V}
    (hpart : IsProperBipartition T E O)
    (hboundary : ∀ ⦃x y : V⦄, T.Adj x y → x ∈ S → y ∉ S → x = r)
    (hrE : r ∉ E) : T.IsIndepSet (flipSecond E O S : Set V) := by
  apply flipSecond_isIndepSet (indep_of_bipartition_left hpart)
    (indep_of_bipartition_right hpart)
  intro e o heE heS hoO hoS heo
  exact hrE ((hboundary heo heS hoS) ▸ heE)

theorem flipSecond_indep_of_outside_boundary [Fintype V]
    {T : SimpleGraph V} {E O S : Finset V} {r : V}
    (hpart : IsProperBipartition T E O)
    (hboundary : ∀ ⦃x y : V⦄, T.Adj x y → x ∈ S → y ∉ S → y = r)
    (hrO : r ∉ O) : T.IsIndepSet (flipSecond E O S : Set V) := by
  apply flipSecond_isIndepSet (indep_of_bipartition_left hpart)
    (indep_of_bipartition_right hpart)
  intro e o heE heS hoO hoS heo
  exact hrO ((hboundary heo heS hoS) ▸ hoO)

theorem naturalSplit_inner_leaves_after_delete_root [Fintype V]
    {l : ℕ} {T : SimpleGraph V} {E O S : Finset V} {r : V}
    (h : NaturalSplit l T E O S r) :
    6 * l + 1 ≤ (leavesIn T (O ∩ (S \ {r}))).card := by
  apply h.inner_odd_leaves.trans
  apply Finset.card_le_card
  intro x hx
  have hxp := mem_leavesIn'.mp hx
  apply mem_leavesIn'.mpr
  refine ⟨?_, hxp.2⟩
  have hxOS := Finset.mem_inter.mp hxp.1
  apply Finset.mem_inter.mpr
  refine ⟨hxOS.1, Finset.mem_sdiff.mpr ⟨hxOS.2, ?_⟩⟩
  intro hxr
  have : x = r := by simpa using hxr
  subst x
  exact h.root_not_leaf hxp.2

theorem naturalSplit_outer_leaves_after_delete_root [Fintype V]
    {l : ℕ} {T : SimpleGraph V} {E O S : Finset V} {r : V}
    (h : NaturalSplit l T E O S r) :
    6 * l + 1 ≤ (leavesIn T (O \ (S \ {r}))).card := by
  apply h.outer_odd_leaves.trans
  apply Finset.card_le_card
  apply leavesIn_mono T
  intro x hx
  have hx' := Finset.mem_sdiff.mp hx
  exact Finset.mem_sdiff.mpr ⟨hx'.1, fun hxS0 => hx'.2 (Finset.mem_sdiff.mp hxS0).1⟩

theorem flipped_partition [Fintype V] {T : SimpleGraph V}
    {E O S : Finset V} (hpart : IsProperBipartition T E O) :
    Disjoint (flipFirst E O S) (flipSecond E O S) ∧
      flipFirst E O S ∪ flipSecond E O S = Finset.univ := by
  have hdisj : Disjoint E O := Finset.disjoint_coe.mp hpart.bipartite.disjoint
  refine ⟨flip_disjoint hdisj, ?_⟩
  rw [flip_union]
  ext x
  have hx := Set.ext_iff.mp hpart.cover x
  simpa using hx

theorem nearCore_of_succ [Fintype V] {l n : ℕ} {T : SimpleGraph V}
    {U₁ U₂ : Finset V}
    (hcardV : Fintype.card V = n + 1)
    (hpart : Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = Finset.univ)
    (hsucc : U₁.card = U₂.card + 1)
    (hind : T.IsIndepSet (U₂ : Set V))
    (hl₁ : 6 * l + 1 ≤ (leavesIn T U₁).card)
    (hl₂ : 6 * l + 1 ≤ (leavesIn T U₂).card) :
    NearIdealCore l n T U₁ U₂ := by
  have hsum : U₁.card + U₂.card = n + 1 := by
    rw [← hcardV, ← Finset.card_univ, ← hpart.2,
      Finset.card_union_of_disjoint hpart.1]
  have hn : n = 2 * U₂.card := by omega
  refine
    { partition := hpart
      n_even := ⟨U₂.card, by omega⟩
      left_card := by omega
      right_card := by omega
      right_independent := hind
      left_leaves := hl₁
      right_leaves := hl₂ }

/-- The full nonexceptional flip calculation and the exact parity-one
exceptional output in Zhao's Case (b). -/
theorem case_b_ideal_or_nearCore [Fintype V]
    (l n : ℕ) (T : SimpleGraph V) (E O S : Finset V) (r : V)
    (hcardV : Fintype.card V = n + 1)
    (hpart : IsProperBipartition T E O) (hEO : E.card ≤ O.card)
    (hgap : O.card - E.card < 2 * l + 1)
    (hsplit : NaturalSplit l T E O S r) :
    (∃ U₁ U₂, IsIdealPartition l T U₁ U₂) ∨
      ((∃ U₁ U₂, NearIdealCore l n T U₁ U₂) ∧
        ∀ z ∈ leavesIn T O, ∀ y, T.Adj y z → y ≠ r →
          ∃ U₁ U₂, NearIdealCore l n T U₁ U₂ ∧ z ∈ U₁ ∧ y ∈ U₂) := by
  classical
  have hdisj : Disjoint E O := Finset.disjoint_coe.mp hpart.bipartite.disjoint
  have hcover : E ∪ O = Finset.univ := by
    ext x
    have hx := Set.ext_iff.mp hpart.cover x
    simpa using hx
  have hrSide : r ∈ E ∨ r ∈ O := by
    have : r ∈ E ∪ O := by rw [hcover]; simp
    simpa using this
  have hEind := indep_of_bipartition_left hpart
  have hOind := indep_of_bipartition_right hpart
  let g : ℤ := (O.card : ℤ) - E.card
  let d : ℤ := ((O ∩ S).card : ℤ) - (E ∩ S).card
  have hgNonneg : 0 ≤ g := by simp only [g]; omega
  rcases hrSide with hrE | hrO
  · have hrO : r ∉ O := fun h => Finset.disjoint_left.mp hdisj hrE h
    by_cases hfirst : g ≤ 2 * d
    · left
      let U₁ := flipSecond E O S
      let U₂ := flipFirst E O S
      refine ⟨U₁, U₂, ?_⟩
      have hdiff := card_flip_difference (S := S) hdisj
      have hcard : U₁.card ≤ U₂.card := by
        dsimp only [U₁, U₂]
        simp only [g, d] at hfirst
        omega
      have hind : T.IsIndepSet (U₂ : Set V) := by
        dsimp only [U₂]
        exact flipSecond_indep_of_inside_boundary
          (T := T) (E := O) (O := E) (S := S)
          { bipartite := hpart.bipartite.symm
            cover := by simpa [Set.union_comm] using hpart.cover
            left_nonempty := hpart.right_nonempty
            right_nonempty := hpart.left_nonempty }
          hsplit.inside_boundary hrO
      refine
        { partition := ⟨(flip_disjoint hdisj).symm, by rw [Finset.union_comm, flip_union, hcover]⟩
          card_le := hcard
          right_independent := hind
          left_leaves := ?_
          right_leaves := ?_ }
      · exact (hsplit.outer_odd_leaves.trans
          (card_leavesIn_flipSecond_of_outer T E O S)).trans' (by omega)
      · exact (hsplit.inner_odd_leaves.trans
          (card_leavesIn_flipFirst_of_inner T E O S)).trans' (by omega)
    · by_cases hsecond : 2 * d + 2 ≤ g
      · left
        let S₀ := S \ {r}
        let U₁ := flipFirst E O S₀
        let U₂ := flipSecond E O S₀
        refine ⟨U₁, U₂, ?_⟩
        have hOeq : O ∩ S₀ = O ∩ S := by
          ext x
          simp only [S₀, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
          constructor
          · tauto
          · intro hx
            refine ⟨hx.1, hx.2, ?_⟩
            intro hxr
            subst x
            exact hrO hx.1
        have hEcard : (E ∩ S₀).card + 1 = (E ∩ S).card := by
          have hrES : r ∈ E ∩ S := Finset.mem_inter.mpr ⟨hrE, hsplit.root_mem⟩
          have heq : E ∩ S₀ = (E ∩ S).erase r := by
            ext x
            simp only [S₀, Finset.mem_inter, Finset.mem_sdiff,
              Finset.mem_singleton, Finset.mem_erase]
            tauto
          rw [heq]
          exact Finset.card_erase_add_one hrES
        have hdiff := card_flip_difference (S := S₀) hdisj
        have hcard : U₁.card ≤ U₂.card := by
          dsimp only [U₁, U₂]
          simp only [g, d] at hsecond
          rw [hOeq] at hdiff
          omega
        refine
          { partition := flipped_partition hpart
            card_le := hcard
            right_independent := flipSecond_indep_of_outside_boundary hpart
              hsplit.outside_boundary_after_delete_root hrO
            left_leaves := ?_
            right_leaves := ?_ }
        · exact (naturalSplit_inner_leaves_after_delete_root hsplit).trans
            (card_leavesIn_flipFirst_of_inner T E O S₀) |>.trans' (by omega)
        · exact (naturalSplit_outer_leaves_after_delete_root hsplit).trans
            (card_leavesIn_flipSecond_of_outer T E O S₀) |>.trans' (by omega)
      · right
        let U₁ := flipSecond E O S
        let U₂ := flipFirst E O S
        have hmain : NearIdealCore l n T U₁ U₂ := by
          have hdiff := card_flip_difference (S := S) hdisj
          have hsucc : U₁.card = U₂.card + 1 := by
            dsimp only [U₁, U₂]
            simp only [g, d] at hfirst hsecond
            omega
          apply nearCore_of_succ hcardV
            ⟨(flip_disjoint hdisj).symm, by rw [Finset.union_comm, flip_union, hcover]⟩ hsucc
          · exact flipSecond_indep_of_inside_boundary
              (T := T) (E := O) (O := E) (S := S)
              { bipartite := hpart.bipartite.symm
                cover := by simpa [Set.union_comm] using hpart.cover
                left_nonempty := hpart.right_nonempty
                right_nonempty := hpart.left_nonempty }
              hsplit.inside_boundary hrO
          · exact hsplit.outer_odd_leaves.trans
              (card_leavesIn_flipSecond_of_outer T E O S)
          · exact hsplit.inner_odd_leaves.trans
              (card_leavesIn_flipFirst_of_inner T E O S)
        let S₀ := S \ {r}
        let U₁' := flipFirst E O S₀
        let U₂' := flipSecond E O S₀
        have hOeq : O ∩ S₀ = O ∩ S := by
          ext x
          simp only [S₀, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
          constructor
          · tauto
          · intro hx
            refine ⟨hx.1, hx.2, ?_⟩
            intro hxr
            subst x
            exact hrO hx.1
        have hEcard : (E ∩ S₀).card + 1 = (E ∩ S).card := by
          have hrES : r ∈ E ∩ S := Finset.mem_inter.mpr ⟨hrE, hsplit.root_mem⟩
          have heq : E ∩ S₀ = (E ∩ S).erase r := by
            ext x
            simp only [S₀, Finset.mem_inter, Finset.mem_sdiff,
              Finset.mem_singleton, Finset.mem_erase]
            tauto
          rw [heq]
          exact Finset.card_erase_add_one hrES
        have halt : NearIdealCore l n T U₁' U₂' := by
          have hdiff' := card_flip_difference (S := S₀) hdisj
          have hsucc' : U₁'.card = U₂'.card + 1 := by
            dsimp only [U₁', U₂']
            simp only [g, d] at hfirst hsecond
            rw [hOeq] at hdiff'
            omega
          apply nearCore_of_succ hcardV (flipped_partition hpart) hsucc'
          · exact flipSecond_indep_of_outside_boundary hpart
              hsplit.outside_boundary_after_delete_root hrO
          · exact (naturalSplit_inner_leaves_after_delete_root hsplit).trans
              (card_leavesIn_flipFirst_of_inner T E O S₀)
          · exact (naturalSplit_outer_leaves_after_delete_root hsplit).trans
              (card_leavesIn_flipSecond_of_outer T E O S₀)
        refine ⟨⟨U₁, U₂, hmain⟩, ?_⟩
        intro z hz y hyz hyr
        have hzParts := mem_leavesIn'.mp hz
        have hzO : z ∈ O := hzParts.1
        have hzLeaf : IsLeaf T z := hzParts.2
        have hyE : y ∈ E := hpart.bipartite.mem_of_mem_adj' hzO hyz
        have hzr : z ≠ r := by
          intro hzr
          exact hsplit.root_not_leaf (hzr ▸ hzLeaf)
        by_cases hzS : z ∈ S
        · refine ⟨U₁', U₂', halt, ?_, ?_⟩
          · apply Finset.mem_union.mpr
            right
            exact Finset.mem_inter.mpr ⟨hzO,
              Finset.mem_sdiff.mpr ⟨hzS, by simpa using hzr⟩⟩
          · apply Finset.mem_union.mpr
            right
            apply Finset.mem_inter.mpr
            refine ⟨hyE, Finset.mem_sdiff.mpr ⟨?_, by simpa using hyr⟩⟩
            by_contra hyS
            exact hzr (hsplit.inside_boundary hyz.symm hzS hyS)
        · refine ⟨U₁, U₂, hmain, ?_, ?_⟩
          · apply Finset.mem_union.mpr
            left
            exact Finset.mem_sdiff.mpr ⟨hzO, hzS⟩
          · apply Finset.mem_union.mpr
            left
            apply Finset.mem_sdiff.mpr
            refine ⟨hyE, ?_⟩
            intro hyS
            exact hyr (hsplit.inside_boundary hyz hyS hzS)
  · have hrE' : r ∉ E := fun h => Finset.disjoint_left.mp hdisj h hrO
    by_cases hfirst : 2 * d ≤ g
    · left
      let U₁ := flipFirst E O S
      let U₂ := flipSecond E O S
      refine ⟨U₁, U₂, ?_⟩
      have hdiff := card_flip_difference (S := S) hdisj
      refine
        { partition := flipped_partition hpart
          card_le := by
            dsimp only [U₁, U₂]
            simp only [g, d] at hfirst
            omega
          right_independent := flipSecond_indep_of_inside_boundary hpart
            hsplit.inside_boundary hrE'
          left_leaves := ?_
          right_leaves := ?_ }
      · exact (hsplit.inner_odd_leaves.trans
          (card_leavesIn_flipFirst_of_inner T E O S)).trans' (by omega)
      · exact (hsplit.outer_odd_leaves.trans
          (card_leavesIn_flipSecond_of_outer T E O S)).trans' (by omega)
    · by_cases hsecond : g + 2 ≤ 2 * d
      · left
        let S₀ := S \ {r}
        let U₁ := flipSecond E O S₀
        let U₂ := flipFirst E O S₀
        refine ⟨U₁, U₂, ?_⟩
        have hEeq : E ∩ S₀ = E ∩ S := by
          ext x
          simp only [S₀, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
          constructor
          · tauto
          · intro hx
            refine ⟨hx.1, hx.2, ?_⟩
            intro hxr
            subst x
            exact hrE' hx.1
        have hOcard : (O ∩ S₀).card + 1 = (O ∩ S).card := by
          have hrOS : r ∈ O ∩ S := Finset.mem_inter.mpr ⟨hrO, hsplit.root_mem⟩
          have heq : O ∩ S₀ = (O ∩ S).erase r := by
            ext x
            simp only [S₀, Finset.mem_inter, Finset.mem_sdiff,
              Finset.mem_singleton, Finset.mem_erase]
            tauto
          rw [heq]
          exact Finset.card_erase_add_one hrOS
        have hdiff := card_flip_difference (S := S₀) hdisj
        refine
          { partition := ⟨(flip_disjoint hdisj).symm,
              by rw [Finset.union_comm, flip_union, hcover]⟩
            card_le := by
              dsimp only [U₁, U₂]
              simp only [g, d] at hsecond
              rw [hEeq] at hdiff
              omega
            right_independent := by
              dsimp only [U₂]
              exact flipSecond_indep_of_outside_boundary
                (T := T) (E := O) (O := E) (S := S₀)
                { bipartite := hpart.bipartite.symm
                  cover := by simpa [Set.union_comm] using hpart.cover
                  left_nonempty := hpart.right_nonempty
                  right_nonempty := hpart.left_nonempty }
                hsplit.outside_boundary_after_delete_root hrE'
            left_leaves := ?_
            right_leaves := ?_ }
        · exact (naturalSplit_outer_leaves_after_delete_root hsplit).trans
            (card_leavesIn_flipSecond_of_outer T E O S₀) |>.trans' (by omega)
        · exact (naturalSplit_inner_leaves_after_delete_root hsplit).trans
            (card_leavesIn_flipFirst_of_inner T E O S₀) |>.trans' (by omega)
      · right
        let U₁ := flipFirst E O S
        let U₂ := flipSecond E O S
        have hmain : NearIdealCore l n T U₁ U₂ := by
          have hdiff := card_flip_difference (S := S) hdisj
          have hsucc : U₁.card = U₂.card + 1 := by
            dsimp only [U₁, U₂]
            simp only [g, d] at hfirst hsecond
            omega
          apply nearCore_of_succ hcardV (flipped_partition hpart) hsucc
          · exact flipSecond_indep_of_inside_boundary hpart hsplit.inside_boundary hrE'
          · exact hsplit.inner_odd_leaves.trans
              (card_leavesIn_flipFirst_of_inner T E O S)
          · exact hsplit.outer_odd_leaves.trans
              (card_leavesIn_flipSecond_of_outer T E O S)
        let S₀ := S \ {r}
        let U₁' := flipSecond E O S₀
        let U₂' := flipFirst E O S₀
        have hEeq : E ∩ S₀ = E ∩ S := by
          ext x
          simp only [S₀, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
          constructor
          · tauto
          · intro hx
            refine ⟨hx.1, hx.2, ?_⟩
            intro hxr
            subst x
            exact hrE' hx.1
        have hOcard : (O ∩ S₀).card + 1 = (O ∩ S).card := by
          have hrOS : r ∈ O ∩ S := Finset.mem_inter.mpr ⟨hrO, hsplit.root_mem⟩
          have heq : O ∩ S₀ = (O ∩ S).erase r := by
            ext x
            simp only [S₀, Finset.mem_inter, Finset.mem_sdiff,
              Finset.mem_singleton, Finset.mem_erase]
            tauto
          rw [heq]
          exact Finset.card_erase_add_one hrOS
        have halt : NearIdealCore l n T U₁' U₂' := by
          have hdiff' := card_flip_difference (S := S₀) hdisj
          have hsucc' : U₁'.card = U₂'.card + 1 := by
            dsimp only [U₁', U₂']
            simp only [g, d] at hfirst hsecond
            rw [hEeq] at hdiff'
            omega
          apply nearCore_of_succ hcardV
            ⟨(flip_disjoint hdisj).symm, by rw [Finset.union_comm, flip_union, hcover]⟩ hsucc'
          · exact flipSecond_indep_of_outside_boundary
              (T := T) (E := O) (O := E) (S := S₀)
              { bipartite := hpart.bipartite.symm
                cover := by simpa [Set.union_comm] using hpart.cover
                left_nonempty := hpart.right_nonempty
                right_nonempty := hpart.left_nonempty }
              hsplit.outside_boundary_after_delete_root hrE'
          · exact (naturalSplit_outer_leaves_after_delete_root hsplit).trans
              (card_leavesIn_flipSecond_of_outer T E O S₀)
          · exact (naturalSplit_inner_leaves_after_delete_root hsplit).trans
              (card_leavesIn_flipFirst_of_inner T E O S₀)
        refine ⟨⟨U₁, U₂, hmain⟩, ?_⟩
        intro z hz y hyz hyr
        have hzParts := mem_leavesIn'.mp hz
        have hzO : z ∈ O := hzParts.1
        have hzLeaf : IsLeaf T z := hzParts.2
        have hyE : y ∈ E := hpart.bipartite.mem_of_mem_adj' hzO hyz
        have hzr : z ≠ r := by
          intro hzr
          exact hsplit.root_not_leaf (hzr ▸ hzLeaf)
        by_cases hzS : z ∈ S
        · refine ⟨U₁, U₂, hmain, ?_, ?_⟩
          · apply Finset.mem_union.mpr
            right
            exact Finset.mem_inter.mpr ⟨hzO, hzS⟩
          · apply Finset.mem_union.mpr
            right
            apply Finset.mem_inter.mpr
            refine ⟨hyE, ?_⟩
            by_contra hyS
            exact hzr (hsplit.inside_boundary hyz.symm hzS hyS)
        · refine ⟨U₁', U₂', halt, ?_, ?_⟩
          · apply Finset.mem_union.mpr
            left
            exact Finset.mem_sdiff.mpr ⟨hzO,
              fun hzS₀ => hzS (Finset.mem_sdiff.mp hzS₀).1⟩
          · apply Finset.mem_union.mpr
            left
            apply Finset.mem_sdiff.mpr
            refine ⟨hyE, ?_⟩
            intro hyS₀
            have hzEq := hsplit.outside_boundary_after_delete_root hyz
              hyS₀ (by
                intro hzS₀
                exact hzS (Finset.mem_sdiff.mp hzS₀).1)
            exact hzr hzEq

end

end Erdos547b.ZhaoLemma77HardCase

#print axioms Erdos547b.ZhaoLemma77HardCase.case_b_ideal_or_nearCore

/-!
The exceptional conversion in Zhao, Lemma 7.7 (EJC 18 (2011), P27,
pp. 46--47).  This file is kept standalone so that it can be merged into the
main Lemma 7.7 development without importing scratch modules.
-/

namespace Erdos547b.ZhaoLemma77Rooted

open Finset SimpleGraph
open scoped Classical

noncomputable section

universe u

variable {V : Type u}

def IsLeaf (T : SimpleGraph V) [T.LocallyFinite] (v : V) : Prop :=
  T.degree v = 1

noncomputable def leavesIn [Fintype V] (T : SimpleGraph V) [T.LocallyFinite]
    (U : Finset V) : Finset V :=
  U.filter (IsLeaf T)

@[simp] theorem mem_leavesIn [Fintype V] {T : SimpleGraph V} [T.LocallyFinite]
    {U : Finset V} {v : V} :
    v ∈ leavesIn T U ↔ v ∈ U ∧ IsLeaf T v := by
  simp [leavesIn]

structure IsIdealPartition [Fintype V] (l : ℕ) (T : SimpleGraph V)
    (U₁ U₂ : Finset V) : Prop where
  partition : Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = Finset.univ
  card_le : U₁.card ≤ U₂.card
  right_independent : T.IsIndepSet (U₂ : Set V)
  left_leaves : 5 * l ≤ (leavesIn T U₁).card
  right_leaves : 2 * l ≤ (leavesIn T U₂).card

structure IsNearIdealPartition [Fintype V] (l n : ℕ) (T : SimpleGraph V)
    (U₁ U₂ : Finset V) : Prop where
  partition : Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = Finset.univ
  n_even : Even n
  left_card : U₁.card = n / 2 + 1
  right_card : U₂.card = n / 2
  right_independent : T.IsIndepSet (U₂ : Set V)
  left_leaves : 5 * l ≤ (leavesIn T U₁).card
  right_leaves : 2 * l ≤ (leavesIn T U₂).card
  special_leaf : ∃ z ∈ U₁, IsLeaf T z ∧
    ∃ y ∈ U₂, T.Adj y z ∧ T.degree y = 2

/-- `y` has exactly one neighbour which is not a leaf.  This is the
intermediate conclusion Zhao obtains from Fact 6.9 in the exceptional parity
case. -/
def HasExactlyOneNonleafNeighbor [Fintype V] (T : SimpleGraph V) (y : V) : Prop :=
  ∃! x : V, T.Adj y x ∧ ¬ IsLeaf T x

/-- The nonleaf neighbours of a vertex. -/
noncomputable def nonleafNeighbors [Fintype V] (T : SimpleGraph V)
    (y : V) : Finset V :=
  (T.neighborFinset y).filter fun x => ¬ IsLeaf T x

/-- The leaf neighbours of a vertex. -/
noncomputable def leafNeighbors [Fintype V] (T : SimpleGraph V)
    (y : V) : Finset V :=
  (T.neighborFinset y).filter (IsLeaf T)

@[simp] theorem mem_nonleafNeighbors [Fintype V] {T : SimpleGraph V} {x y : V} :
    x ∈ nonleafNeighbors T y ↔ T.Adj y x ∧ ¬ IsLeaf T x := by
  simp [nonleafNeighbors]

@[simp] theorem mem_leafNeighbors [Fintype V] {T : SimpleGraph V} {x y : V} :
    x ∈ leafNeighbors T y ↔ T.Adj y x ∧ IsLeaf T x := by
  simp [leafNeighbors]

theorem card_leafNeighbors_add_card_nonleafNeighbors [Fintype V]
    (T : SimpleGraph V) (y : V) :
    (leafNeighbors T y).card + (nonleafNeighbors T y).card = T.degree y := by
  classical
  rw [← T.card_neighborFinset_eq_degree y]
  have hu : leafNeighbors T y ∪ nonleafNeighbors T y = T.neighborFinset y := by
    ext x
    simp only [Finset.mem_union, mem_leafNeighbors, mem_nonleafNeighbors,
      SimpleGraph.mem_neighborFinset]
    constructor
    · aesop
    · intro hxy
      by_cases hx : IsLeaf T x
      · exact Or.inl ⟨hxy, hx⟩
      · exact Or.inr ⟨hxy, hx⟩
  have hd : Disjoint (leafNeighbors T y) (nonleafNeighbors T y) := by
    rw [Finset.disjoint_left]
    intro x hxL hxN
    exact (mem_nonleafNeighbors.mp hxN).2 (mem_leafNeighbors.mp hxL).2
  rw [← Finset.card_union_of_disjoint hd, hu]

/-- If a nonleaf vertex of degree other than two has at most one nonleaf
neighbour and is adjacent to a specified leaf, then it has another leaf
neighbour.  This includes the zero-nonleaf-neighbour case omitted by the
paper's `exactly one` phrasing. -/
theorem exists_second_leaf_neighbor_of_card_nonleaf_le_one [Fintype V]
    (T : SimpleGraph V) {y z : V}
    (hz : IsLeaf T z) (hyz : T.Adj y z) (hyNotLeaf : ¬ IsLeaf T y)
    (hFew : (nonleafNeighbors T y).card ≤ 1)
    (hyDegree : T.degree y ≠ 2) :
    ∃ z' : V, z' ≠ z ∧ T.Adj y z' ∧ IsLeaf T z' := by
  classical
  have hdegPos : 0 < T.degree y :=
    (T.degree_pos_iff_exists_adj y).mpr ⟨z, hyz⟩
  have hdegThree : 3 ≤ T.degree y := by
    have hneOne : T.degree y ≠ 1 := hyNotLeaf
    omega
  have hsplit := card_leafNeighbors_add_card_nonleafNeighbors T y
  have hleafTwo : 2 ≤ (leafNeighbors T y).card := by omega
  have hzMem : z ∈ leafNeighbors T y := mem_leafNeighbors.mpr ⟨hyz, hz⟩
  have hremove : 0 < (leafNeighbors T y \ {z}).card := by
    rw [Finset.card_sdiff_of_subset (by simpa using hzMem)]
    simp only [Finset.card_singleton]
    omega
  obtain ⟨z', hz'Mem⟩ := Finset.card_pos.mp hremove
  have hz'Parts := Finset.mem_sdiff.mp hz'Mem
  have hz'Leaf := mem_leafNeighbors.mp hz'Parts.1
  exact ⟨z', by simpa using hz'Parts.2, hz'Leaf.1, hz'Leaf.2⟩

/-- A degree-at-least-three vertex with exactly one nonleaf neighbour and one
specified leaf neighbour has a second, distinct leaf neighbour. -/
theorem exists_second_leaf_neighbor [Fintype V]
    (T : SimpleGraph V) {y z : V}
    (hz : IsLeaf T z) (hyz : T.Adj y z)
    (hyNonleaf : HasExactlyOneNonleafNeighbor T y)
    (hyDegree : T.degree y ≠ 2) :
    ∃ z' : V, z' ≠ z ∧ T.Adj y z' ∧ IsLeaf T z' := by
  classical
  obtain ⟨x, hx, hxUnique⟩ := hyNonleaf
  have hzx : z ≠ x := by
    intro h
    subst x
    exact hx.2 hz
  have hyDegreePos : 0 < T.degree y := by
    exact (T.degree_pos_iff_exists_adj y).mpr ⟨z, hyz⟩
  have hyDegreeThree : 3 ≤ T.degree y := by
    by_contra h
    have hle : T.degree y ≤ 2 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h)
    have htwo : T.degree y = 2 := by
      have hzmem : z ∈ T.neighborFinset y := by simpa using hyz
      have hxmem : x ∈ T.neighborFinset y := by simpa using hx.1
      have honeCard : 1 < (T.neighborFinset y).card :=
        Finset.one_lt_card.mpr ⟨z, hzmem, x, hxmem, hzx⟩
      have hone : 1 < T.degree y := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using honeCard
      omega
    exact hyDegree htwo
  have hcardRemove : 1 ≤ (T.neighborFinset y \ {z, x}).card := by
    have hzmem : z ∈ T.neighborFinset y := by simpa using hyz
    have hxmem : x ∈ T.neighborFinset y := by simpa using hx.1
    have hpair : ({z, x} : Finset V) ⊆ T.neighborFinset y := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hzmem
      · exact hxmem
    rw [Finset.card_sdiff_of_subset hpair]
    simp only [Finset.card_insert_of_notMem, Finset.card_singleton, hzx,
      Finset.mem_singleton, not_false_eq_true]
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨z', hz'⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hcardRemove)
  have hz'parts := Finset.mem_sdiff.mp hz'
  have hz'adj : T.Adj y z' := by simpa using hz'parts.1
  have hz'ne : z' ≠ z := by
    intro h
    subst z'
    exact hz'parts.2 (by simp)
  have hz'leaf : IsLeaf T z' := by
    by_contra hnleaf
    have hzx' : z' = x := hxUnique z' ⟨hz'adj, hnleaf⟩
    subst z'
    exact hz'parts.2 (by simp)
  exact ⟨z', hz'ne, hz'adj, hz'leaf⟩

/-- The partition obtained in Zhao's last subcase by moving `y` to the left
and two of its leaf neighbours to the right. -/
noncomputable def exceptionalFlipLeft (U₁ U₂ : Finset V) (y z z' : V) : Finset V :=
  (U₁ \ {z, z'}) ∪ {y}

noncomputable def exceptionalFlipRight (U₁ U₂ : Finset V) (y z z' : V) : Finset V :=
  (U₂ \ {y}) ∪ {z, z'}

theorem exceptionalFlip_partition [Fintype V]
    {U₁ U₂ : Finset V} {y z z' : V}
    (hpart : Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = Finset.univ)
    (hy : y ∈ U₂) (hz : z ∈ U₁) (hz' : z' ∈ U₁)
    (hzz' : z ≠ z') :
    Disjoint (exceptionalFlipLeft U₁ U₂ y z z')
      (exceptionalFlipRight U₁ U₂ y z z') ∧
    exceptionalFlipLeft U₁ U₂ y z z' ∪
      exceptionalFlipRight U₁ U₂ y z z' = Finset.univ := by
  classical
  have hyU₁ : y ∉ U₁ := fun h => Finset.disjoint_left.mp hpart.1 h hy
  have hzU₂ : z ∉ U₂ := fun h => Finset.disjoint_left.mp hpart.1 hz h
  have hz'U₂ : z' ∉ U₂ := fun h => Finset.disjoint_left.mp hpart.1 hz' h
  constructor
  · rw [Finset.disjoint_left]
    intro v hvL hvR
    rcases Finset.mem_union.mp hvL with hvL | hvLy
    · rcases Finset.mem_union.mp hvR with hvR | hvRzz'
      · exact Finset.disjoint_left.mp hpart.1
          (Finset.mem_sdiff.mp hvL).1 (Finset.mem_sdiff.mp hvR).1
      · exact (Finset.mem_sdiff.mp hvL).2 hvRzz'
    · have hvy : v = y := by simpa using hvLy
      subst v
      rcases Finset.mem_union.mp hvR with hvR | hvRzz'
      · exact (Finset.mem_sdiff.mp hvR).2 (by simp)
      · have hyPair : y = z ∨ y = z' := by simpa using hvRzz'
        rcases hyPair with rfl | rfl
        · exact hyU₁ hz
        · exact hyU₁ hz'
  · ext v
    have hvCover : v ∈ U₁ ∨ v ∈ U₂ := by
      have : v ∈ U₁ ∪ U₂ := by rw [hpart.2]; simp
      simpa using this
    simp only [Finset.mem_univ, iff_true]
    rcases hvCover with hv₁ | hv₂
    · by_cases hvpair : v ∈ ({z, z'} : Finset V)
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_union.mpr
        exact Or.inr hvpair
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_sdiff.mpr ⟨hv₁, hvpair⟩
    · by_cases hvy : v = y
      · subst v
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        exact Or.inr (by simp)
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_sdiff.mpr ⟨hv₂, by simpa [hvy]⟩

theorem exceptionalFlip_cards [Fintype V]
    {U₁ U₂ : Finset V} {y z z' : V}
    (hpart : Disjoint U₁ U₂) (hy : y ∈ U₂)
    (hz : z ∈ U₁) (hz' : z' ∈ U₁) (hzz' : z ≠ z') :
    (exceptionalFlipLeft U₁ U₂ y z z').card = U₁.card - 2 + 1 ∧
      (exceptionalFlipRight U₁ U₂ y z z').card = U₂.card - 1 + 2 := by
  classical
  have hpairSub₁ : ({z, z'} : Finset V) ⊆ U₁ := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hz
    · exact hz'
  have hyNot₁ : y ∉ U₁ := fun hy₁ => Finset.disjoint_left.mp hpart hy₁ hy
  have hleftDisj : Disjoint (U₁ \ {z, z'}) ({y} : Finset V) := by
    rw [Finset.disjoint_singleton_right]
    intro hyDiff
    exact hyNot₁ (Finset.mem_sdiff.mp hyDiff).1
  have hzNot₂ : z ∉ U₂ := fun hz₂ => Finset.disjoint_left.mp hpart hz hz₂
  have hz'Not₂ : z' ∉ U₂ := fun hz₂ => Finset.disjoint_left.mp hpart hz' hz₂
  have hrightDisj : Disjoint (U₂ \ {y}) ({z, z'} : Finset V) := by
    rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
    exact ⟨fun hzDiff => hzNot₂ (Finset.mem_sdiff.mp hzDiff).1,
      fun hzDiff => hz'Not₂ (Finset.mem_sdiff.mp hzDiff).1⟩
  constructor
  · rw [exceptionalFlipLeft, Finset.card_union_of_disjoint hleftDisj,
      Finset.card_sdiff_of_subset hpairSub₁, Finset.card_pair hzz',
      Finset.card_singleton]
  · have hySub₂ : ({y} : Finset V) ⊆ U₂ := by simpa using hy
    rw [exceptionalFlipRight, Finset.card_union_of_disjoint hrightDisj,
      Finset.card_sdiff_of_subset hySub₂, Finset.card_singleton,
      Finset.card_pair hzz']

theorem exceptionalFlipRight_independent [Fintype V]
    (T : SimpleGraph V) {U₁ U₂ : Finset V} {y z z' : V}
    (hpart : Disjoint U₁ U₂) (hind : T.IsIndepSet (U₂ : Set V))
    (hy : y ∈ U₂) (hz : z ∈ U₁) (hz' : z' ∈ U₁)
    (hzLeaf : IsLeaf T z) (hz'Leaf : IsLeaf T z')
    (hyz : T.Adj y z) (hyz' : T.Adj y z') :
    T.IsIndepSet (exceptionalFlipRight U₁ U₂ y z z' : Set V) := by
  classical
  have hzUnique : ∀ w, T.Adj z w → w = y := by
    unfold IsLeaf at hzLeaf
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hzLeaf
    intro w hzw
    exact hzLeaf.unique hzw hyz.symm
  have hz'Unique : ∀ w, T.Adj z' w → w = y := by
    unfold IsLeaf at hz'Leaf
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hz'Leaf
    intro w hz'w
    exact hz'Leaf.unique hz'w hyz'.symm
  rw [SimpleGraph.isIndepSet_iff] at hind ⊢
  intro a ha b hb hab hAdj
  change a ∈ exceptionalFlipRight U₁ U₂ y z z' at ha
  change b ∈ exceptionalFlipRight U₁ U₂ y z z' at hb
  simp only [exceptionalFlipRight, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hind ha.1 hb.1 hab hAdj
  · rcases hb with (rfl : b = z) | (rfl : b = z')
    · exact ha.2 (by simpa [hzUnique a hAdj.symm])
    · exact ha.2 (by simpa [hz'Unique a hAdj.symm])
  · rcases ha with (rfl : a = z) | (rfl : a = z')
    · exact hb.2 (by simpa [hzUnique b hAdj])
    · exact hb.2 (by simpa [hz'Unique b hAdj])
  · rcases ha with ha | ha
    · have haz : a = z := ha
      subst a
      rcases hb with hb | hb
      · have hbz : b = z := hb
        subst b
        exact hab rfl
      · have hbz' : b = z' := hb
        subst b
        have hyEq : z' = y := hzUnique z' hAdj
        subst z'
        exact Finset.disjoint_left.mp hpart hz' hy
    · have haz' : a = z' := ha
      subst a
      rcases hb with hb | hb
      · have hbz : b = z := hb
        subst b
        have hyEq : z = y := hz'Unique z hAdj
        subst z
        exact Finset.disjoint_left.mp hpart hz hy
      · have hbz' : b = z' := hb
        subst b
        exact hab rfl

theorem exceptionalFlip_left_leaf_lower [Fintype V]
    (T : SimpleGraph V) {U₁ U₂ : Finset V} {y z z' : V} :
    (leavesIn T U₁).card - 2 ≤
      (leavesIn T (exceptionalFlipLeft U₁ U₂ y z z')).card := by
  classical
  let L := leavesIn T U₁ \ {z, z'}
  have hsub : L ⊆ leavesIn T (exceptionalFlipLeft U₁ U₂ y z z') := by
    intro v hv
    have hvp := Finset.mem_sdiff.mp hv
    have hvLeaf := mem_leavesIn.mp hvp.1
    apply mem_leavesIn.mpr
    refine ⟨?_, hvLeaf.2⟩
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_sdiff.mpr ⟨hvLeaf.1, hvp.2⟩
  have hcard := Finset.card_le_card hsub
  have hpairCard : (({z, z'} : Finset V) ∩ leavesIn T U₁).card ≤ 2 := by
    calc
      (({z, z'} : Finset V) ∩ leavesIn T U₁).card ≤ ({z, z'} : Finset V).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ ≤ 2 := by
        by_cases h : z = z'
        · subst z'
          simp
        · rw [Finset.card_pair h]
  dsimp only [L] at hcard
  rw [Finset.card_sdiff] at hcard
  omega

theorem exceptionalFlip_right_leaf_mono [Fintype V]
    (T : SimpleGraph V) {U₁ U₂ : Finset V} {y z z' : V}
    (hyNotLeaf : ¬ IsLeaf T y) :
    (leavesIn T U₂).card ≤
      (leavesIn T (exceptionalFlipRight U₁ U₂ y z z')).card := by
  classical
  apply Finset.card_le_card
  intro v hv
  have hvLeaf := mem_leavesIn.mp hv
  apply mem_leavesIn.mpr
  refine ⟨?_, hvLeaf.2⟩
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_sdiff.mpr ⟨hvLeaf.1, fun hvy => by
    have hEq : v = y := by simpa using hvy
    exact hyNotLeaf (hEq ▸ hvLeaf.2)⟩

/-- Zhao's final exceptional conversion: the almost-balanced partition is
near-ideal if the special parent has degree two; otherwise a second leaf
neighbour exists, and moving the parent and the two leaves produces an ideal
partition. -/
theorem exceptional_nearIdeal_or_ideal [Fintype V]
    (l n : ℕ) (hl : 0 < l) (T : SimpleGraph V)
    (U₁ U₂ : Finset V)
    (hpart : Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = Finset.univ)
    (hnEven : Even n)
    (hcard₁ : U₁.card = n / 2 + 1) (hcard₂ : U₂.card = n / 2)
    (hind : T.IsIndepSet (U₂ : Set V))
    (hleaves₁ : 6 * l + 1 ≤ (leavesIn T U₁).card)
    (hleaves₂ : 6 * l + 1 ≤ (leavesIn T U₂).card)
    {z y : V} (hzU₁ : z ∈ U₁) (hzLeaf : IsLeaf T z)
    (hyU₂ : y ∈ U₂) (hyz : T.Adj y z)
    (hyNonleaf : HasExactlyOneNonleafNeighbor T y) :
    (∃ U₁' U₂', IsIdealPartition l T U₁' U₂') ∨
      IsNearIdealPartition l n T U₁ U₂ := by
  classical
  by_cases hyDegree : T.degree y = 2
  · right
    refine ⟨hpart, hnEven, hcard₁, hcard₂, hind, ?_, ?_,
      ⟨z, hzU₁, hzLeaf, y, hyU₂, hyz, hyDegree⟩⟩
    · omega
    · omega
  · left
    obtain ⟨z', hzz', hyz', hz'Leaf⟩ :=
      exists_second_leaf_neighbor T hzLeaf hyz hyNonleaf hyDegree
    have hz'U₁ : z' ∈ U₁ := by
      have hz'NotU₂ : z' ∉ U₂ := by
        intro hz'U₂
        rw [SimpleGraph.isIndepSet_iff] at hind
        exact hind hyU₂ hz'U₂ hyz'.ne hyz'
      have hz'Univ : z' ∈ U₁ ∪ U₂ := by rw [hpart.2]; simp
      rcases Finset.mem_union.mp hz'Univ with h | h
      · exact h
      · exact False.elim (hz'NotU₂ h)
    let U₁' := exceptionalFlipLeft U₁ U₂ y z z'
    let U₂' := exceptionalFlipRight U₁ U₂ y z z'
    refine ⟨U₁', U₂', ?_⟩
    have hflipPart := exceptionalFlip_partition hpart hyU₂ hzU₁ hz'U₁ hzz'.symm
    have hflipCards := exceptionalFlip_cards hpart.1 hyU₂ hzU₁ hz'U₁ hzz'.symm
    have hdegreeThree : 3 ≤ T.degree y := by
      obtain ⟨x, hx, hxUnique⟩ := hyNonleaf
      have hzx : z ≠ x := by
        intro h
        subst x
        exact hx.2 hzLeaf
      have hzmem : z ∈ T.neighborFinset y := by simpa using hyz
      have hxmem : x ∈ T.neighborFinset y := by simpa using hx.1
      have honeCard : 1 < (T.neighborFinset y).card :=
        Finset.one_lt_card.mpr ⟨z, hzmem, x, hxmem, hzx⟩
      have hone : 1 < T.degree y := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using honeCard
      omega
    have hyNotLeaf : ¬ IsLeaf T y := by
      intro h
      unfold IsLeaf at h
      omega
    refine
      { partition := hflipPart
        card_le := ?_
        right_independent := exceptionalFlipRight_independent T hpart.1 hind
          hyU₂ hzU₁ hz'U₁ hzLeaf hz'Leaf hyz hyz'
        left_leaves := ?_
        right_leaves := ?_ }
    · dsimp only [U₁', U₂']
      rw [hflipCards.1, hflipCards.2, hcard₁, hcard₂]
      omega
    · dsimp only [U₁']
      have hlower := exceptionalFlip_left_leaf_lower T
        (U₁ := U₁) (U₂ := U₂) (y := y) (z := z) (z' := z')
      omega
    · dsimp only [U₂']
      have hmono := exceptionalFlip_right_leaf_mono T
        (U₁ := U₁) (U₂ := U₂) (z := z) (z' := z') hyNotLeaf
      omega

/-- The exceptional conversion in the form needed by the direct degree-sum
argument: it is enough that the parent have *at most* one nonleaf neighbour.
When it has degree two we obtain the near-ideal witness.  Otherwise the
preceding counting lemma supplies two leaf neighbours and the three-vertex
flip is ideal. -/
theorem exceptional_nearIdeal_or_ideal_of_card_nonleaf_le_one [Fintype V]
    (l n : ℕ) (T : SimpleGraph V)
    (U₁ U₂ : Finset V)
    (hpart : Disjoint U₁ U₂ ∧ U₁ ∪ U₂ = Finset.univ)
    (hnEven : Even n)
    (hcard₁ : U₁.card = n / 2 + 1) (hcard₂ : U₂.card = n / 2)
    (hind : T.IsIndepSet (U₂ : Set V))
    (hleaves₁ : 6 * l + 1 ≤ (leavesIn T U₁).card)
    (hleaves₂ : 6 * l + 1 ≤ (leavesIn T U₂).card)
    {z y : V} (hzU₁ : z ∈ U₁) (hzLeaf : IsLeaf T z)
    (hyU₂ : y ∈ U₂) (hyz : T.Adj y z) (hyNotLeaf : ¬ IsLeaf T y)
    (hyFew : (nonleafNeighbors T y).card ≤ 1) :
    (∃ U₁' U₂', IsIdealPartition l T U₁' U₂') ∨
      IsNearIdealPartition l n T U₁ U₂ := by
  classical
  by_cases hyDegree : T.degree y = 2
  · right
    refine ⟨hpart, hnEven, hcard₁, hcard₂, hind, ?_, ?_,
      ⟨z, hzU₁, hzLeaf, y, hyU₂, hyz, hyDegree⟩⟩ <;> omega
  · left
    obtain ⟨z', hzz', hyz', hz'Leaf⟩ :=
      exists_second_leaf_neighbor_of_card_nonleaf_le_one T hzLeaf hyz
        hyNotLeaf hyFew hyDegree
    have hz'U₁ : z' ∈ U₁ := by
      have hz'NotU₂ : z' ∉ U₂ := by
        intro hz'U₂
        rw [SimpleGraph.isIndepSet_iff] at hind
        exact hind hyU₂ hz'U₂ hyz'.ne hyz'
      have hz'Univ : z' ∈ U₁ ∪ U₂ := by rw [hpart.2]; simp
      rcases Finset.mem_union.mp hz'Univ with h | h
      · exact h
      · exact False.elim (hz'NotU₂ h)
    let U₁' := exceptionalFlipLeft U₁ U₂ y z z'
    let U₂' := exceptionalFlipRight U₁ U₂ y z z'
    refine ⟨U₁', U₂', ?_⟩
    have hflipPart := exceptionalFlip_partition hpart hyU₂ hzU₁ hz'U₁ hzz'.symm
    have hflipCards := exceptionalFlip_cards hpart.1 hyU₂ hzU₁ hz'U₁ hzz'.symm
    refine
      { partition := hflipPart
        card_le := ?_
        right_independent := exceptionalFlipRight_independent T hpart.1 hind
          hyU₂ hzU₁ hz'U₁ hzLeaf hz'Leaf hyz hyz'
        left_leaves := ?_
        right_leaves := ?_ }
    · dsimp only [U₁', U₂']
      rw [hflipCards.1, hflipCards.2, hcard₁, hcard₂]
      omega
    · dsimp only [U₁']
      have hlower := exceptionalFlip_left_leaf_lower T
        (U₁ := U₁) (U₂ := U₂) (y := y) (z := z) (z' := z')
      omega
    · dsimp only [U₂']
      have hmono := exceptionalFlip_right_leaf_mono T
        (U₁ := U₁) (U₂ := U₂) (z := z) (z' := z') hyNotLeaf
      omega

end

end Erdos547b.ZhaoLemma77Rooted

#print axioms Erdos547b.ZhaoLemma77Rooted.exists_second_leaf_neighbor
#print axioms Erdos547b.ZhaoLemma77Rooted.exceptionalFlip_partition
#print axioms Erdos547b.ZhaoLemma77Rooted.exceptional_nearIdeal_or_ideal_of_card_nonleaf_le_one

namespace Erdos547b

open Finset
open SimpleGraph

/-- The degree-sum core used in Zhao's Lemma 7.7.  If every leaf in the
`O`-side is attached to a vertex having at least two nonleaf neighbours, then
the leaves in the two sides satisfy the indicated imbalance inequality. -/
theorem leaf_imbalance_of_two_nonleaf_neighbors {V : Type*} [Fintype V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V)
    (hT : T.IsTree) (hpart : IsProperBipartition T E O)
    (hbranch : ∀ z ∈ leavesIn T O, ∀ y, T.Adj z y →
      2 ≤ (by
        classical
        exact ((T.neighborFinset y).filter fun w => ¬ IsLeaf T w).card)) :
    (leavesIn T O).card + E.card + 1 ≤ (leavesIn T E).card + O.card := by
  classical
  have hdisj : Disjoint E O := Finset.disjoint_coe.mp hpart.bipartite.disjoint
  have hcover : E ∪ O = Finset.univ := by
    ext v
    have hv := Set.ext_iff.mp hpart.cover v
    simpa using hv
  have hcardV : Fintype.card V = E.card + O.card := by
    rw [← Finset.card_univ, ← hcover, Finset.card_union_of_disjoint hdisj]
  have hcardEpos : 0 < E.card := Finset.card_pos.mpr hpart.left_nonempty
  have hcardOpos : 0 < O.card := Finset.card_pos.mpr hpart.right_nonempty
  have hcardVtwo : 1 < Fintype.card V := by omega
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcardVtwo

  let leafNbr : V → Finset V := fun y =>
    (T.neighborFinset y).filter fun z => z ∈ leavesIn T O
  let nonleafNbr : V → Finset V := fun y =>
    (T.neighborFinset y).filter fun z => ¬ IsLeaf T z

  have hlocal_union (y : V) :
      (leafNbr y).card + (nonleafNbr y).card ≤ T.degree y := by
    have hd : Disjoint (leafNbr y) (nonleafNbr y) := by
      rw [Finset.disjoint_left]
      intro z hzleaf hznonleaf
      have hzOleaf : z ∈ leavesIn T O := (Finset.mem_filter.mp hzleaf).2
      have hzL : IsLeaf T z := (Finset.mem_filter.mp hzOleaf).2
      exact (Finset.mem_filter.mp hznonleaf).2 hzL
    rw [← Finset.card_union_of_disjoint hd, ← T.card_neighborFinset_eq_degree]
    exact Finset.card_le_card (by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_filter.mp hz).1
      · exact (Finset.mem_filter.mp hz).1)

  have hpoint (y : V) (hy : y ∈ E) :
      2 + (leafNbr y).card ≤
        T.degree y + if IsLeaf T y then 1 else 0 := by
    by_cases hzero : (leafNbr y).card = 0
    · have hpos : 0 < T.degree y := hT.preconnected.degree_pos_of_nontrivial y
      by_cases hleaf : IsLeaf T y
      · rw [hzero, if_pos hleaf]
        have hdeg : T.degree y = 1 := hleaf
        omega
      · rw [hzero, if_neg hleaf]
        have hne : T.degree y ≠ 1 := by
          intro hdeg
          exact hleaf hdeg
        omega
    · have hne : (leafNbr y).Nonempty := Finset.card_ne_zero.mp hzero
      obtain ⟨z, hz⟩ := hne
      have hzOleaf : z ∈ leavesIn T O :=
        (Finset.mem_filter.mp hz).2
      have hzy : T.Adj z y := by
        exact (T.adj_comm y z).mp
          ((T.mem_neighborFinset y z).mp (Finset.mem_filter.mp hz).1)
      have htwo : 2 ≤ (nonleafNbr y).card := by
        simpa only [nonleafNbr] using hbranch z hzOleaf y hzy
      have hsum := hlocal_union y
      have hynonleaf : ¬ IsLeaf T y := by
        intro hleaf
        have hdeg : T.degree y = 1 := hleaf
        omega
      rw [if_neg hynonleaf]
      omega

  have hdouble :
      (∑ y ∈ E, (leafNbr y).card) = (leavesIn T O).card := by
    calc
      (∑ y ∈ E, (leafNbr y).card) =
          ∑ y ∈ E,
            #((leavesIn T O).bipartiteAbove T.Adj y) := by
              apply Finset.sum_congr rfl
              intro y hy
              apply congrArg Finset.card
              ext z
              simp only [leafNbr, Finset.mem_filter,
                Finset.mem_bipartiteAbove, T.mem_neighborFinset]
              tauto
      _ = ∑ z ∈ leavesIn T O, #(E.bipartiteBelow T.Adj z) :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow T.Adj
      _ = ∑ z ∈ leavesIn T O, 1 := by
        apply Finset.sum_congr rfl
        intro z hz
        have hzO : z ∈ O := (Finset.mem_filter.mp hz).1
        have hbelow : E.bipartiteBelow T.Adj z = T.neighborFinset z := by
          ext y
          simp only [Finset.mem_bipartiteBelow, T.mem_neighborFinset]
          constructor
          · exact fun h => (T.adj_comm y z).mp h.2
          · intro hyz
            have hyz' : T.Adj y z := (T.adj_comm z y).mp hyz
            exact ⟨hpart.bipartite.mem_of_mem_adj' hzO hyz', hyz'⟩
        rw [hbelow, T.card_neighborFinset_eq_degree]
        exact (Finset.mem_filter.mp hz).2
      _ = (leavesIn T O).card := by simp

  have hsumE : (∑ y ∈ E, T.degree y) = T.edgeFinset.card :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hpart.bipartite
  have hedge : T.edgeFinset.card = E.card + O.card - 1 := by
    have h := hT.card_edgeFinset
    rw [hcardV] at h
    omega
  have hdegreeLeaf :
      2 * E.card + (leavesIn T O).card ≤
        (∑ y ∈ E, T.degree y) + (leavesIn T E).card := by
    rw [← hdouble]
    calc
      2 * E.card + ∑ y ∈ E, (leafNbr y).card =
          ∑ y ∈ E, (2 + (leafNbr y).card) := by
            simp [Finset.sum_add_distrib, Nat.mul_comm]
      _ ≤ ∑ y ∈ E,
          (T.degree y + if IsLeaf T y then 1 else 0) := by
            exact Finset.sum_le_sum fun y hy => hpoint y hy
      _ = (∑ y ∈ E, T.degree y) + (leavesIn T E).card := by
            rw [Finset.sum_add_distrib]
            simp [leavesIn]
  rw [hsumE, hedge] at hdegreeLeaf
  omega

end Erdos547b

#print axioms Erdos547b.leaf_imbalance_of_two_nonleaf_neighbors

namespace Erdos547b

open Finset
open SimpleGraph

/-- The one-exception form of the degree-sum core.  The exceptional vertex
`r` is charged only for its leaf neighbours, rather than for two additional
nonleaf neighbours. -/
theorem leaf_imbalance_of_two_nonleaf_neighbors_except {V : Type*} [Fintype V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (E O : Finset V) (r : V)
    (hT : T.IsTree) (hpart : IsProperBipartition T E O) (hr : r ∈ E)
    (hbranch : ∀ z ∈ leavesIn T O, ∀ y, T.Adj z y → y ≠ r →
      2 ≤ (by
        classical
        exact ((T.neighborFinset y).filter fun w => ¬ IsLeaf T w).card)) :
    (leavesIn T O).card + E.card ≤ (leavesIn T E).card + O.card + 1 := by
  classical
  have hdisj : Disjoint E O := Finset.disjoint_coe.mp hpart.bipartite.disjoint
  have hcover : E ∪ O = Finset.univ := by
    ext v
    have hv := Set.ext_iff.mp hpart.cover v
    simpa using hv
  have hcardV : Fintype.card V = E.card + O.card := by
    rw [← Finset.card_univ, ← hcover, Finset.card_union_of_disjoint hdisj]
  have hcardVtwo : 1 < Fintype.card V := by
    have hE : 0 < E.card := Finset.card_pos.mpr hpart.left_nonempty
    have hO : 0 < O.card := Finset.card_pos.mpr hpart.right_nonempty
    omega
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcardVtwo

  let leafNbr : V → Finset V := fun y =>
    (T.neighborFinset y).filter fun z => z ∈ leavesIn T O
  let nonleafNbr : V → Finset V := fun y =>
    (T.neighborFinset y).filter fun z => ¬ IsLeaf T z

  have hlocal_union (y : V) :
      (leafNbr y).card + (nonleafNbr y).card ≤ T.degree y := by
    have hd : Disjoint (leafNbr y) (nonleafNbr y) := by
      rw [Finset.disjoint_left]
      intro z hzleaf hznonleaf
      have hzOleaf : z ∈ leavesIn T O := (Finset.mem_filter.mp hzleaf).2
      have hzL : IsLeaf T z := (Finset.mem_filter.mp hzOleaf).2
      exact (Finset.mem_filter.mp hznonleaf).2 hzL
    rw [← Finset.card_union_of_disjoint hd, ← T.card_neighborFinset_eq_degree]
    exact Finset.card_le_card (by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_filter.mp hz).1
      · exact (Finset.mem_filter.mp hz).1)

  have hpoint (y : V) (hy : y ∈ E) :
      (if y = r then 0 else 2) + (leafNbr y).card ≤
        T.degree y + if IsLeaf T y then 1 else 0 := by
    by_cases hyr : y = r
    · rw [if_pos hyr]
      have hsub : leafNbr y ⊆ T.neighborFinset y := by
        intro z hz
        exact (Finset.mem_filter.mp hz).1
      have hle : (leafNbr y).card ≤ T.degree y := by
        rw [← T.card_neighborFinset_eq_degree]
        exact Finset.card_le_card hsub
      omega
    · rw [if_neg hyr]
      by_cases hzero : (leafNbr y).card = 0
      · have hpos : 0 < T.degree y := hT.preconnected.degree_pos_of_nontrivial y
        by_cases hleaf : IsLeaf T y
        · rw [hzero, if_pos hleaf]
          have hdeg : T.degree y = 1 := hleaf
          omega
        · rw [hzero, if_neg hleaf]
          have hne : T.degree y ≠ 1 := fun hdeg => hleaf hdeg
          omega
      · obtain ⟨z, hz⟩ : (leafNbr y).Nonempty := Finset.card_ne_zero.mp hzero
        have hzOleaf : z ∈ leavesIn T O := (Finset.mem_filter.mp hz).2
        have hzy : T.Adj z y := by
          exact (T.adj_comm y z).mp
            ((T.mem_neighborFinset y z).mp (Finset.mem_filter.mp hz).1)
        have htwo : 2 ≤ (nonleafNbr y).card := by
          simpa only [nonleafNbr] using hbranch z hzOleaf y hzy hyr
        have hsum := hlocal_union y
        have hynonleaf : ¬ IsLeaf T y := by
          intro hleaf
          have hdeg : T.degree y = 1 := hleaf
          omega
        rw [if_neg hynonleaf]
        omega

  have hdouble :
      (∑ y ∈ E, (leafNbr y).card) = (leavesIn T O).card := by
    calc
      (∑ y ∈ E, (leafNbr y).card) =
          ∑ y ∈ E, #((leavesIn T O).bipartiteAbove T.Adj y) := by
            apply Finset.sum_congr rfl
            intro y hy
            apply congrArg Finset.card
            ext z
            simp only [leafNbr, Finset.mem_filter,
              Finset.mem_bipartiteAbove, T.mem_neighborFinset]
            tauto
      _ = ∑ z ∈ leavesIn T O, #(E.bipartiteBelow T.Adj z) :=
        Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow T.Adj
      _ = ∑ z ∈ leavesIn T O, 1 := by
        apply Finset.sum_congr rfl
        intro z hz
        have hzO : z ∈ O := (Finset.mem_filter.mp hz).1
        have hbelow : E.bipartiteBelow T.Adj z = T.neighborFinset z := by
          ext y
          simp only [Finset.mem_bipartiteBelow, T.mem_neighborFinset]
          constructor
          · exact fun h => (T.adj_comm y z).mp h.2
          · intro hyz
            have hyz' : T.Adj y z := (T.adj_comm z y).mp hyz
            exact ⟨hpart.bipartite.mem_of_mem_adj' hzO hyz', hyz'⟩
        rw [hbelow, T.card_neighborFinset_eq_degree]
        exact (Finset.mem_filter.mp hz).2
      _ = (leavesIn T O).card := by simp

  have hconst :
      (∑ y ∈ E, if y = r then 0 else 2) = 2 * (E.card - 1) := by
    have hersum :
        (∑ y ∈ E.erase r, if y = r then 0 else 2) = 2 * (E.erase r).card := by
      calc
        (∑ y ∈ E.erase r, if y = r then 0 else 2) =
            ∑ _y ∈ E.erase r, 2 := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [if_neg (Finset.mem_erase.mp hy).1]
        _ = 2 * (E.erase r).card := by simp [Nat.mul_comm]
    rw [← Finset.sum_erase_add _ _ hr, if_pos rfl, add_zero, hersum,
      Finset.card_erase_of_mem hr]
  have hsumE : (∑ y ∈ E, T.degree y) = T.edgeFinset.card :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hpart.bipartite
  have hedge : T.edgeFinset.card = E.card + O.card - 1 := by
    have h := hT.card_edgeFinset
    rw [hcardV] at h
    omega
  have hdegreeLeaf :
      2 * (E.card - 1) + (leavesIn T O).card ≤
        (∑ y ∈ E, T.degree y) + (leavesIn T E).card := by
    rw [← hconst, ← hdouble]
    calc
      (∑ y ∈ E, if y = r then 0 else 2) +
            ∑ y ∈ E, (leafNbr y).card =
          ∑ y ∈ E, ((if y = r then 0 else 2) + (leafNbr y).card) := by
            rw [Finset.sum_add_distrib]
      _ ≤ ∑ y ∈ E,
          (T.degree y + if IsLeaf T y then 1 else 0) := by
            exact Finset.sum_le_sum fun y hy => hpoint y hy
      _ = (∑ y ∈ E, T.degree y) + (leavesIn T E).card := by
            rw [Finset.sum_add_distrib]
            simp [leavesIn]
  rw [hsumE, hedge] at hdegreeLeaf
  have hEpos : 0 < E.card := Finset.card_pos.mpr hpart.left_nonempty
  omega

end Erdos547b

#print axioms Erdos547b.leaf_imbalance_of_two_nonleaf_neighbors_except

/-!
Assembly of Zhao Lemma 7.7.  The first public theorem below is the exact
trichotomy with the parity-one branch exposed as `NearIdealCore`; the final
special-leaf step is developed below it.
-/

namespace Erdos547b.ZhaoLemma77Full74

open Finset SimpleGraph
open scoped Classical

noncomputable section

universe u
variable {V : Type u}

/-- The numerical degree of a finite neighbor set is independent of the
chosen `Fintype` witness on that set. -/
theorem degree_instance_eq (T : SimpleGraph V) (v : V)
    (i j : Fintype (T.neighborSet v)) :
    @SimpleGraph.degree V T v i = @SimpleGraph.degree V T v j := by
  rw [← @SimpleGraph.card_neighborSet_eq_degree V T v i,
      ← @SimpleGraph.card_neighborSet_eq_degree V T v j]
  exact @Fintype.card_congr _ _ i j (Equiv.refl _)

theorem rooted_isLeaf_iff_shared [Fintype V] (T : SimpleGraph V) (v : V) :
    Erdos547b.Lemma77Rooted.IsLeaf T v ↔ Erdos547b.IsLeaf T v := by
  unfold Erdos547b.Lemma77Rooted.IsLeaf Erdos547b.IsLeaf
  apply iff_of_eq
  apply congrArg (fun d : ℕ => d = 1)
  apply degree_instance_eq

theorem rooted_leaves_eq_shared [Fintype V] (T : SimpleGraph V) :
    Erdos547b.Lemma77Rooted.leaves T = Finset.univ.filter (Erdos547b.IsLeaf T) := by
  classical
  ext v
  simp only [Erdos547b.Lemma77Rooted.mem_leaves, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact rooted_isLeaf_iff_shared T v

theorem rooted_leavesIn_eq_shared [Fintype V] (T : SimpleGraph V) (S : Finset V) :
    Erdos547b.Lemma77Rooted.leavesIn T S = Erdos547b.leavesIn T S := by
  classical
  ext v
  simp only [Erdos547b.Lemma77Rooted.mem_leavesIn, Erdos547b.leavesIn,
    Finset.mem_filter]
  exact and_congr_right (fun _ => rooted_isLeaf_iff_shared T v)

theorem main_leaves_eq_rooted [Fintype V] (T : SimpleGraph V) :
    Erdos547b.ZhaoLemma77.leaves T = Erdos547b.Lemma77Rooted.leaves T := by
  classical
  ext v
  simp only [Erdos547b.ZhaoLemma77.mem_leaves,
    Erdos547b.Lemma77Rooted.mem_leaves]
  unfold Erdos547b.ZhaoLemma77.IsLeaf Erdos547b.Lemma77Rooted.IsLeaf
  apply iff_of_eq
  apply congrArg (fun d : ℕ => d = 1)
  apply degree_instance_eq

theorem main_leavesIn_eq_shared [Fintype V] (T : SimpleGraph V) (S : Finset V) :
    Erdos547b.ZhaoLemma77.leavesIn T S = Erdos547b.leavesIn T S := by
  rfl

theorem rootedExceptional_isLeaf_iff_shared [Fintype V]
    (T : SimpleGraph V) (v : V) :
    Erdos547b.ZhaoLemma77Rooted.IsLeaf T v ↔ Erdos547b.IsLeaf T v := by
  unfold Erdos547b.ZhaoLemma77Rooted.IsLeaf Erdos547b.IsLeaf
  apply iff_of_eq
  apply congrArg (fun d : ℕ => d = 1)
  apply degree_instance_eq

theorem rootedExceptional_nonleafNeighbors_eq_sharedFilter [Fintype V]
    (T : SimpleGraph V) (y : V) :
    Erdos547b.ZhaoLemma77Rooted.nonleafNeighbors T y =
      (T.neighborFinset y).filter fun w => ¬ Erdos547b.IsLeaf T w := by
  classical
  ext w
  simp only [Erdos547b.ZhaoLemma77Rooted.mem_nonleafNeighbors,
    Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact and_congr_right (fun _ => not_congr (rootedExceptional_isLeaf_iff_shared T w))

theorem proper_to_main_bipartition [Fintype V] {T : SimpleGraph V}
    {E O : Finset V} (h : IsProperBipartition T E O) :
    Erdos547b.ZhaoLemma77.IsVertexBipartition T E O := by
  refine ⟨h.bipartite, ?_⟩
  ext v
  have hv := Set.ext_iff.mp h.cover v
  simpa using hv

theorem exists_nonleaf_root [Fintype V]
    (T : SimpleGraph V) (hT : T.IsTree) (l : ℕ) (hl : 0 < l)
    (hmany : 33 * l ≤ (Erdos547b.Lemma77Rooted.leaves T).card) :
    ∃ r : V, ¬ Erdos547b.Lemma77Rooted.IsLeaf T r := by
  classical
  let rootLF : T.LocallyFinite := fun _ => Subtype.fintype _
  let : T.LocallyFinite := rootLF
  by_contra h
  push_neg at h
  have hsumOne :
      (∑ v : V, @SimpleGraph.degree V T v (rootLF v)) = Fintype.card V := by
    calc
      ∑ v : V, T.degree v = ∑ _v : V, 1 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (rooted_isLeaf_iff_shared T v).mp (h v)
      _ = Fintype.card V := by simp
  have hsum := T.sum_degrees_eq_twice_card_edges
  let standardLF : T.LocallyFinite := fun _ => Subtype.fintype _
  have hsumBridge :
      (∑ v : V, @SimpleGraph.degree V T v (rootLF v)) =
        ∑ v : V, @SimpleGraph.degree V T v (standardLF v) := by
    apply Finset.sum_congr rfl
    intro v _
    apply degree_instance_eq
  have hsumStd :
      (∑ v : V, @SimpleGraph.degree V T v (standardLF v)) =
        2 * T.edgeFinset.card := by
    simpa [standardLF] using hsum
  have hsumRoot :
      (∑ v : V, @SimpleGraph.degree V T v (rootLF v)) =
        2 * T.edgeFinset.card := hsumBridge.trans hsumStd
  have hedge := hT.card_edgeFinset
  have hcardLarge : 33 ≤ Fintype.card V := by
    have hleafSub : Erdos547b.Lemma77Rooted.leaves T ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
    have hc : (Erdos547b.Lemma77Rooted.leaves T).card ≤ Fintype.card V := by
      simpa using Finset.card_le_card hleafSub
    omega
  have hcardEq : Fintype.card V = 2 * T.edgeFinset.card :=
    hsumOne.symm.trans hsumRoot
  have hedgeOne : T.edgeFinset.card = 1 := by omega
  omega

theorem naturalSplit_of_fact79 [Fintype V]
    (l : ℕ) (hl : 0 < l) (T : SimpleGraph V) (hT : T.IsTree)
    (E O : Finset V) (hpart : IsProperBipartition T E O)
    (hleftSmall : (Erdos547b.leavesIn T E).card < 5 * l)
    (hmany : 33 * l ≤ (Erdos547b.Lemma77Rooted.leaves T).card) :
    ∃ S x, Erdos547b.ZhaoLemma77HardCase.NaturalSplit l T E O S x := by
  classical
  obtain ⟨r, hr⟩ := exists_nonleaf_root T hT l hl hmany
  obtain ⟨x, kept, S, hkept, hS, hnatural, hboundary,
      hSin, hSupper, hSout⟩ := Erdos547b.Lemma77Rooted.fact79_leaf_natural_subtree T hT r hr l hl hmany
  have hxNonleafR : ¬ Erdos547b.Lemma77Rooted.IsLeaf T x :=
    Erdos547b.Lemma77Rooted.natural_root_not_leaf_of_eleven_leaves hT hr l hl kept hkept (by simpa [hS] using hSin)
  have hxNonleaf : ¬ Erdos547b.IsLeaf T x := by simpa [rooted_isLeaf_iff_shared] using hxNonleafR
  have hAinner : (Erdos547b.leavesIn T (E ∩ S)).card ≤
      (Erdos547b.leavesIn T E).card := by
    apply Finset.card_le_card
    intro v hv
    simp only [Erdos547b.leavesIn, Finset.mem_filter] at hv ⊢
    exact ⟨(Finset.mem_inter.mp hv.1).1, hv.2⟩
  have hAouter : (Erdos547b.leavesIn T (E \ S)).card ≤
      (Erdos547b.leavesIn T E).card := by
    apply Finset.card_le_card
    intro v hv
    simp only [Erdos547b.leavesIn, Finset.mem_filter] at hv ⊢
    exact ⟨(Finset.mem_sdiff.mp hv.1).1, hv.2⟩
  have hLeafSplitInner :
      (Erdos547b.Lemma77Rooted.leavesIn T S).card =
        (Erdos547b.leavesIn T (E ∩ S)).card +
          (Erdos547b.leavesIn T (O ∩ S)).card := by
    have hcover : E ∪ O = Finset.univ := by
      ext v
      have hv := Set.ext_iff.mp hpart.cover v
      simpa using hv
    have hdisj : Disjoint E O := Finset.disjoint_coe.mp hpart.bipartite.disjoint
    have heq : Erdos547b.Lemma77Rooted.leavesIn T S =
        Erdos547b.leavesIn T (E ∩ S) ∪ Erdos547b.leavesIn T (O ∩ S) := by
      ext v
      simp only [Erdos547b.Lemma77Rooted.mem_leavesIn, Erdos547b.leavesIn, Finset.mem_filter,
        Finset.mem_union, Finset.mem_inter]
      rw [rooted_isLeaf_iff_shared]
      have hvSide : v ∈ E ∨ v ∈ O := by
        have : v ∈ E ∪ O := by rw [hcover]; simp
        simpa using this
      constructor
      · rintro ⟨hvS, hvLeaf⟩
        rcases hvSide with hvE | hvO
        · exact Or.inl ⟨⟨hvE, hvS⟩, hvLeaf⟩
        · exact Or.inr ⟨⟨hvO, hvS⟩, hvLeaf⟩
      · rintro (hv | hv)
        · exact ⟨hv.1.2, hv.2⟩
        · exact ⟨hv.1.2, hv.2⟩
    rw [heq, Finset.card_union_of_disjoint]
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _) <|
      Finset.disjoint_of_subset_right (Finset.filter_subset _ _) <|
        Finset.disjoint_of_subset_left Finset.inter_subset_left <|
          Finset.disjoint_of_subset_right Finset.inter_subset_left hdisj
  have hLeafSplitOuter :
      (Erdos547b.Lemma77Rooted.leaves T \ S).card =
        (Erdos547b.leavesIn T (E \ S)).card +
          (Erdos547b.leavesIn T (O \ S)).card := by
    have hcover : E ∪ O = Finset.univ := by
      ext v
      have hv := Set.ext_iff.mp hpart.cover v
      simpa using hv
    have hdisj : Disjoint E O := Finset.disjoint_coe.mp hpart.bipartite.disjoint
    have heq : Erdos547b.Lemma77Rooted.leaves T \ S =
        Erdos547b.leavesIn T (E \ S) ∪ Erdos547b.leavesIn T (O \ S) := by
      ext v
      simp only [Erdos547b.Lemma77Rooted.mem_leaves, Erdos547b.leavesIn, Finset.mem_sdiff,
        Finset.mem_filter, Finset.mem_union]
      rw [rooted_isLeaf_iff_shared]
      have hvSide : v ∈ E ∨ v ∈ O := by
        have : v ∈ E ∪ O := by rw [hcover]; simp
        simpa using this
      constructor
      · rintro ⟨hvLeaf, hvS⟩
        rcases hvSide with hvE | hvO
        · exact Or.inl ⟨⟨hvE, hvS⟩, hvLeaf⟩
        · exact Or.inr ⟨⟨hvO, hvS⟩, hvLeaf⟩
      · rintro (hv | hv)
        · exact ⟨hv.2, hv.1.2⟩
        · exact ⟨hv.2, hv.1.2⟩
    rw [heq, Finset.card_union_of_disjoint]
    exact Finset.disjoint_of_subset_left (Finset.filter_subset _ _) <|
      Finset.disjoint_of_subset_right (Finset.filter_subset _ _) <|
        Finset.disjoint_of_subset_left Finset.sdiff_subset <|
          Finset.disjoint_of_subset_right Finset.sdiff_subset hdisj
  have hInnerOdd : 6 * l + 1 ≤ (Erdos547b.leavesIn T (O ∩ S)).card := by
    have hAinner' : (Erdos547b.leavesIn T (E ∩ S)).card < 5 * l :=
      lt_of_le_of_lt hAinner hleftSmall
    rw [hLeafSplitInner] at hSin
    omega
  have hOuterOdd : 6 * l + 1 ≤ (Erdos547b.leavesIn T (O \ S)).card := by
    have hAouter' : (Erdos547b.leavesIn T (E \ S)).card < 5 * l :=
      lt_of_le_of_lt hAouter hleftSmall
    rw [hLeafSplitOuter] at hSout
    omega
  refine ⟨S, x, ?_⟩
  refine
    { root_mem := ?_
      root_not_leaf := hxNonleaf
      inside_boundary := ?_
      outside_boundary_after_delete_root := ?_
      inner_odd_leaves := hInnerOdd
      outer_odd_leaves := hOuterOdd }
  · subst S
    simp [Erdos547b.Lemma77Rooted.naturalVertices]
  · intro u v huv hu hv
    exact hboundary huv hu hv
  · subst S
    have hout := Erdos547b.Lemma77Rooted.naturalVertices_sdiff_root_hasSingleOutsideBoundaryAttachment
      hT kept hkept
    intro u v huv hu hv
    refine hout huv ?_ ?_
    · exact ⟨(Finset.mem_sdiff.mp hu).1, by simpa using (Finset.mem_sdiff.mp hu).2⟩
    · intro hvset
      apply hv
      exact Finset.mem_sdiff.mpr ⟨hvset.1, by simpa using hvset.2⟩

theorem hard_ideal_to_main [Fintype V] {l : ℕ} {T : SimpleGraph V}
    {U₁ U₂ : Finset V} (h : Erdos547b.ZhaoLemma77HardCase.IsIdealPartition l T U₁ U₂) :
    Erdos547b.ZhaoLemma77.IsIdealPartition l T U₁ U₂ := by
  exact ⟨h.partition, h.card_le, h.right_independent, h.left_leaves, h.right_leaves⟩

theorem rootedExceptional_ideal_to_main [Fintype V] {l : ℕ} {T : SimpleGraph V}
    {U₁ U₂ : Finset V}
    (h : Erdos547b.ZhaoLemma77Rooted.IsIdealPartition l T U₁ U₂) :
    Erdos547b.ZhaoLemma77.IsIdealPartition l T U₁ U₂ := by
  exact ⟨h.partition, h.card_le, h.right_independent, h.left_leaves, h.right_leaves⟩

theorem rootedExceptional_near_to_main [Fintype V] {l n : ℕ} {T : SimpleGraph V}
    {U₁ U₂ : Finset V}
    (h : Erdos547b.ZhaoLemma77Rooted.IsNearIdealPartition l n T U₁ U₂) :
    Erdos547b.ZhaoLemma77.IsNearIdealPartition l n T U₁ U₂ := by
  exact ⟨h.partition, h.n_even, h.left_card, h.right_card,
    h.right_independent, h.left_leaves, h.right_leaves, h.special_leaf⟩

/-- In a connected graph containing some nonleaf vertex, the neighbor of a
leaf cannot itself be a leaf. -/
theorem neighbor_of_leaf_not_leaf_of_exists_nonleaf [Fintype V]
    (T : SimpleGraph V) (hT : T.IsTree) {x y z : V}
    (hx : ¬ Erdos547b.IsLeaf T x) (hz : Erdos547b.IsLeaf T z)
    (hyz : T.Adj y z) : ¬ Erdos547b.IsLeaf T y := by
  change T.degree x ≠ 1 at hx
  change T.degree z = 1 at hz
  change T.degree y ≠ 1
  intro hy
  have hyz_ne : y ≠ z := hyz.ne
  have hxz : x ≠ z := by
    intro h
    exact hx (h ▸ hz)
  have hyx : y ≠ x := by
    intro h
    exact hx (h ▸ hy)
  let C : Set V := ({z} : Set V)ᶜ
  let y' : C := ⟨y, by simp [C, hyz_ne]⟩
  let x' : C := ⟨x, by simp [C, hxz]⟩
  have hyx' : y' ≠ x' := by
    intro h
    exact hyx (congrArg Subtype.val h)
  let : Nontrivial C := ⟨⟨y', x', hyx'⟩⟩
  have hconn := hT.connected.induce_compl_singleton_of_degree_eq_one hz
  have hpos := hconn.preconnected.degree_pos_of_nontrivial y'
  obtain ⟨w, hyw⟩ := ((T.induce C).degree_pos_iff_exists_adj y').mp hpos
  have hywT : T.Adj y w := SimpleGraph.induce_adj.mp hyw
  have huniq := (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hy).unique hywT hyz
  exact w.property (by simpa using huniq)

/-- Exact Lemma-7.7 assembly through the parity-one core.  No mathematical
assumption is hidden: `NearIdealCore` is precisely Definition 7.6(2) with
only its final degree-two witness omitted. -/
theorem lemma7_7_ideal_or_nearCore [Fintype V]
    (l n : ℕ) (T : SimpleGraph V) (hT : T.IsTree)
    (E O : Finset V) (hpart : IsProperBipartition T E O)
    (hEO : E.card ≤ O.card) (hedges : T.edgeFinset.card = n)
    (hmany : 33 * l ≤ (Erdos547b.ZhaoLemma77.leaves T).card) :
    2 * l + 1 ≤ Erdos547b.ZhaoLemma77.bipartitionGap E O ∨
      (∃ U₁ U₂, Erdos547b.ZhaoLemma77.IsIdealPartition l T U₁ U₂) ∨
      (∃ U₁ U₂, Erdos547b.ZhaoLemma77HardCase.NearIdealCore l n T U₁ U₂) := by
  classical
  have hmainPart := proper_to_main_bipartition hpart
  rcases Erdos547b.ZhaoLemma77.lemma7_7_reduction_to_left_leaf_deficit l T E O hmainPart hEO hmany with
    hgap | hideal | hhard
  · exact Or.inl hgap
  · exact Or.inr (Or.inl hideal)
  · right
    have hl : 0 < l := by
      by_contra h
      have hl0 : l = 0 := Nat.eq_zero_of_not_pos h
      subst l
      simp at hhard
    have hmanyR : 33 * l ≤ (Erdos547b.Lemma77Rooted.leaves T).card := by simpa [main_leaves_eq_rooted] using hmany
    obtain ⟨S, x, hsplit⟩ := naturalSplit_of_fact79 l hl T hT E O hpart hhard.1 hmanyR
    have hcardV : Fintype.card V = n + 1 := by
      have hedgeTree := hT.card_edgeFinset
      omega
    have hgapSub : O.card - E.card < 2 * l + 1 := by
      have hg := hhard.2.2
      rw [Erdos547b.ZhaoLemma77.bipartitionGap, Nat.dist_eq_sub_of_le hEO] at hg
      exact hg
    rcases Erdos547b.ZhaoLemma77HardCase.case_b_ideal_or_nearCore l n T E O S x hcardV hpart hEO hgapSub hsplit with
      hI | hN
    · left
      obtain ⟨U₁, U₂, hU⟩ := hI
      exact ⟨U₁, U₂, hard_ideal_to_main hU⟩
    · exact Or.inr hN.1

/-- Zhao's Lemma 7.7, with the real threshold `sqrt θ * n` replaced by an
integer parameter `l`.  This is the exact trichotomy: the final branch
includes the degree-two parent required in Definition 7.6. -/
theorem lemma7_7 [Fintype V]
    (l n : ℕ) (T : SimpleGraph V) (hT : T.IsTree)
    (E O : Finset V) (hpart : IsProperBipartition T E O)
    (hEO : E.card ≤ O.card) (hedges : T.edgeFinset.card = n)
    (hmany : 33 * l ≤ (Erdos547b.ZhaoLemma77.leaves T).card) :
    2 * l + 1 ≤ Erdos547b.ZhaoLemma77.bipartitionGap E O ∨
      (∃ U₁ U₂, Erdos547b.ZhaoLemma77.IsIdealPartition l T U₁ U₂) ∨
      (∃ U₁ U₂, Erdos547b.ZhaoLemma77.IsNearIdealPartition l n T U₁ U₂) := by
  classical
  have hmainPart := proper_to_main_bipartition hpart
  rcases Erdos547b.ZhaoLemma77.lemma7_7_reduction_to_left_leaf_deficit
      l T E O hmainPart hEO hmany with hgap | hideal | hhard
  · exact Or.inl hgap
  · exact Or.inr (Or.inl hideal)
  · right
    have hl : 0 < l := by
      by_contra h
      have hl0 : l = 0 := Nat.eq_zero_of_not_pos h
      subst l
      simp at hhard
    have hmanyR : 33 * l ≤ (Erdos547b.Lemma77Rooted.leaves T).card := by
      simpa [main_leaves_eq_rooted] using hmany
    obtain ⟨S, x, hsplit⟩ :=
      naturalSplit_of_fact79 l hl T hT E O hpart hhard.1 hmanyR
    have hcardV : Fintype.card V = n + 1 := by
      have hedgeTree := hT.card_edgeFinset
      omega
    have hgapSub : O.card - E.card < 2 * l + 1 := by
      have hg := hhard.2.2
      rw [Erdos547b.ZhaoLemma77.bipartitionGap,
        Nat.dist_eq_sub_of_le hEO] at hg
      exact hg
    rcases Erdos547b.ZhaoLemma77HardCase.case_b_ideal_or_nearCore
        l n T E O S x hcardV hpart hEO hgapSub hsplit with hI | hN
    · left
      obtain ⟨U₁, U₂, hU⟩ := hI
      exact ⟨U₁, U₂, hard_ideal_to_main hU⟩
    · have hleafSum :=
        Erdos547b.ZhaoLemma77.card_leaves_eq_card_leavesIn_add T E O hmainPart
      have hleafSumShared :
          (Erdos547b.ZhaoLemma77.leaves T).card =
            (Erdos547b.leavesIn T E).card + (Erdos547b.leavesIn T O).card := by
        simpa [main_leavesIn_eq_shared] using hleafSum
      have hleftSmallShared : (Erdos547b.leavesIn T E).card < 5 * l := by
        simpa [main_leavesIn_eq_shared] using hhard.1
      have hgapLe : O.card - E.card ≤ 2 * l := by omega
      have existsLowExcept (r : V) (hrE : r ∈ E) :
          ∃ z ∈ Erdos547b.leavesIn T O, ∃ y,
            T.Adj y z ∧ y ≠ r ∧
              ((T.neighborFinset y).filter fun w => ¬ Erdos547b.IsLeaf T w).card ≤ 1 := by
        by_contra hnone
        have hbranch : ∀ z ∈ Erdos547b.leavesIn T O, ∀ y, T.Adj z y → y ≠ r →
            2 ≤ ((T.neighborFinset y).filter fun w => ¬ Erdos547b.IsLeaf T w).card := by
          intro z hz y hzy hyr
          by_contra htwo
          have hle :
              ((T.neighborFinset y).filter fun w => ¬ Erdos547b.IsLeaf T w).card ≤ 1 := by
            omega
          exact hnone ⟨z, hz, y, hzy.symm, hyr, hle⟩
        have himbalance := Erdos547b.leaf_imbalance_of_two_nonleaf_neighbors_except
          T E O r hT hpart hrE hbranch
        omega
      obtain ⟨e, heE⟩ := hpart.left_nonempty
      by_cases hxE : x ∈ E
      · obtain ⟨z, hz, y, hyz, hyx, hyFewRaw⟩ := existsLowExcept x hxE
        obtain ⟨U₁, U₂, hcore, hzU₁, hyU₂⟩ := hN.2 z hz y hyz hyx
        have hzLeaf : Erdos547b.IsLeaf T z := (Finset.mem_filter.mp hz).2
        have hyNotLeaf : ¬ Erdos547b.IsLeaf T y :=
          neighbor_of_leaf_not_leaf_of_exists_nonleaf T hT hsplit.root_not_leaf hzLeaf hyz
        have hyFew :
            (Erdos547b.ZhaoLemma77Rooted.nonleafNeighbors T y).card ≤ 1 := by
          rw [rootedExceptional_nonleafNeighbors_eq_sharedFilter]
          exact hyFewRaw
        have hzLeaf' : Erdos547b.ZhaoLemma77Rooted.IsLeaf T z := by
          exact (rootedExceptional_isLeaf_iff_shared T z).mpr hzLeaf
        have hyNotLeaf' : ¬ Erdos547b.ZhaoLemma77Rooted.IsLeaf T y := by
          exact fun h => hyNotLeaf ((rootedExceptional_isLeaf_iff_shared T y).mp h)
        rcases Erdos547b.ZhaoLemma77Rooted.exceptional_nearIdeal_or_ideal_of_card_nonleaf_le_one
            l n T U₁ U₂ hcore.partition hcore.n_even hcore.left_card hcore.right_card
            hcore.right_independent hcore.left_leaves hcore.right_leaves
            hzU₁ hzLeaf' hyU₂ hyz hyNotLeaf' hyFew with hIdeal | hNear
        · left
          obtain ⟨U₁', U₂', hU⟩ := hIdeal
          exact ⟨U₁', U₂', rootedExceptional_ideal_to_main hU⟩
        · right
          exact ⟨U₁, U₂, rootedExceptional_near_to_main hNear⟩
      · obtain ⟨z, hz, y, hyz, hye, hyFewRaw⟩ := existsLowExcept e heE
        have hyE : y ∈ E := hpart.bipartite.mem_of_mem_adj'
          (Finset.mem_filter.mp hz).1 hyz
        have hyx : y ≠ x := by
          intro hyx
          subst y
          exact hxE hyE
        obtain ⟨U₁, U₂, hcore, hzU₁, hyU₂⟩ := hN.2 z hz y hyz hyx
        have hzLeaf : Erdos547b.IsLeaf T z := (Finset.mem_filter.mp hz).2
        have hyNotLeaf : ¬ Erdos547b.IsLeaf T y :=
          neighbor_of_leaf_not_leaf_of_exists_nonleaf T hT hsplit.root_not_leaf hzLeaf hyz
        have hyFew :
            (Erdos547b.ZhaoLemma77Rooted.nonleafNeighbors T y).card ≤ 1 := by
          rw [rootedExceptional_nonleafNeighbors_eq_sharedFilter]
          exact hyFewRaw
        have hzLeaf' : Erdos547b.ZhaoLemma77Rooted.IsLeaf T z := by
          exact (rootedExceptional_isLeaf_iff_shared T z).mpr hzLeaf
        have hyNotLeaf' : ¬ Erdos547b.ZhaoLemma77Rooted.IsLeaf T y := by
          exact fun h => hyNotLeaf ((rootedExceptional_isLeaf_iff_shared T y).mp h)
        rcases Erdos547b.ZhaoLemma77Rooted.exceptional_nearIdeal_or_ideal_of_card_nonleaf_le_one
            l n T U₁ U₂ hcore.partition hcore.n_even hcore.left_card hcore.right_card
            hcore.right_independent hcore.left_leaves hcore.right_leaves
            hzU₁ hzLeaf' hyU₂ hyz hyNotLeaf' hyFew with hIdeal | hNear
        · left
          obtain ⟨U₁', U₂', hU⟩ := hIdeal
          exact ⟨U₁', U₂', rootedExceptional_ideal_to_main hU⟩
        · right
          exact ⟨U₁, U₂, rootedExceptional_near_to_main hNear⟩

end

end Erdos547b.ZhaoLemma77Full74

#print axioms Erdos547b.ZhaoLemma77Full74.lemma7_7_ideal_or_nearCore
#print axioms Erdos547b.ZhaoLemma77Full74.lemma7_7
