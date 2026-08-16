import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedCellLifting

/-!
# Shared ordered-face partitions and boundary pullbacks

The hypergraph-complex regularity proof uses one genuine partition on every
ordered lower face.  If `e` is an upper face, its boundary partition is not
an independently generated partition of the whole upper tuple space.  It is
the common refinement of the pullbacks of the shared partitions on the
immediate subfaces `eraseOrderedFace e i`.

This file implements that architecture.  Its central membership theorem says
that two upper tuples lie in the same boundary atom exactly when every pair
of erased tuples lies in the same atom of the corresponding genuine lower
face partition.  This is the compatibility needed for closed atom
configurations and localized energy estimates.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Coordinate deletion specialized to a successor arity.  This
definition has codomain `Fin j → G` on the nose, avoiding transports through
the propositionally equal expression `Fin (j + 1 - 1) → G`. -/
def eraseBoundaryCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    Fin j → G :=
  fun q => x (i.succAbove q)

/-- Immediate ordered subface specialized to a successor rank. -/
def eraseBoundaryFace
    {k j : ℕ}
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    OrderedFace k j :=
  (Fin.succAboveOrderEmb i).trans e

@[simp]
theorem orderedFaceTuple_eraseBoundaryFace
    {G : Type*} {k j : ℕ}
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1))
    (x : Fin k → G) :
    orderedFaceTuple (eraseBoundaryFace e i) x =
      eraseBoundaryCoordinate i (orderedFaceTuple e x) :=
  rfl

/-- A shared partition on every ordered face of one fixed rank. -/
abbrev OrderedFacePartitionSystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ) :=
  (e : OrderedFace k j) → FacePartition (Fin j → G)

/-- Pointwise refinement of shared ordered-face partitions. -/
def OrderedFacePartitionRefines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (fine coarse : OrderedFacePartitionSystem G k j) : Prop :=
  ∀ e, fine e ≤ coarse e

namespace OrderedFacePartitionRefines

theorem refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j) :
    OrderedFacePartitionRefines P P :=
  fun _ => le_rfl

theorem trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {P Q R : OrderedFacePartitionSystem G k j}
    (hPQ : OrderedFacePartitionRefines P Q)
    (hQR : OrderedFacePartitionRefines Q R) :
    OrderedFacePartitionRefines P R :=
  fun e => le_trans (hPQ e) (hQR e)

end OrderedFacePartitionRefines

/-- The indiscrete shared partition layer. -/
def indiscreteOrderedFacePartitionSystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ) :
    OrderedFacePartitionSystem G k j :=
  fun _ => FacePartition.indiscrete

/-- Pull one actual lower-face partition back to an upper tuple space. -/
def orderedImmediateBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.pullback (eraseBoundaryCoordinate i)
    (P (eraseBoundaryFace e i))

/-- Common refinement of the pullbacks from every immediate subface. -/
def orderedBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ : Finset (Fin (j + 1)))
    (orderedImmediateBoundaryPartition P e)

/-- The full boundary partition refines each one-coordinate pullback. -/
theorem orderedBoundaryPartition_le_immediate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1)) :
    orderedBoundaryPartition P e ≤
      orderedImmediateBoundaryPartition P e i := by
  exact FacePartition.joinFinset_le_of_mem
    (orderedImmediateBoundaryPartition P e)
    (Finset.mem_univ i)

/-- Refining all genuine lower-face partitions refines every induced
boundary partition. -/
theorem orderedBoundaryPartition_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1)) :
    orderedBoundaryPartition fine e ≤
      orderedBoundaryPartition coarse e := by
  unfold orderedBoundaryPartition
  apply FacePartition.le_joinFinset_iff.mpr
  intro i _
  exact le_trans
    (orderedBoundaryPartition_le_immediate fine e i)
    (FacePartition.pullback_mono (eraseBoundaryCoordinate i)
      (hfc (eraseBoundaryFace e i)))

/-- Exact boundary-atom membership: every erased upper tuple must belong to
the corresponding shared lower-face atom. -/
theorem mem_orderedBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin (j + 1) → G) :
    y ∈ (orderedBoundaryPartition P e).part x ↔
      ∀ i : Fin (j + 1),
        eraseBoundaryCoordinate i y ∈
          (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i x) := by
  rw [orderedBoundaryPartition,
    FacePartition.mem_part_joinFinset_iff]
  simp only [Finset.mem_univ, forall_const,
    orderedImmediateBoundaryPartition,
    FacePartition.mem_part_pullback_iff_image_mem]

/-- Equivalent same-atom formulation of boundary membership. -/
theorem mem_orderedBoundaryPartition_part_iff_part_eq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin (j + 1) → G) :
    y ∈ (orderedBoundaryPartition P e).part x ↔
      ∀ i : Fin (j + 1),
        (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i y) =
          (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i x) := by
  rw [mem_orderedBoundaryPartition_part_iff]
  constructor
  · intro h i
    exact
      ((P (eraseBoundaryFace e i)).mem_part_iff_part_eq_part
        (Finset.mem_univ (eraseBoundaryCoordinate i y))
        (Finset.mem_univ (eraseBoundaryCoordinate i x))).1
        (h i)
  · intro h i
    exact
      ((P (eraseBoundaryFace e i)).mem_part_iff_part_eq_part
        (Finset.mem_univ (eraseBoundaryCoordinate i y))
        (Finset.mem_univ (eraseBoundaryCoordinate i x))).2
        (h i)

/-- On full labelled tuples, boundary compatibility is precisely
compatibility on every actual immediate ordered subface. -/
theorem orderedFaceTuple_mem_boundary_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin k → G) :
    orderedFaceTuple e y ∈
        (orderedBoundaryPartition P e).part
          (orderedFaceTuple e x) ↔
      ∀ i : Fin (j + 1),
        orderedFaceTuple (eraseBoundaryFace e i) y ∈
          (P (eraseBoundaryFace e i)).part
            (orderedFaceTuple (eraseBoundaryFace e i) x) := by
  rw [mem_orderedBoundaryPartition_part_iff]
  constructor
  · intro h i
    rw [orderedFaceTuple_eraseBoundaryFace e i y,
      orderedFaceTuple_eraseBoundaryFace e i x]
    exact h i
  · intro h i
    rw [← orderedFaceTuple_eraseBoundaryFace e i y,
      ← orderedFaceTuple_eraseBoundaryFace e i x]
    exact h i

/-- A boundary common refinement has no more atoms than the product of the
atom counts of the genuine lower-face partitions. -/
theorem complexity_orderedBoundaryPartition_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1)) :
    FacePartition.complexity
        (orderedBoundaryPartition P e) ≤
      ∏ i : Fin (j + 1),
        FacePartition.complexity
          (P (eraseBoundaryFace e i)) := by
  calc
    FacePartition.complexity
        (orderedBoundaryPartition P e) ≤
        ∏ i : Fin (j + 1),
          FacePartition.complexity
            (orderedImmediateBoundaryPartition P e i) := by
      exact FacePartition.complexity_joinFinset_le
        (Finset.univ : Finset (Fin (j + 1)))
        (orderedImmediateBoundaryPartition P e)
    _ ≤
        ∏ i : Fin (j + 1),
          FacePartition.complexity
            (P (eraseBoundaryFace e i)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.zero_le _
      intro i _
      exact FacePartition.complexity_pullback_le
        (eraseBoundaryCoordinate i) (P (eraseBoundaryFace e i))

/-- A uniform lower-layer complexity bound raises to the number of boundary
coordinates. -/
theorem complexity_orderedBoundaryPartition_le_pow
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j M : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (hP : ∀ g, FacePartition.complexity (P g) ≤ M)
    (e : OrderedFace k (j + 1)) :
    FacePartition.complexity
        (orderedBoundaryPartition P e) ≤
      M ^ (j + 1) := by
  calc
    FacePartition.complexity
        (orderedBoundaryPartition P e) ≤
        ∏ i : Fin (j + 1),
          FacePartition.complexity
            (P (eraseBoundaryFace e i)) :=
      complexity_orderedBoundaryPartition_le P e
    _ ≤ ∏ _i : Fin (j + 1), M := by
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.zero_le _
      intro i _
      exact hP (eraseBoundaryFace e i)
    _ = M ^ (j + 1) := by simp

/-- Canonical boundary atom containing an upper tuple. -/
noncomputable def orderedBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x : Fin (j + 1) → G) :
    (orderedBoundaryPartition P e).parts :=
  ⟨(orderedBoundaryPartition P e).part x,
    (orderedBoundaryPartition P e).part_mem.2
      (Finset.mem_univ x)⟩

@[simp]
theorem orderedBoundaryAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x : Fin (j + 1) → G) :
    (orderedBoundaryAtomAt P e x).1 =
      (orderedBoundaryPartition P e).part x :=
  rfl

theorem mem_orderedBoundaryAtomAt_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (x y : Fin (j + 1) → G) :
    y ∈ (orderedBoundaryAtomAt P e x).1 ↔
      ∀ i : Fin (j + 1),
        eraseBoundaryCoordinate i y ∈
          (P (eraseBoundaryFace e i)).part
            (eraseBoundaryCoordinate i x) :=
  mem_orderedBoundaryPartition_part_iff P e x y

/-- Conditional mean of an upper-face function relative to its shared
immediate boundary. -/
noncomputable def orderedBoundaryStructured
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) :
    (Fin (j + 1) → G) → ℝ :=
  conditionalMean (orderedBoundaryPartition P e) f

/-- Energy of an upper-face function visible from its shared immediate
boundary. -/
noncomputable def orderedBoundaryEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (P : OrderedFacePartitionSystem G k j)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) : ℝ :=
  partitionEnergy (orderedBoundaryPartition P e) f

/-- Shared lower-face refinement increases every upper boundary energy. -/
theorem orderedBoundaryEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) :
    orderedBoundaryEnergy coarse e f ≤
      orderedBoundaryEnergy fine e f :=
  partitionEnergy_mono
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    (orderedBoundaryPartition_mono hfc e) f

/-- Pythagoras for coarse/fine shared boundary layers. -/
theorem orderedBoundaryEnergy_sub_eq_mean_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {fine coarse : OrderedFacePartitionSystem G k j}
    (hfc : OrderedFacePartitionRefines fine coarse)
    (e : OrderedFace k (j + 1))
    (f : (Fin (j + 1) → G) → ℝ) :
    orderedBoundaryEnergy fine e f -
        orderedBoundaryEnergy coarse e f =
      mean (fun x =>
        (orderedBoundaryStructured fine e f x -
          orderedBoundaryStructured coarse e f x) ^ 2) := by
  exact partitionEnergy_sub_eq_mean_sq
    (orderedBoundaryPartition fine e)
    (orderedBoundaryPartition coarse e)
    (orderedBoundaryPartition_mono hfc e) f

/-- A bounded hierarchy of shared partitions, one layer for every rank from
zero through `r`. -/
structure OrderedPartitionComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  partition :
    (j : Fin (r + 1)) →
      (e : OrderedFace k j.1) →
        FacePartition (Fin j.1 → G)

namespace OrderedPartitionComplex

/-- Extract a numerically indexed layer from a bounded partition complex. -/
def layer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (j : ℕ) (hj : j ≤ r) :
    OrderedFacePartitionSystem G k j :=
  C.partition ⟨j, Nat.lt_succ_iff.mpr hj⟩

/-- The immediate-boundary partition supplied by rank `j` of a complex. -/
def boundary
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r j : ℕ}
    (C : OrderedPartitionComplex G k r)
    (hj : j < r)
    (e : OrderedFace k (j + 1)) :
    FacePartition (Fin (j + 1) → G) :=
  orderedBoundaryPartition (C.layer j (Nat.le_of_lt hj)) e

/-- Pointwise refinement at every rank of two partition complexes. -/
def Refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r) : Prop :=
  ∀ j e, fine.partition j e ≤ coarse.partition j e

theorem Refines.refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    C.Refines C :=
  fun _ _ => le_rfl

theorem Refines.trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C D E : OrderedPartitionComplex G k r}
    (hCD : C.Refines D) (hDE : D.Refines E) :
    C.Refines E :=
  fun j e => le_trans (hCD j e) (hDE j e)

/-- Refinement of complexes induces refinement of every rank boundary. -/
theorem boundary_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r j : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse)
    (hj : j < r)
    (e : OrderedFace k (j + 1)) :
    fine.boundary hj e ≤ coarse.boundary hj e := by
  apply orderedBoundaryPartition_mono
  intro g
  exact hfc
    ⟨j, Nat.lt_succ_iff.mpr (Nat.le_of_lt hj)⟩ g

end OrderedPartitionComplex

end Wikipedia.SzemeredisTheorem
