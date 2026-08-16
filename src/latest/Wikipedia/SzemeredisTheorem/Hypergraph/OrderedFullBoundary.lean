import Wikipedia.SzemeredisTheorem.Hypergraph.CoarseConfigurationCounting

/-!
# Full lower boundaries of ordered faces

The source hypergraph regularity argument conditions an upper face on the
join of the partitions carried by *all* of its nonempty proper subfaces.
The adjacent-rank boundary in `OrderedBoundaryPartition` is enough to encode
closedness, but it does not expose this source-level sigma algebra directly.

This file constructs that full lower boundary.  A proper positive subface of
an `n + 1` tuple is represented by a positive ordered face of that tuple
whose rank is at most `n`.  Each genuine partition in the ambient ordered
complex is pulled back to the selected upper tuple space, and the full lower
boundary is their finite common refinement.

The last section packages the coarse/fine defect and the corresponding
source mixed-goodness condition.  Its principal consequence is the localized
weighted square-defect estimate on the selected full-lower atom.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Proper positive subfaces -/

/-- Every nonempty proper ordered subface of an `n + 1` tuple.

The `lowerRank` field of `PositiveOrderedFace (n + 1) n` ranges over
`0, ..., n - 1`, so its actual rank ranges over `1, ..., n`. -/
abbrev ProperPositiveOrderedSubface (n : ℕ) :=
  PositiveOrderedFace (n + 1) n

@[simp]
theorem properPositiveOrderedSubface_rank_lt_upper {n : ℕ}
    (d : ProperPositiveOrderedSubface n) :
    d.rank < n + 1 := by
  simp only [PositiveOrderedFace.rank]
  exact Nat.succ_lt_succ d.lowerRank.2

/-! ## The full lower partition -/

/-- The layer of the ambient complex carrying a proper positive subface. -/
abbrev orderedFullLowerComplexRank
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    Fin (r + 1) :=
  ⟨d.lowerRank.1 + 1, by
    have hd : d.rank < e.rank := by
      exact properPositiveOrderedSubface_rank_lt_upper d
    have he : e.rank ≤ r := by
      simp only [PositiveOrderedFace.rank]
      exact e.lowerRank.2
    omega⟩

@[simp]
theorem orderedFullLowerComplexRank_val
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    (orderedFullLowerComplexRank e d).1 =
      d.lowerRank.1 + 1 :=
  rfl

/-- A local proper subface, transported into the ambient labelled face. -/
abbrev orderedFullLowerAmbientFace
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    OrderedFace k (d.lowerRank.1 + 1) :=
  d.face.trans e.face

/-- Restricting through the ambient face agrees with first selecting the
upper tuple and then selecting its local proper subface. -/
@[simp]
theorem orderedFaceTuple_orderedFullLowerAmbientFace
    {G : Type*} {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1)
    (x : Fin k → G) :
    orderedFaceTuple (orderedFullLowerAmbientFace e d) x =
      orderedFaceTuple d.face (orderedFaceTuple e.face x) :=
  rfl

/-- Pull the genuine partition on one proper ambient subface back to the
selected upper tuple space. -/
noncomputable def orderedFullLowerConstituentPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.pullback
    (orderedFaceTuple d.face)
    (C.partition
      (orderedFullLowerComplexRank e d)
      (orderedFullLowerAmbientFace e d))

/-- Common refinement of the pullbacks from every nonempty proper ordered
subface. -/
noncomputable def orderedFullLowerPositivePartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.joinFinset
    (Finset.univ :
      Finset (ProperPositiveOrderedSubface e.lowerRank.1))
    (orderedFullLowerConstituentPartition C e)

/-- The positive strict-subface join refines every constituent pullback. -/
theorem orderedFullLowerPositivePartition_le_constituent
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    orderedFullLowerPositivePartition C e ≤
      orderedFullLowerConstituentPartition C e d := by
  exact FacePartition.joinFinset_le_of_mem
    (orderedFullLowerConstituentPartition C e)
    (Finset.mem_univ d)

/-- Refining an ordered complex refines its positive strict-subface join. -/
theorem orderedFullLowerPositivePartition_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse)
    (e : PositiveOrderedFace k r) :
    orderedFullLowerPositivePartition fine e ≤
      orderedFullLowerPositivePartition coarse e := by
  apply FacePartition.le_joinFinset_iff.mpr
  intro d _hd
  exact le_trans
    (orderedFullLowerPositivePartition_le_constituent fine e d)
    (FacePartition.pullback_mono
      (orderedFaceTuple d.face)
      (hfc
        (orderedFullLowerComplexRank e d)
        (orderedFullLowerAmbientFace e d)))

/-- The source-faithful full lower boundary.  We explicitly join the
ordinary immediate boundary with the positive strict-subface join.  For
rank greater than one the immediate constituents already occur in the
positive join; for rank one the immediate rank-zero face space is a
singleton.  Keeping this harmless factor explicit makes the refinement to
the boundary used by the counting decomposition definitional. -/
noncomputable def orderedFullLowerBoundaryPartition
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition (Fin (e.lowerRank.1 + 1) → G) :=
  FacePartition.join
    (orderedBoundaryPartition
      (positiveFaceLowerLayer C e) e.face)
    (orderedFullLowerPositivePartition C e)

/-- The full lower boundary refines the immediate boundary used in the
standard coarse/fine counting decomposition. -/
theorem orderedFullLowerBoundaryPartition_le_immediate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    orderedFullLowerBoundaryPartition C e ≤
      orderedBoundaryPartition
        (positiveFaceLowerLayer C e) e.face := by
  exact FacePartition.join_le_left _ _

/-- The full lower boundary refines every positive proper-subface
constituent. -/
theorem orderedFullLowerBoundaryPartition_le_constituent
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    orderedFullLowerBoundaryPartition C e ≤
      orderedFullLowerConstituentPartition C e d := by
  exact le_trans
    (FacePartition.join_le_right _ _)
    (orderedFullLowerPositivePartition_le_constituent C e d)

/-- Refining an ordered complex refines the induced full lower boundary. -/
theorem orderedFullLowerBoundaryPartition_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse)
    (e : PositiveOrderedFace k r) :
    orderedFullLowerBoundaryPartition fine e ≤
      orderedFullLowerBoundaryPartition coarse e := by
  apply FacePartition.le_join_iff.mpr
  constructor
  · exact le_trans
      (orderedFullLowerBoundaryPartition_le_immediate fine e)
      (orderedBoundaryPartition_mono
        (fun f =>
          hfc e.lowerRank.castSucc f)
        e.face)
  · exact le_trans
      (FacePartition.join_le_right _ _)
      (orderedFullLowerPositivePartition_mono hfc e)

/-- Exact atom membership for the full lower boundary. -/
theorem mem_orderedFullLowerBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    y ∈ (orderedFullLowerBoundaryPartition C e).part x ↔
      y ∈
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face).part x ∧
        ∀ d : ProperPositiveOrderedSubface e.lowerRank.1,
          orderedFaceTuple d.face y ∈
            (C.partition
              (orderedFullLowerComplexRank e d)
              (orderedFullLowerAmbientFace e d)).part
              (orderedFaceTuple d.face x) := by
  rw [orderedFullLowerBoundaryPartition, FacePartition.part_join,
    Finset.mem_inter, orderedFullLowerPositivePartition,
    FacePartition.mem_part_joinFinset_iff]
  simp only [Finset.mem_univ, forall_const,
    orderedFullLowerConstituentPartition,
    FacePartition.mem_part_pullback_iff_image_mem]

/-- The same membership statement on full labelled ambient tuples. -/
theorem orderedFaceTuple_mem_orderedFullLowerBoundaryPartition_part_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin k → G) :
    orderedFaceTuple e.face y ∈
        (orderedFullLowerBoundaryPartition C e).part
          (orderedFaceTuple e.face x) ↔
      orderedFaceTuple e.face y ∈
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face).part
            (orderedFaceTuple e.face x) ∧
        ∀ d : ProperPositiveOrderedSubface e.lowerRank.1,
          orderedFaceTuple (orderedFullLowerAmbientFace e d) y ∈
            (C.partition
              (orderedFullLowerComplexRank e d)
              (orderedFullLowerAmbientFace e d)).part
              (orderedFaceTuple
                (orderedFullLowerAmbientFace e d) x) := by
  rw [mem_orderedFullLowerBoundaryPartition_part_iff]
  constructor
  · rintro ⟨hboundary, hsubfaces⟩
    refine ⟨hboundary, ?_⟩
    intro d
    rw [orderedFaceTuple_orderedFullLowerAmbientFace e d y,
      orderedFaceTuple_orderedFullLowerAmbientFace e d x]
    exact hsubfaces d
  · rintro ⟨hboundary, hsubfaces⟩
    refine ⟨hboundary, ?_⟩
    intro d
    have hd := hsubfaces d
    rw [orderedFaceTuple_orderedFullLowerAmbientFace e d y,
      orderedFaceTuple_orderedFullLowerAmbientFace e d x] at hd
    exact hd

/-- The number of full-lower atoms is bounded by the product of the
complexities of all genuine proper-subface partitions. -/
theorem complexity_orderedFullLowerBoundaryPartition_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    FacePartition.complexity
        (orderedFullLowerBoundaryPartition C e) ≤
      FacePartition.complexity
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face) *
        ∏ d : ProperPositiveOrderedSubface e.lowerRank.1,
          FacePartition.complexity
            (C.partition
              (orderedFullLowerComplexRank e d)
              (orderedFullLowerAmbientFace e d)) := by
  calc
    FacePartition.complexity
        (orderedFullLowerBoundaryPartition C e) ≤
        FacePartition.complexity
            (orderedBoundaryPartition
              (positiveFaceLowerLayer C e) e.face) *
          FacePartition.complexity
            (orderedFullLowerPositivePartition C e) := by
      exact FacePartition.complexity_join_le _ _
    _ ≤
        FacePartition.complexity
            (orderedBoundaryPartition
              (positiveFaceLowerLayer C e) e.face) *
          ∏ d : ProperPositiveOrderedSubface e.lowerRank.1,
            FacePartition.complexity
              (orderedFullLowerConstituentPartition C e d) := by
      exact Nat.mul_le_mul_left _
        (FacePartition.complexity_joinFinset_le
          (Finset.univ :
            Finset (ProperPositiveOrderedSubface e.lowerRank.1))
          (orderedFullLowerConstituentPartition C e))
    _ ≤
        FacePartition.complexity
            (orderedBoundaryPartition
              (positiveFaceLowerLayer C e) e.face) *
          ∏ d : ProperPositiveOrderedSubface e.lowerRank.1,
            FacePartition.complexity
              (C.partition
                (orderedFullLowerComplexRank e d)
                (orderedFullLowerAmbientFace e d)) := by
      apply Nat.mul_le_mul_left
      apply Finset.prod_le_prod
      · intro d _hd
        exact Nat.zero_le _
      · intro d _hd
        exact FacePartition.complexity_pullback_le
          (orderedFaceTuple d.face)
          (C.partition
            (orderedFullLowerComplexRank e d)
            (orderedFullLowerAmbientFace e d))

/-! ## Selected full-lower atoms and their weights -/

/-- Canonical full-lower atom containing a selected upper tuple. -/
noncomputable def orderedFullLowerBoundaryAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    (orderedFullLowerBoundaryPartition C e).parts :=
  partitionAtomAt (orderedFullLowerBoundaryPartition C e) x

@[simp]
theorem orderedFullLowerBoundaryAtomAt_val
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    (orderedFullLowerBoundaryAtomAt C e x).1 =
      (orderedFullLowerBoundaryPartition C e).part x :=
  rfl

/-- Indicator of the full-lower atom selected by `x`. -/
noncomputable def orderedFullLowerBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedFullLowerBoundaryPartition C e)
    (orderedFullLowerBoundaryAtomAt C e x)
    y

theorem orderedFullLowerBoundaryWeight_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ orderedFullLowerBoundaryWeight C e x y :=
  partitionAtomIndicator_nonneg _ _ _

theorem orderedFullLowerBoundaryWeight_le_one
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y ≤ 1 :=
  partitionAtomIndicator_le_one _ _ _

/-- The selected full-lower atom lies inside the selected immediate
boundary atom. -/
theorem orderedFullLowerBoundaryWeight_le_immediateWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y ≤
      partitionAtomIndicator
        (orderedBoundaryPartition
          (positiveFaceLowerLayer C e) e.face)
        (orderedBoundaryAtomAt
          (positiveFaceLowerLayer C e) e.face x)
        y := by
  by_cases hy :
      y ∈ (orderedFullLowerBoundaryPartition C e).part x
  · have himmediate :
        y ∈
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face).part x :=
      FacePartition.part_subset_of_le
        (orderedFullLowerBoundaryPartition_le_immediate C e)
        x hy
    rw [show orderedFullLowerBoundaryWeight C e x y = 1 by
          exact partitionAtomIndicator_of_mem _ _ hy,
      partitionAtomIndicator_of_mem _ _ himmediate]
  · rw [show orderedFullLowerBoundaryWeight C e x y = 0 by
          exact partitionAtomIndicator_of_not_mem _ _ hy]
    exact partitionAtomIndicator_nonneg _ _ _

@[simp]
theorem orderedFullLowerBoundaryWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y ^ 2 =
      orderedFullLowerBoundaryWeight C e x y :=
  partitionAtomIndicator_sq _ _ _

@[simp]
theorem orderedFullLowerBoundaryWeight_self
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x x = 1 := by
  apply partitionAtomIndicator_of_mem
  exact
    (orderedFullLowerBoundaryPartition C e).mem_part
      (Finset.mem_univ x)

/-- Support of the selected full-lower weight. -/
theorem orderedFullLowerBoundaryWeight_eq_one_iff
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y = 1 ↔
      y ∈ (orderedFullLowerBoundaryPartition C e).part x := by
  constructor
  · intro h
    by_contra hy
    have hz :
        orderedFullLowerBoundaryWeight C e x y = 0 :=
      partitionAtomIndicator_of_not_mem _ _ hy
    linarith
  · intro hy
    exact partitionAtomIndicator_of_mem _ _ hy

/-- Support expanded into all genuine proper subfaces. -/
theorem orderedFullLowerBoundaryWeight_eq_one_iff_all_subfaces
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (x y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFullLowerBoundaryWeight C e x y = 1 ↔
      y ∈
          (orderedBoundaryPartition
            (positiveFaceLowerLayer C e) e.face).part x ∧
        ∀ d : ProperPositiveOrderedSubface e.lowerRank.1,
          orderedFaceTuple d.face y ∈
            (C.partition
              (orderedFullLowerComplexRank e d)
              (orderedFullLowerAmbientFace e d)).part
              (orderedFaceTuple d.face x) := by
  rw [orderedFullLowerBoundaryWeight_eq_one_iff,
    mem_orderedFullLowerBoundaryPartition_part_iff]

/-! ## Source full-lower goodness -/

/-- Conditional expectation on the full lower boundary. -/
noncomputable def orderedFullLowerStructured
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r)
    (f : (Fin (e.lowerRank.1 + 1) → G) → ℝ) :
    (Fin (e.lowerRank.1 + 1) → G) → ℝ :=
  conditionalMean (orderedFullLowerBoundaryPartition C e) f

/-- The source density term is the existing immediate-boundary coarse
conditional density.  The full lower boundary is used to localize its
fine--coarse defect, not to alter the three-term counting decomposition. -/
noncomputable def sourceFullMixedCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mixedConfigurationCoarseDensity P A e

/-- The defect in the source-goodness test is the existing immediate
fine-boundary density minus immediate coarse-boundary density.  Conditioning
its square on the full strict lower atom is the extra source-faithful
localization. -/
noncomputable def sourceFullMixedDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  mixedConfigurationDefect P A e y

/-- The coarse full-lower atom selected by a closed configuration. -/
noncomputable def sourceFullMixedBoundaryWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedFullLowerBoundaryWeight P.coarse e
    (orderedFaceTuple e.face A.witness) y

@[simp]
theorem sourceFullMixedBoundaryWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    sourceFullMixedBoundaryWeight P A e y ^ 2 =
      sourceFullMixedBoundaryWeight P A e y :=
  orderedFullLowerBoundaryWeight_sq _ _ _ _

/-- Full-lower localization is supported inside the immediate coarse
boundary indicator from the standard mixed decomposition. -/
theorem sourceFullMixedBoundaryWeight_le_mixedConfigurationBoundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    sourceFullMixedBoundaryWeight P A e y ≤
      mixedConfigurationBoundaryIndicator P A e y := by
  exact orderedFullLowerBoundaryWeight_le_immediateWeight
    P.coarse e (orderedFaceTuple e.face A.witness) y

/-- Source mixed goodness at one positive face.  The first clause is the
coarse density floor.  The second is the conditional square average of the
fine--coarse defect on the selected full-lower coarse atom. -/
def SourceFullMixedGoodAtFace
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) : Prop :=
  α ≤ sourceFullMixedCoarseDensity P A e ∧
    conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (fun y => sourceFullMixedDefect P A e y ^ 2)
        (orderedFaceTuple e.face A.witness) ≤
      β

/-- Source mixed goodness simultaneously at every positive ordered face. -/
def ClosedOrderedAtomConfiguration.IsSourceFullMixedGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : PositiveOrderedFace k r,
    SourceFullMixedGoodAtFace P A e
      (α e.rank) (β e.rank)

/-- The global square-defect mass localized by the selected full-lower
coarse atom. -/
noncomputable def sourceFullMixedLocalizedDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  mean fun y =>
    sourceFullMixedDefect P A e y ^ 2 *
      sourceFullMixedBoundaryWeight P A e y

/-- Pointwise source goodness yields the localized weighted-defect estimate
used in the source counting argument. -/
theorem SourceFullMixedGoodAtFace.localized_defect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ)
    (hgood : SourceFullMixedGoodAtFace P A e α β) :
    sourceFullMixedLocalizedDefectSq P A e ≤
      β * mean (sourceFullMixedBoundaryWeight P A e) := by
  unfold sourceFullMixedLocalizedDefectSq
  apply mean_mul_partitionAtomIndicator_le
    (orderedFullLowerBoundaryPartition P.coarse e)
    (fun y => sourceFullMixedDefect P A e y ^ 2)
    (orderedFullLowerBoundaryAtomAt P.coarse e
      (orderedFaceTuple e.face A.witness))
  have hrep :
      (orderedFullLowerBoundaryPartition P.coarse e).representative
          (orderedFullLowerBoundaryAtomAt P.coarse e
            (orderedFaceTuple e.face A.witness)) ∈
        (orderedFullLowerBoundaryPartition P.coarse e).part
          (orderedFaceTuple e.face A.witness) := by
    exact
      (orderedFullLowerBoundaryPartition P.coarse e).representative_mem
        (orderedFullLowerBoundaryAtomAt P.coarse e
          (orderedFaceTuple e.face A.witness))
  have heq :=
    conditionalMean_eq_of_mem_part
      (orderedFullLowerBoundaryPartition P.coarse e)
      (fun y => sourceFullMixedDefect P A e y ^ 2)
      hrep
  rw [heq]
  exact hgood.2

/-- The all-face source-goodness predicate specializes to its localized
weighted-defect consequence at any positive face. -/
theorem ClosedOrderedAtomConfiguration.IsSourceFullMixedGood.localized_defect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (e : PositiveOrderedFace k r) :
    sourceFullMixedLocalizedDefectSq P A e ≤
      β e.rank *
        mean (sourceFullMixedBoundaryWeight P A e) :=
  (hgood e).localized_defect P A e
    (α e.rank) (β e.rank)

end Wikipedia.SzemeredisTheorem
