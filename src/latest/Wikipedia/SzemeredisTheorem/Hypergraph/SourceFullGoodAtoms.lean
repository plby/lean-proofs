import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedFullBoundary
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedRemoval

/-!
# Source-full good atoms and sharp bad-cell cleaning

The source hypergraph regularity argument tests the square of the usual
fine-immediate-boundary minus coarse-immediate-boundary defect after
conditioning on the join of every proper lower face.  This file implements
that test without changing the defect whose global square mass is paid for
by the ordinary adjacent-boundary atom-energy increment.

For a fixed upper atom, the bad base is the union of

* the usual low coarse-density support, observed on the immediate coarse
  boundary; and
* the support on which the full-lower conditional average of the same
  immediate-boundary defect square exceeds the chosen threshold.

Markov's inequality charges the second support directly to the immediate
atom-energy increment.  Summing over the disjoint upper atoms therefore
gives

```
upperComplexity * α + immediateAtomEnergyGap / β,
```

with no factor involving the complexity of the full-lower partition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace OrderedCoarseFineComplex

/-! ## Full-lower large-defect supports -/

/-- The immediate-boundary square defect of one selected upper atom.

The partition used to *average* this function below is the source-full lower
boundary, but the function itself remains the ordinary adjacent-boundary
fine-minus-coarse defect.  This is what permits the cleaning loss to be
charged to the existing atom-energy increment. -/
noncomputable def sourceFullAtomDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    (x : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  atomBoundaryDefectSq
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.fine e) e.face)
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face)
    upper a x

theorem sourceFullAtomDefectSq_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    0 ≤ P.sourceFullAtomDefectSq e upper a x := by
  exact atomBoundaryDefectSq_nonneg _ _ upper a x

/-- Full-lower coarse atoms on which the conditional square average of the
immediate-boundary defect exceeds `β`. -/
noncomputable def sourceFullLargeDefectBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  largeAverageBaseSupport
    (orderedFullLowerBoundaryPartition P.coarse e)
    (P.sourceFullAtomDefectSq e upper a) β

@[simp]
theorem mem_sourceFullLargeDefectBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (β : ℝ)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullLargeDefectBaseSupport e upper a β ↔
      β <
        conditionalMean
          (orderedFullLowerBoundaryPartition P.coarse e)
          (P.sourceFullAtomDefectSq e upper a) x := by
  exact
    mem_largeAverageBaseSupport
      (orderedFullLowerBoundaryPartition P.coarse e)
      (P.sourceFullAtomDefectSq e upper a) β x

/-- Markov accounting on the source-full boundary.  The right hand side is
the global mass of the *immediate* defect square, so no full-boundary
complexity enters. -/
theorem mul_mean_indicator_sourceFullLargeDefectBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (P.sourceFullLargeDefectBaseSupport e upper a β)) ≤
      mean (P.sourceFullAtomDefectSq e upper a) := by
  exact
    mul_mean_indicator_largeAverageBaseSupport_le
      (orderedFullLowerBoundaryPartition P.coarse e)
      (P.sourceFullAtomDefectSq e upper a)
      (P.sourceFullAtomDefectSq_nonneg e upper a)
      hβ

/-- The same Markov loss charged to the existing immediate-boundary
aggregate atom-energy increment.  This coarse bound is convenient when a
single selected atom is considered; the sharper own-atom sum below retains
the individual square masses until after summation. -/
theorem mul_mean_indicator_sourceFullLargeDefectBaseSupport_le_atomEnergy_sub
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (P.sourceFullLargeDefectBaseSupport e upper a β)) ≤
      orderedAtomEnergy
          (positiveFaceLowerLayer P.fine e) e.face upper -
        orderedAtomEnergy
          (positiveFaceLowerLayer P.coarse e) e.face upper := by
  refine
    (P.mul_mean_indicator_sourceFullLargeDefectBaseSupport_le
      e upper a hβ).trans ?_
  change
    mean
        (atomBoundaryDefectSq
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.fine e) e.face)
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          upper a) ≤
      partitionAtomEnergy
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.fine e) e.face) upper -
        partitionAtomEnergy
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face) upper
  exact
    mean_atomBoundaryDefectSq_le_atomEnergy_sub
      (orderedBoundaryPartition_mono
        (fun f => P.refines e.lowerRank.castSucc f) e.face)
      upper a

/-- Divided form of the source-full Markov estimate. -/
theorem mean_indicator_sourceFullLargeDefectBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {β : ℝ} (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullLargeDefectBaseSupport e upper a β)) ≤
      mean (P.sourceFullAtomDefectSq e upper a) / β := by
  apply (le_div_iff₀ hβ).2
  simpa [mul_comm] using
    P.mul_mean_indicator_sourceFullLargeDefectBaseSupport_le
      e upper a hβ.le

/-! ## Low-density union and own-atom accounting -/

/-- The adjacent-boundary atom-energy gap is exactly the sum of the
source-full defect-square masses.  The full-lower partition is used only
to localize those masses and therefore does not occur in this identity. -/
theorem orderedAtomEnergy_sub_eq_sum_mean_sourceFullAtomDefectSq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G)) :
    orderedAtomEnergy
          (positiveFaceLowerLayer P.fine e) e.face upper -
        orderedAtomEnergy
          (positiveFaceLowerLayer P.coarse e) e.face upper =
      ∑ a : upper.parts,
        mean (P.sourceFullAtomDefectSq e upper a) := by
  rw [orderedAtomEnergy_sub_eq_sum_mean_sq
    (fine := positiveFaceLowerLayer P.fine e)
    (coarse := positiveFaceLowerLayer P.coarse e)
    (fun f => P.refines e.lowerRank.castSucc f)
    e.face upper]
  rfl

/-- The source-full bad base for one upper atom.  Its density component is
still measured on the immediate coarse boundary, exactly as in the mixed
counting decomposition. -/
noncomputable def sourceFullAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  smallAverageBaseSupport
      (orderedBoundaryPartition
        (positiveFaceLowerLayer P.coarse e) e.face)
      (partitionAtomIndicator upper a) α ∪
    P.sourceFullLargeDefectBaseSupport e upper a β

@[simp]
theorem mem_sourceFullAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts) (α β : ℝ)
    (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullAtomBadBaseSupport e upper a α β ↔
      conditionalMean
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          (partitionAtomIndicator upper a) x < α ∨
        β <
          conditionalMean
            (orderedFullLowerBoundaryPartition P.coarse e)
            (P.sourceFullAtomDefectSq e upper a) x := by
  rw [sourceFullAtomBadBaseSupport, Finset.mem_union,
    mem_smallAverageBaseSupport,
    P.mem_sourceFullLargeDefectBaseSupport]

/-- The local bad part of one upper atom costs one density threshold plus
the mean square of that atom's immediate defect divided by `β`. -/
theorem mean_indicator_atom_inter_sourceFullAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (a : upper.parts)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (a.1 ∩ P.sourceFullAtomBadBaseSupport
          e upper a α β)) ≤
      α + mean (P.sourceFullAtomDefectSq e upper a) / β := by
  calc
    mean (finsetIndicator
        (a.1 ∩ P.sourceFullAtomBadBaseSupport
          e upper a α β)) ≤
        mean (finsetIndicator
          (a.1 ∩
            smallAverageBaseSupport
              (orderedBoundaryPartition
                (positiveFaceLowerLayer P.coarse e) e.face)
              (partitionAtomIndicator upper a) α)) +
          mean (finsetIndicator
            (P.sourceFullLargeDefectBaseSupport
              e upper a β)) := by
      exact
        mean_indicator_inter_union_le_add
          a.1
          (smallAverageBaseSupport
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) α)
          (P.sourceFullLargeDefectBaseSupport e upper a β)
    _ ≤
        α + mean (P.sourceFullAtomDefectSq e upper a) / β :=
      add_le_add
        (mean_indicator_inter_smallAverageBaseSupport_le
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          a.1 hα)
        (P.mean_indicator_sourceFullLargeDefectBaseSupport_le
          e upper a hβ)

/-- Union over all upper atoms of the part of that atom lying above its own
source-full bad base. -/
noncomputable def sourceFullOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) := by
  classical
  exact
    (Finset.univ : Finset upper.parts).biUnion fun a =>
      a.1 ∩ P.sourceFullAtomBadBaseSupport e upper a α β

@[simp]
theorem mem_sourceFullOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    (α β : ℝ) (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullOwnAtomBadBaseSupport e upper α β ↔
      x ∈ P.sourceFullAtomBadBaseSupport e upper
        (partitionAtomAt upper x) α β := by
  classical
  constructor
  · intro hx
    rw [sourceFullOwnAtomBadBaseSupport] at hx
    obtain ⟨a, _ha, hxpart⟩ :=
      Finset.mem_biUnion.mp hx
    have hxa : x ∈ a.1 :=
      (Finset.mem_inter.mp hxpart).1
    have hbad :
        x ∈ P.sourceFullAtomBadBaseSupport
          e upper a α β :=
      (Finset.mem_inter.mp hxpart).2
    have hcanonical : partitionAtomAt upper x = a :=
      (partitionAtomAt_eq_iff_mem upper x a).2 hxa
    simpa [hcanonical] using hbad
  · intro hbad
    rw [sourceFullOwnAtomBadBaseSupport]
    apply Finset.mem_biUnion.mpr
    refine ⟨partitionAtomAt upper x, Finset.mem_univ _, ?_⟩
    exact Finset.mem_inter.mpr
      ⟨upper.mem_part (Finset.mem_univ x), hbad⟩

/-- **Sharp source-full own-atom cleaning estimate.**  The source-full
partition appears only in Markov localization.  The quantitative loss is
the upper complexity times `α` plus the existing immediate-boundary
atom-energy gap divided by `β`. -/
theorem mean_indicator_sourceFullOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullOwnAtomBadBaseSupport
          e upper α β)) ≤
      (FacePartition.complexity upper : ℝ) * α +
        (orderedAtomEnergy
            (positiveFaceLowerLayer P.fine e) e.face upper -
          orderedAtomEnergy
            (positiveFaceLowerLayer P.coarse e) e.face upper) / β := by
  calc
    mean (finsetIndicator
        (P.sourceFullOwnAtomBadBaseSupport
          e upper α β)) ≤
        ∑ a : upper.parts,
          mean (finsetIndicator
            (a.1 ∩ P.sourceFullAtomBadBaseSupport
              e upper a α β)) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ : Finset upper.parts)
          (fun a =>
            a.1 ∩ P.sourceFullAtomBadBaseSupport
              e upper a α β)
    _ ≤
        ∑ a : upper.parts,
          (α + mean
            (P.sourceFullAtomDefectSq e upper a) / β) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact
        P.mean_indicator_atom_inter_sourceFullAtomBadBaseSupport_le
          e upper a hα hβ
    _ =
        (FacePartition.complexity upper : ℝ) * α +
          (orderedAtomEnergy
              (positiveFaceLowerLayer P.fine e) e.face upper -
            orderedAtomEnergy
              (positiveFaceLowerLayer P.coarse e) e.face upper) / β := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div]
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      rw [Fintype.card_coe]
      rw [← P.orderedAtomEnergy_sub_eq_sum_mean_sourceFullAtomDefectSq
        e upper]
      rfl

/-! ## The coarse upper partition selected by configurations -/

/-- Source-full own-atom bad support for the coarse upper partition used by
mixed configuration counting. -/
noncomputable def sourceFullCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) :
    Finset (Fin (e.lowerRank.1 + 1) → G) :=
  P.sourceFullOwnAtomBadBaseSupport e
    (P.coarse.partition e.lowerRank.succ e.face) α β

@[simp]
theorem mem_sourceFullCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (α β : ℝ) (x : Fin (e.lowerRank.1 + 1) → G) :
    x ∈ P.sourceFullCoarseOwnAtomBadBaseSupport e α β ↔
      x ∈ P.sourceFullAtomBadBaseSupport e
        (P.coarse.partition e.lowerRank.succ e.face)
        (partitionAtomAt
          (P.coarse.partition e.lowerRank.succ e.face) x)
        α β := by
  exact
    P.mem_sourceFullOwnAtomBadBaseSupport e
      (P.coarse.partition e.lowerRank.succ e.face) α β x

/-- Specialized sharp cleaning estimate for the coarse upper atoms used by
the source mixed counting argument. -/
theorem mean_indicator_sourceFullCoarseOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullCoarseOwnAtomBadBaseSupport e α β)) ≤
      (FacePartition.complexity
          (P.coarse.partition e.lowerRank.succ e.face) : ℝ) * α +
        P.coarseUpperFaceAtomEnergyGap
          e.lowerRank e.face / β := by
  unfold sourceFullCoarseOwnAtomBadBaseSupport
    coarseUpperFaceAtomEnergyGap
  exact
    P.mean_indicator_sourceFullOwnAtomBadBaseSupport_le
      e (P.coarse.partition e.lowerRank.succ e.face) hα hβ

end OrderedCoarseFineComplex

/-! ## Avoidance implies source-full mixed goodness -/

/-- On the selected full-lower atom, the mixed defect is pointwise equal to
the ordinary immediate-boundary atom defect. -/
theorem sourceFullMixedDefect_eq_orderedAtomBoundaryDefect_of_mem
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G)
    (hy :
      y ∈
        (orderedFullLowerBoundaryPartition P.coarse e).part
          (orderedFaceTuple e.face A.witness)) :
    sourceFullMixedDefect P A e y =
      orderedAtomBoundaryDefect
        (positiveFaceLowerLayer P.fine e)
        (positiveFaceLowerLayer P.coarse e)
        e.face
        (P.coarse.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face) y := by
  have himmediate :
      y ∈
        (orderedBoundaryPartition
          (positiveFaceLowerLayer P.coarse e) e.face).part
          (orderedFaceTuple e.face A.witness) :=
    FacePartition.part_subset_of_le
      (orderedFullLowerBoundaryPartition_le_immediate
        P.coarse e)
      (orderedFaceTuple e.face A.witness) hy
  have hindicator :
      mixedConfigurationBoundaryIndicator P A e y = 1 := by
    unfold mixedConfigurationBoundaryIndicator
    exact partitionAtomIndicator_of_mem _ _ himmediate
  have h :=
    mixedConfigurationDefect_mul_boundaryIndicator P A e y
  rw [hindicator, mul_one, mul_one] at h
  simpa [sourceFullMixedDefect] using h

/-- Consequently, conditioning the mixed defect square on the selected
full-lower atom is the same as conditioning the immediate atom defect
square there. -/
theorem conditionalMean_sourceFullMixedDefect_sq_eq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (fun y => sourceFullMixedDefect P A e y ^ 2)
        (orderedFaceTuple e.face A.witness) =
      conditionalMean
        (orderedFullLowerBoundaryPartition P.coarse e)
        (P.sourceFullAtomDefectSq e
          (P.coarse.partition e.lowerRank.succ e.face)
          (A.atom e.lowerRank.succ e.face))
        (orderedFaceTuple e.face A.witness) := by
  unfold conditionalMean
  apply Finset.expect_congr rfl
  intro y hy
  rw [sourceFullMixedDefect_eq_orderedAtomBoundaryDefect_of_mem
    P A e y hy]
  rfl

namespace ClosedOrderedAtomConfiguration

/-- A coarse closed configuration avoids the source-full cleaning support
when its selected tuple misses its own bad base at every positive face. -/
def AvoidsSourceFullBadBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ e : PositiveOrderedFace k r,
    orderedFaceTuple e.face A.witness ∉
      P.sourceFullCoarseOwnAtomBadBaseSupport e
        (α e.rank) (β e.rank)

/-- Avoidance of the own coarse upper atom's source-full bad base implies
source mixed goodness at one positive face. -/
theorem sourceFullMixedGoodAtFace_of_not_mem_badBase
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (α β : ℝ)
    (havoid :
      orderedFaceTuple e.face A.witness ∉
        P.sourceFullCoarseOwnAtomBadBaseSupport e α β) :
    SourceFullMixedGoodAtFace P A e α β := by
  let upper :=
    P.coarse.partition e.lowerRank.succ e.face
  let a : upper.parts :=
    A.atom e.lowerRank.succ e.face
  let x : Fin (e.lowerRank.1 + 1) → G :=
    orderedFaceTuple e.face A.witness
  have hcanonical :
      partitionAtomAt upper x = a := by
    exact (A.atom_eq_partitionAtomAt
      e.lowerRank.succ e.face).symm
  have hlocal :
      x ∉ P.sourceFullAtomBadBaseSupport
        e upper a α β := by
    intro hbad
    apply havoid
    apply
      (P.mem_sourceFullCoarseOwnAtomBadBaseSupport
        e α β x).2
    change
      x ∈ P.sourceFullAtomBadBaseSupport
        e upper (partitionAtomAt upper x) α β
    rw [hcanonical]
    exact hbad
  have hlow :
      x ∉
        smallAverageBaseSupport
          (orderedBoundaryPartition
            (positiveFaceLowerLayer P.coarse e) e.face)
          (partitionAtomIndicator upper a) α := by
    intro h
    exact hlocal (Finset.mem_union_left _ h)
  have hlarge :
      x ∉
        P.sourceFullLargeDefectBaseSupport
          e upper a β := by
    intro h
    exact hlocal (Finset.mem_union_right _ h)
  constructor
  · have hdensity :
        α ≤
          conditionalMean
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) x :=
      not_lt.mp fun h =>
        hlow
          ((mem_smallAverageBaseSupport
            (orderedBoundaryPartition
              (positiveFaceLowerLayer P.coarse e) e.face)
            (partitionAtomIndicator upper a) α x).2 h)
    simpa [sourceFullMixedCoarseDensity,
      mixedConfigurationCoarseDensity, upper, a, x,
      orderedBoundaryStructured] using hdensity
  · rw [conditionalMean_sourceFullMixedDefect_sq_eq P A e]
    have hdefect :
        conditionalMean
            (orderedFullLowerBoundaryPartition P.coarse e)
            (P.sourceFullAtomDefectSq e upper a) x ≤
          β :=
      not_lt.mp fun h =>
        hlarge
          ((P.mem_sourceFullLargeDefectBaseSupport
            e upper a β x).2 h)
    simpa [upper, a, x] using hdefect

/-- Simultaneous avoidance of the source-full bad base at every positive
face implies the all-face source-goodness predicate used by counting. -/
theorem isSourceFullMixedGood_of_avoids_badBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (havoid : A.AvoidsSourceFullBadBases P α β) :
    A.IsSourceFullMixedGood P α β := by
  intro e
  exact
    A.sourceFullMixedGoodAtFace_of_not_mem_badBase
      P e (α e.rank) (β e.rank) (havoid e)

end ClosedOrderedAtomConfiguration

end Wikipedia.SzemeredisTheorem
