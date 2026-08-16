import Wikipedia.SzemeredisTheorem.Hypergraph.SourceFullGoodAtoms
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedRemovalTheorem

/-!
# Source-full bad-base cleaning and the ordered removal contradiction

The source-full counting argument conditions the usual adjacent-boundary
square defect on the join of every proper lower face.  `SourceFullGoodAtoms`
shows that cleaning the resulting bad bases nevertheless costs only

```
upper complexity * density threshold + adjacent atom-energy gap / defect threshold.
```

This file pulls those bad bases back to top faces, records the corresponding
normalized deletion bounds, and proves the semantic cover contradiction.  A
tuple surviving every top-face deletion induces its canonical coarse closed
configuration; factorization of each positive face through a top face shows
that this configuration avoids every source-full bad base and is therefore
source-full mixed-good.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace OrderedCoarseFineComplex

/-! ## Pulling source-full bad bases back to top faces -/

/-- Delete a top tuple when one of its positive-rank subfaces lies in the
source-full bad base attached to its own coarse upper atom. -/
noncomputable def sourceFullTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ) :
    Finset (Fin r → G) := by
  classical
  exact
    (Finset.univ :
      Finset (OrderedPositiveSubface r)).biUnion fun q =>
      orderedFacePullbackFinset q.2
        (P.sourceFullCoarseOwnAtomBadBaseSupport
          ({ lowerRank := q.1
             face := q.2.trans e } : PositiveOrderedFace k r)
          (α (q.1.1 + 1))
          (β (q.1.1 + 1)))

/-- Source-full bad-base deletions, one finite set for every top ordered
face. -/
noncomputable def sourceFullBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  fun e => P.sourceFullTopBadBaseDeletion e α β

/-- Direct normalized union-bound cost of one source-full top deletion. -/
theorem mean_indicator_sourceFullTopBadBaseDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1)) :
    mean (finsetIndicator
        (P.sourceFullTopBadBaseDeletion e α β)) ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  calc
    mean (finsetIndicator
        (P.sourceFullTopBadBaseDeletion e α β)) ≤
        ∑ q : OrderedPositiveSubface r,
          mean (finsetIndicator
            (orderedFacePullbackFinset q.2
              (P.sourceFullCoarseOwnAtomBadBaseSupport
                ({ lowerRank := q.1
                   face := q.2.trans e } :
                  PositiveOrderedFace k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ : Finset (OrderedPositiveSubface r))
          (fun q =>
            orderedFacePullbackFinset q.2
              (P.sourceFullCoarseOwnAtomBadBaseSupport
                ({ lowerRank := q.1
                   face := q.2.trans e } :
                  PositiveOrderedFace k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [mean_indicator_orderedFacePullbackFinset]
      exact
        P.mean_indicator_sourceFullCoarseOwnAtomBadBaseSupport_le
          ({ lowerRank := q.1
             face := q.2.trans e } : PositiveOrderedFace k r)
          (hα q.1.1) (hβ q.1.1)

/-- Per-top-face deletion density in terms of the coarse upper complexity and
the coarse-upper adjacent atom-energy gap. -/
theorem faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  rw [show
      OrderedPattern.faceDeletionDensity
          (P.sourceFullBadBaseDeletionFamily α β) e =
        mean (finsetIndicator
          (P.sourceFullTopBadBaseDeletion e α β)) by
    unfold OrderedPattern.faceDeletionDensity
      sourceFullBadBaseDeletionFamily
    rw [mean_finsetIndicator]]
  exact
    P.mean_indicator_sourceFullTopBadBaseDeletion_le
      e α β hα hβ

/-- The same normalized cost expressed through the fine upper complexity and
the ordinary fine-upper face atom-energy gap. -/
theorem faceDeletionDensity_sourceFullBadBaseDeletionFamily_le_fineGap
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          ((FacePartition.complexity
              (P.fine.partition q.1.succ
                (q.2.trans e)) : ℝ) *
            P.faceAtomEnergyGap q.1 (q.2.trans e)) /
            β (q.1.1 + 1)) := by
  calc
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily α β) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) /
              β (q.1.1 + 1)) :=
      P.faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
        α β hα hβ e
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            ((FacePartition.complexity
                (P.fine.partition q.1.succ
                  (q.2.trans e)) : ℝ) *
              P.faceAtomEnergyGap q.1 (q.2.trans e)) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      exact add_le_add
        (le_refl _)
        (div_le_div_of_nonneg_right
          (P.coarseUpperFaceAtomEnergyGap_le
            q.1 (q.2.trans e))
          (hβ q.1.1).le)

/-- Constant-threshold deletion bound using uniform coarse/fine complexity
bounds and the total ordinary atom-energy increment. -/
theorem faceDeletionDensity_sourceFullBadBaseDeletionFamily_constant_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r coarseBound fineBound : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (hcoarse :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (P.coarse.partition j e) ≤ coarseBound)
    (hfine :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (P.fine.partition j e) ≤ fineBound)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily
          (fun _ => α) (fun _ => β)) e ≤
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
        ((coarseBound : ℝ) * α +
          (fineBound : ℝ) * P.totalAtomEnergyGap / β) := by
  calc
    OrderedPattern.faceDeletionDensity
        (P.sourceFullBadBaseDeletionFamily
          (fun _ => α) (fun _ => β)) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) * α +
            ((FacePartition.complexity
                (P.fine.partition q.1.succ
                  (q.2.trans e)) : ℝ) *
              P.faceAtomEnergyGap q.1 (q.2.trans e)) / β) := by
      exact
        P.faceDeletionDensity_sourceFullBadBaseDeletionFamily_le_fineGap
          (fun _ => α) (fun _ => β)
          (fun _ => hα) (fun _ => hβ) e
    _ ≤
        ∑ _q : OrderedPositiveSubface r,
          ((coarseBound : ℝ) * α +
            (fineBound : ℝ) * P.totalAtomEnergyGap / β) := by
      apply Finset.sum_le_sum
      intro q _hq
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr
            (hcoarse q.1.succ (q.2.trans e)))
          hα
      · apply div_le_div_of_nonneg_right _ hβ.le
        calc
          (FacePartition.complexity
                (P.fine.partition q.1.succ
                  (q.2.trans e)) : ℝ) *
              P.faceAtomEnergyGap q.1 (q.2.trans e) ≤
              (fineBound : ℝ) *
                P.faceAtomEnergyGap q.1 (q.2.trans e) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr
                (hfine q.1.succ (q.2.trans e)))
              (P.faceAtomEnergyGap_nonneg
                q.1 (q.2.trans e))
          _ ≤
              (fineBound : ℝ) * P.totalAtomEnergyGap :=
            mul_le_mul_of_nonneg_left
              (P.faceAtomEnergyGap_le_total
                q.1 (q.2.trans e))
              (Nat.cast_nonneg fineBound)
    _ =
        (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          ((coarseBound : ℝ) * α +
            (fineBound : ℝ) * P.totalAtomEnergyGap / β) := by
      simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]

end OrderedCoarseFineComplex

/-! ## Surviving tuples are source-full mixed-good -/

namespace ClosedOrderedAtomConfiguration

/-- If a full tuple avoids every source-full top deletion, its canonical
coarse closed atom configuration is source-full mixed-good at every positive
face. -/
theorem isSourceFullMixedGood_of_avoids_sourceFullTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (hrk : r ≤ k)
    (P : OrderedCoarseFineComplex G k r)
    (x : Fin k → G) (α β : ℕ → ℝ)
    (havoid :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∉
          P.sourceFullTopBadBaseDeletion e α β) :
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).IsSourceFullMixedGood P α β := by
  apply
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).isSourceFullMixedGood_of_avoids_badBases
      P α β
  intro f hbad
  obtain ⟨e, d, hde⟩ :=
    exists_orderedFace_factor_through
      (Nat.succ_le_iff.mpr f.lowerRank.2) hrk f.face
  apply havoid e
  rw [OrderedCoarseFineComplex.sourceFullTopBadBaseDeletion]
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨f.lowerRank, d⟩, Finset.mem_univ _, ?_⟩
  rw [mem_orderedFacePullbackFinset]
  change
    orderedFaceTuple (d.trans e) x ∈
      P.sourceFullCoarseOwnAtomBadBaseSupport
        ({ lowerRank := f.lowerRank
           face := d.trans e } : PositiveOrderedFace k r)
        (α (f.lowerRank.1 + 1))
        (β (f.lowerRank.1 + 1))
  rw [hde]
  exact hbad

end ClosedOrderedAtomConfiguration

/-! ## Abstract source-good cover contradiction -/

/-- A uniform lower count for every source-full mixed-good coarse
configuration forces the source-full bad-base family to cover every
occurrence of the original pattern. -/
theorem sourceFullBadBaseDeletionFamily_isCover_of_sourceFullMixedGood_count
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ) (c : ℝ)
    (hcount : H.toWeighted.patternCount < c)
    (hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration
          G k (n + 1) P.coarse,
        A.IsSourceFullMixedGood P α β →
          c ≤ fullConfigurationCount A) :
    H.IsCover
      (P.sourceFullBadBaseDeletionFamily α β) := by
  intro x hx
  by_contra hsurvives
  push Not at hsurvives
  let A :
      ClosedOrderedAtomConfiguration
        G k (n + 1) P.coarse :=
    ClosedOrderedAtomConfiguration.ofTuple P.coarse x
  have hgood : A.IsSourceFullMixedGood P α β := by
    exact
      ClosedOrderedAtomConfiguration.isSourceFullMixedGood_of_avoids_sourceFullTopBadBaseDeletion
        hrk P x α β hsurvives
  have hcA : c ≤ fullConfigurationCount A :=
    hgoodCount A hgood
  have htop :
      OrderedFacePartitionRefines P.coarse.topLayer
        (orderedPatternTopPartition H) :=
    orderedPatternTopPartition_refines_of_complex_refines_initial
      H hinitial
  have hAH :
      fullConfigurationCount A ≤
        H.toWeighted.patternCount :=
    fullConfigurationCount_le_patternCount
      H htop A ((H.mem_occurrenceFinset x).1 hx)
  linarith

end Wikipedia.SzemeredisTheorem
