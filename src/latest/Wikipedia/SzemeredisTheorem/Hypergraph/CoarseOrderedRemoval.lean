import Wikipedia.SzemeredisTheorem.Hypergraph.CoarseAtomBridge
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedRemoval

/-!
# Bad-base cleaning for coarse ordered atom configurations

The existing ordered cleaning argument selects upper atoms from the fine
complex.  For the eventual removal contradiction it is useful instead to
select a closed configuration in the fixed coarse complex.  The boundary
comparison is still mixed: conditional densities and square defects compare
the fine lower boundary with the coarse lower boundary, but the selected
upper atom belongs to the coarse upper partition.

This file packages that mixed goodness predicate, its own-coarse-atom bad
support, and the associated top-face deletion family.  The direct cleaning
bound is

```
coarseUpperComplexity * α + coarseUpperAtomEnergyGap / β.
```

`CoarseAtomBridge` then replaces the coarse-upper gap by one fine-upper
complexity factor times the existing fine-upper atom-energy gap.  No
configuration counting or parameter selection is performed here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Coarse-own-atom bad bases -/

namespace OrderedCoarseFineComplex

/-- Tuples whose mixed fine/coarse boundary lies in the bad base attached
to their own atom of the coarse upper face partition. -/
noncomputable def orderedCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r)
    (e : OrderedFace k (j.1 + 1))
    (α β : ℝ) :
    Finset (Fin (j.1 + 1) → G) :=
  orderedOwnAtomBadBaseSupport
    (P.fine.partition j.castSucc)
    (P.coarse.partition j.castSucc)
    e
    (P.coarse.partition j.succ e)
    α β

@[simp]
theorem mem_orderedCoarseOwnAtomBadBaseSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r)
    (e : OrderedFace k (j.1 + 1))
    (α β : ℝ) (x : Fin (j.1 + 1) → G) :
    x ∈ P.orderedCoarseOwnAtomBadBaseSupport j e α β ↔
      x ∈ orderedAtomBadBaseSupport
        (P.fine.partition j.castSucc)
        (P.coarse.partition j.castSucc)
        e
        (P.coarse.partition j.succ e)
        (partitionAtomAt
          (P.coarse.partition j.succ e) x)
        α β := by
  exact
    mem_orderedOwnAtomBadBaseSupport
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.castSucc)
      e (P.coarse.partition j.succ e) α β x

/-- The direct own-coarse-atom cleaning estimate on one ordered face. -/
theorem mean_indicator_orderedCoarseOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r)
    (e : OrderedFace k (j.1 + 1))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.orderedCoarseOwnAtomBadBaseSupport
          j e α β)) ≤
      (FacePartition.complexity
          (P.coarse.partition j.succ e) : ℝ) * α +
        P.coarseUpperFaceAtomEnergyGap j e / β := by
  unfold orderedCoarseOwnAtomBadBaseSupport
    coarseUpperFaceAtomEnergyGap
  apply
    mean_indicator_orderedOwnAtomBadBaseSupport_le
      (fun f => P.refines j.castSucc f)
      e (P.coarse.partition j.succ e) hα hβ

end OrderedCoarseFineComplex

/-! ## Mixed goodness for a coarse closed configuration -/

namespace ClosedOrderedAtomConfiguration

/-- Goodness at one successor-rank face for a configuration whose selected
upper atom is coarse, while the conditioned boundary comparison remains
fine versus coarse. -/
def IsMixedGoodAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (j : ℕ) (hj : j < r)
    (e : OrderedFace k (j + 1))
    (α β : ℝ) : Prop :=
  OrderedAtomIsGoodAtBoundary
    (P.fine.partition
      (⟨j, hj⟩ : Fin r).castSucc)
    (P.coarse.partition
      (⟨j, hj⟩ : Fin r).castSucc)
    e
    (P.coarse.partition
      (⟨j, hj⟩ : Fin r).succ e)
    (A.atom (⟨j, hj⟩ : Fin r).succ e)
    (orderedFaceTuple e A.witness)
    α β

/-- Rank-dependent mixed goodness for a realizable coarse closed atom
configuration. -/
def IsMixedGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) : Prop :=
  ∀ (j : ℕ) (hj : j < r) (e : OrderedFace k (j + 1)),
    A.IsMixedGoodAt P j hj e
      (α (j + 1)) (β (j + 1))

/-- Avoiding the coarse-own-atom bad support makes the selected coarse
atom mixed-good at that face. -/
theorem isMixedGoodAt_of_not_mem_coarseBadBase
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (j : ℕ) (hj : j < r)
    (e : OrderedFace k (j + 1))
    (α β : ℝ)
    (havoid :
      orderedFaceTuple e A.witness ∉
        P.orderedCoarseOwnAtomBadBaseSupport
          ⟨j, hj⟩ e α β) :
    A.IsMixedGoodAt P j hj e α β := by
  apply
    orderedAtomIsGoodAtBoundary_of_not_mem_badBase
      (P.fine.partition
        (⟨j, hj⟩ : Fin r).castSucc)
      (P.coarse.partition
        (⟨j, hj⟩ : Fin r).castSucc)
      e
      (P.coarse.partition
        (⟨j, hj⟩ : Fin r).succ e)
      (A.atom (⟨j, hj⟩ : Fin r).succ e)
      (orderedFaceTuple e A.witness)
      α β
  intro hbad
  apply havoid
  unfold
    OrderedCoarseFineComplex.orderedCoarseOwnAtomBadBaseSupport
    orderedOwnAtomBadBaseSupport
    ownAtomBadBaseSupport
  apply Finset.mem_biUnion.mpr
  refine
    ⟨A.atom (⟨j, hj⟩ : Fin r).succ e,
      Finset.mem_univ _, ?_⟩
  exact Finset.mem_inter.mpr
    ⟨A.mem_atom (⟨j, hj⟩ : Fin r).succ e, hbad⟩

/-- Facewise avoidance of all coarse-own-atom bad bases implies global
mixed goodness. -/
theorem isMixedGood_of_avoids_coarseBadBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (havoid :
      ∀ (j : ℕ) (hj : j < r)
        (e : OrderedFace k (j + 1)),
        orderedFaceTuple e A.witness ∉
          P.orderedCoarseOwnAtomBadBaseSupport
            ⟨j, hj⟩ e
            (α (j + 1)) (β (j + 1))) :
    A.IsMixedGood P α β := by
  intro j hj e
  exact
    A.isMixedGoodAt_of_not_mem_coarseBadBase
      P j hj e (α (j + 1)) (β (j + 1))
      (havoid j hj e)

end ClosedOrderedAtomConfiguration

/-! ## Pullback to top faces -/

namespace OrderedCoarseFineComplex

/-- Delete a top tuple when one of its positive-rank subfaces lies in the
mixed bad base attached to its own coarse upper atom. -/
noncomputable def orderedCoarseTopBadBaseDeletion
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
        (P.orderedCoarseOwnAtomBadBaseSupport
          q.1 (q.2.trans e)
          (α (q.1.1 + 1))
          (β (q.1.1 + 1)))

/-- The coarse bad-base top deletions, one for every top ordered face. -/
noncomputable def orderedCoarseBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  fun e => P.orderedCoarseTopBadBaseDeletion e α β

/-- Direct union-bound cost of the coarse-own-atom top deletion. -/
theorem mean_indicator_orderedCoarseTopBadBaseDeletion_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1)) :
    mean (finsetIndicator
        (P.orderedCoarseTopBadBaseDeletion e α β)) ≤
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
        (P.orderedCoarseTopBadBaseDeletion e α β)) ≤
        ∑ q : OrderedPositiveSubface r,
          mean (finsetIndicator
            (orderedFacePullbackFinset q.2
              (P.orderedCoarseOwnAtomBadBaseSupport
                q.1 (q.2.trans e)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ :
            Finset (OrderedPositiveSubface r))
          (fun q =>
            orderedFacePullbackFinset q.2
              (P.orderedCoarseOwnAtomBadBaseSupport
                q.1 (q.2.trans e)
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
        mean_indicator_orderedCoarseOwnAtomBadBaseSupport_le
          P q.1 (q.2.trans e)
          (hα q.1.1) (hβ q.1.1)

/-- Per-top-face density bound in terms of coarse-upper complexity and the
coarse-upper atom-energy gap. -/
theorem faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.orderedCoarseBadBaseDeletionFamily α β) e ≤
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
          (P.orderedCoarseBadBaseDeletionFamily α β) e =
        mean (finsetIndicator
          (P.orderedCoarseTopBadBaseDeletion e α β)) by
    unfold OrderedPattern.faceDeletionDensity
      orderedCoarseBadBaseDeletionFamily
    rw [mean_finsetIndicator]]
  exact
    mean_indicator_orderedCoarseTopBadBaseDeletion_le
      P e α β hα hβ

/-- Coarse-atom deletion cost expressed entirely through the coarse/fine
upper complexities and the existing fine-upper face atom-energy gaps. -/
theorem faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_le_fineGap
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1))
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (P.orderedCoarseBadBaseDeletionFamily α β) e ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          ((FacePartition.complexity
              (P.fine.partition q.1.succ
                (q.2.trans e)) : ℝ) *
            P.faceAtomEnergyGap
              q.1 (q.2.trans e)) /
            β (q.1.1 + 1)) := by
  calc
    OrderedPattern.faceDeletionDensity
        (P.orderedCoarseBadBaseDeletionFamily α β) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) /
              β (q.1.1 + 1)) :=
      faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_le
        P α β hα hβ e
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            ((FacePartition.complexity
                (P.fine.partition q.1.succ
                  (q.2.trans e)) : ℝ) *
              P.faceAtomEnergyGap
                q.1 (q.2.trans e)) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      exact add_le_add
        (le_refl _)
        (div_le_div_of_nonneg_right
          (P.coarseUpperFaceAtomEnergyGap_le
            q.1 (q.2.trans e))
          (hβ q.1.1).le)

/-- Constant-threshold form using separate uniform bounds for coarse and
fine upper complexity and the existing total fine-upper atom-energy gap. -/
theorem faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_constant_le
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
        (P.orderedCoarseBadBaseDeletionFamily
          (fun _ => α) (fun _ => β)) e ≤
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
        ((coarseBound : ℝ) * α +
          (fineBound : ℝ) * P.totalAtomEnergyGap / β) := by
  calc
    OrderedPattern.faceDeletionDensity
        (P.orderedCoarseBadBaseDeletionFamily
          (fun _ => α) (fun _ => β)) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) * α +
            ((FacePartition.complexity
                (P.fine.partition q.1.succ
                  (q.2.trans e)) : ℝ) *
              P.faceAtomEnergyGap
                q.1 (q.2.trans e)) / β) := by
      exact
        faceDeletionDensity_orderedCoarseBadBaseDeletionFamily_le_fineGap
          P (fun _ => α) (fun _ => β)
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
              P.faceAtomEnergyGap
                q.1 (q.2.trans e) ≤
              (fineBound : ℝ) *
                P.faceAtomEnergyGap
                  q.1 (q.2.trans e) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr
                (hfine q.1.succ (q.2.trans e)))
              (P.faceAtomEnergyGap_nonneg
                q.1 (q.2.trans e))
          _ ≤
              (fineBound : ℝ) *
                P.totalAtomEnergyGap :=
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

/-! ## Surviving tuples induce mixed-good coarse configurations -/

namespace ClosedOrderedAtomConfiguration

/-- If a full tuple avoids every coarse-own-atom top deletion, its
canonical coarse atom configuration is mixed-good at every positive rank. -/
theorem isMixedGood_of_avoids_coarseTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (hrk : r ≤ k)
    (P : OrderedCoarseFineComplex G k r)
    (x : Fin k → G) (α β : ℕ → ℝ)
    (havoid :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∉
          P.orderedCoarseTopBadBaseDeletion e α β) :
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).IsMixedGood P α β := by
  apply
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).isMixedGood_of_avoids_coarseBadBases
      P α β
  intro j hj f hbad
  obtain ⟨e, d, hde⟩ :=
    exists_orderedFace_factor_through
      (Nat.succ_le_iff.mpr hj) hrk f
  apply havoid e
  rw [
    OrderedCoarseFineComplex.orderedCoarseTopBadBaseDeletion]
  apply Finset.mem_biUnion.mpr
  refine
    ⟨⟨⟨j, hj⟩, d⟩, Finset.mem_univ _, ?_⟩
  rw [mem_orderedFacePullbackFinset]
  have htuple :
      orderedFaceTuple d (orderedFaceTuple e x) =
        orderedFaceTuple f x := by
    rw [show
        orderedFaceTuple d (orderedFaceTuple e x) =
          orderedFaceTuple (d.trans e) x by rfl,
      hde]
  rw [htuple, hde]
  exact hbad

end ClosedOrderedAtomConfiguration

end Wikipedia.SzemeredisTheorem
