import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedConfigurationCounting
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedPatternPartition
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedRemoval

/-!
# The ordered removal cover contradiction

This file joins the three semantic parts of ordered hypergraph removal.

* The top partition remembers the original edge predicates.
* A tuple surviving every bad-base deletion determines a good closed fine
  atom configuration.
* The configuration counting lemma gives every good configuration a
  uniform lower count.

Every tuple counted by the selected configuration remains an occurrence of
the original pattern, because its selected top atoms are edge-monochromatic.
Thus an occurrence surviving all deletions would force the original pattern
count above the assumed small-count threshold.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## The selected configuration lies inside the original pattern -/

/-- Regard a top face of successor rank as a positive ordered face. -/
def topPositiveOrderedFace
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    PositiveOrderedFace k (n + 1) where
  lowerRank := Fin.last n
  face := e

@[simp]
theorem topPositiveOrderedFace_rank
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    (topPositiveOrderedFace e).rank = n + 1 := by
  rfl

@[simp]
theorem topPositiveOrderedFace_lowerRank_succ
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    (topPositiveOrderedFace e).lowerRank.succ =
      Fin.last (n + 1) := by
  apply Fin.ext
  rfl

/-- If a full tuple is not an occurrence, then the full selected
configuration weight of an occurring closed configuration vanishes on that
tuple. -/
theorem partialConfigurationWeight_univ_eq_zero_of_not_occurrence
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness)
    {x : Fin k → G} (hx : ¬H.IsOccurrence x) :
    partialConfigurationWeight A Finset.univ x = 0 := by
  have hmissing :
      ∃ e : OrderedFace k (n + 1),
        orderedFaceTuple e x ∉
          (A.atom (Fin.last (n + 1)) e).1 := by
    by_contra h
    push Not at h
    exact hx
      (A.isOccurrence_of_mem_topAtoms
        H hC hA x h)
  obtain ⟨e, he⟩ := hmissing
  unfold partialConfigurationWeight
  apply Finset.prod_eq_zero
    (Finset.mem_univ (topPositiveOrderedFace e))
  unfold configurationFaceWeight
  change
    partitionAtomIndicator
        (C.partition (Fin.last (n + 1)) e)
        (A.atom (Fin.last (n + 1)) e)
        (orderedFaceTuple e x) =
      0
  exact
    partitionAtomIndicator_of_not_mem
      (C.partition (Fin.last (n + 1)) e)
      (A.atom (Fin.last (n + 1)) e) he

/-- Pointwise, the indicator product for an occurring closed configuration
is bounded by the original zero-one pattern weight. -/
theorem partialConfigurationWeight_univ_le_patternWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness)
    (x : Fin k → G) :
    partialConfigurationWeight A Finset.univ x ≤
      H.toWeighted.patternWeight x := by
  by_cases hx : H.IsOccurrence x
  · rw [H.toWeighted_patternWeight_of_occurrence hx]
    exact partialConfigurationWeight_le_one
      A Finset.univ x
  · rw [H.toWeighted_patternWeight_of_not_occurrence hx,
      partialConfigurationWeight_univ_eq_zero_of_not_occurrence
        H hC A hA hx]

/-- The normalized count of an occurring closed configuration is bounded
by the normalized count of the original pattern. -/
theorem fullConfigurationCount_le_patternCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness) :
    fullConfigurationCount A ≤
      H.toWeighted.patternCount := by
  unfold fullConfigurationCount partialConfigurationCount
    WeightedOrderedPattern.patternCount
  exact mean_mono
    (partialConfigurationWeight_univ_le_patternWeight
      H hC A hA)

/-! ## The cover contradiction -/

/-- If every good configuration has count at least `c`, then a pattern of
count below `c` is covered by the canonical bad-base deletion family. -/
theorem orderedBadBaseDeletionFamily_isCover_of_good_count
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.fine.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ) (c : ℝ)
    (hcount : H.toWeighted.patternCount < c)
    (hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration
          G k (n + 1) P.fine,
        A.IsGood P.fine P.coarse α β →
          c ≤ fullConfigurationCount A) :
    H.IsCover
      (orderedBadBaseDeletionFamily
        P.fine P.coarse α β) := by
  intro x hx
  by_contra hsurvives
  push Not at hsurvives
  let A :
      ClosedOrderedAtomConfiguration
        G k (n + 1) P.fine :=
    ClosedOrderedAtomConfiguration.ofTuple P.fine x
  have hgood :
      A.IsGood P.fine P.coarse α β := by
    exact
      ClosedOrderedAtomConfiguration.isGood_of_avoids_topBadBaseDeletion
        hrk P.fine P.coarse x α β hsurvives
  have hcA : c ≤ fullConfigurationCount A :=
    hgoodCount A hgood
  have htop :
      OrderedFacePartitionRefines P.fine.topLayer
        (orderedPatternTopPartition H) :=
    orderedPatternTopPartition_refines_of_complex_refines_initial
      H hinitial
  have hAH :
      fullConfigurationCount A ≤
        H.toWeighted.patternCount := by
    exact fullConfigurationCount_le_patternCount
      H htop A ((H.mem_occurrenceFinset x).1 hx)
  linarith

/-- Concrete cover theorem obtained from the quantitative configuration
counting lower bound. -/
theorem orderedBadBaseDeletionFamily_isCover
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.fine.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ)
    (ε : OrderedRegularityTolerance (n + 1))
    (hregular :
      IsFullyPreliminaryOrderedRegular P.fine ε)
    {ρ η δ : ℝ}
    (hρ : 0 ≤ ρ) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hα : ∀ m, ρ ≤ α m)
    (hε : ∀ j, ε j ≤ η)
    (hβ0 : ∀ m, 0 ≤ β m)
    (hβδ : ∀ m, β m ≤ δ ^ 2)
    (hcount :
      H.toWeighted.patternCount <
        ρ ^ Fintype.card
            (PositiveOrderedFace k (n + 1)) -
          (Fintype.card
              (PositiveOrderedFace k (n + 1)) : ℝ) *
            (η + δ)) :
    H.IsCover
      (orderedBadBaseDeletionFamily
        P.fine P.coarse α β) := by
  apply orderedBadBaseDeletionFamily_isCover_of_good_count
    hrk H P hinitial α β
    (ρ ^ Fintype.card
        (PositiveOrderedFace k (n + 1)) -
      (Fintype.card
          (PositiveOrderedFace k (n + 1)) : ℝ) *
        (η + δ))
    hcount
  intro A hgood
  exact fullConfigurationCount_lower_bound
    P A α β hgood ε hregular
    hρ hη hδ hα hε hβ0 hβδ

end Wikipedia.SzemeredisTheorem
