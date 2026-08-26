import ErdosProblems.Erdos1038.PlatformReferencePartition
import ErdosProblems.Erdos1038.ResidualWidthRefinement

/-!
# Finite product refinements of the platform reference quantile

Each atomic target block is subdivided into `n + 1` equal subcells.  Sampling
the inverse platform CDF at the left endpoint of each subcell gives the
finite reference vector used in the common-refinement convexity argument.
-/

set_option warningAsError false

open Set

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- Lagrange weights on the `n + 1` product refinement. -/
def platformResidualRefinementAlpha
    (C : ResidualConfiguration iota) (k : ℝ) (n : ℕ) :
    iota × Fin (n + 1) → ℝ :=
  refinedLagrangeWeight (n + 1) (residualLagrangeAlpha C k)

/-- Atomic target locations repeated on the `n + 1` product refinement. -/
def platformResidualRefinementTarget
    (C : ResidualConfiguration iota) (n : ℕ) :
    iota × Fin (n + 1) → ℝ :=
  refinedCoordinates (n + 1) C.location

omit [LinearOrder iota] in
lemma platformResidualRefinementTarget_mem_positiveCoordinates
    (C : ResidualConfiguration iota) (n : ℕ) :
    platformResidualRefinementTarget C n ∈
      positiveCoordinates (iota × Fin (n + 1)) :=
  refinedCoordinates_mem_positiveCoordinates
    (residual_locations_mem_positiveCoordinates C)

/-- Left-endpoint fraction of subcell `j` in an `n + 1` subdivision. -/
def residualRefinementFraction (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  (j : ℕ) / (n + 1 : ℕ)

lemma residualRefinementFraction_mem_Ico (n : ℕ) (j : Fin (n + 1)) :
    residualRefinementFraction n j ∈ Ico (0 : ℝ) 1 := by
  have hden : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hden.le
  · unfold residualRefinementFraction
    rw [div_lt_one hden]
    exact_mod_cast j.isLt

/-- Quantile mass coordinate sampled in the target block indexed by `p.1`. -/
def platformResidualRefinementMass
    (C : ResidualConfiguration iota) (n : ℕ)
    (p : iota × Fin (n + 1)) : ℝ :=
  orderedResidualLeftMass C p.1 +
    C.weight p.1 * residualRefinementFraction n p.2

lemma orderedResidualLeftMass_le_refinementMass
    (C : ResidualConfiguration iota) (n : ℕ)
    (p : iota × Fin (n + 1)) :
    orderedResidualLeftMass C p.1 ≤ platformResidualRefinementMass C n p := by
  unfold platformResidualRefinementMass
  exact le_add_of_nonneg_right
    (mul_nonneg (C.weight_pos p.1).le
      (residualRefinementFraction_mem_Ico n p.2).1)

lemma platformResidualRefinementMass_lt_rightMass
    (C : ResidualConfiguration iota) (n : ℕ)
    (p : iota × Fin (n + 1)) :
    platformResidualRefinementMass C n p < orderedResidualRightMass C p.1 := by
  rw [orderedResidualRightMass_eq_left_add_weight]
  unfold platformResidualRefinementMass
  have hmul : C.weight p.1 * residualRefinementFraction n p.2 <
      C.weight p.1 * 1 :=
    mul_lt_mul_of_pos_left
      (residualRefinementFraction_mem_Ico n p.2).2 (C.weight_pos p.1)
  linarith

lemma platformResidualRefinementMass_mem_Icc
    (C : ResidualConfiguration iota) (n : ℕ)
    (p : iota × Fin (n + 1)) :
    platformResidualRefinementMass C n p ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact (orderedResidualLeftMass_mem_Icc C p.1).1.trans
      (orderedResidualLeftMass_le_refinementMass C n p)
  · exact (platformResidualRefinementMass_lt_rightMass C n p).le.trans
      (orderedResidualRightMass_mem_Icc C p.1).2

/-- The canonical finite sample of the continuous platform reference
quantile on every refined target block. -/
def platformResidualRefinementReference
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    (p : iota × Fin (n + 1)) : ℝ :=
  platformAngularDistance a
    (platformReferenceCut k a hk ha ha2 hthreshold
      ⟨platformResidualRefinementMass C n p,
        platformResidualRefinementMass_mem_Icc C n p⟩)

lemma platformResidualRefinementReference_mem_Icc
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    (p : iota × Fin (n + 1)) :
    platformResidualRefinementReference C k a hk ha ha2 hthreshold n p ∈
      Icc a 2 := by
  apply platformAngularDistance_mem_Icc ha2.le
  exact platformReferenceCut_mem_Icc k a hk ha ha2 hthreshold _

/-- Every canonical platform reference sample is a positive coordinate. -/
theorem platformResidualRefinementReference_mem_positiveCoordinates
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ) :
    platformResidualRefinementReference C k a hk ha ha2 hthreshold n ∈
      positiveCoordinates (iota × Fin (n + 1)) := by
  intro p
  exact ha.trans_le
    (platformResidualRefinementReference_mem_Icc
      C k a hk ha ha2 hthreshold n p).1

/-- The sampled angular coordinate lies inside its canonical target block. -/
lemma platformResidualBlockLeft_le_refinementCut
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    (p : iota × Fin (n + 1)) :
    platformResidualBlockLeft C k a hk ha ha2 hthreshold p.1 ≤
      platformReferenceCut k a hk ha ha2 hthreshold
        ⟨platformResidualRefinementMass C n p,
          platformResidualRefinementMass_mem_Icc C n p⟩ := by
  exact (platformReferenceCut_strictMono k a hk ha ha2 hthreshold).monotone
    (orderedResidualLeftMass_le_refinementMass C n p)

lemma refinementCut_lt_platformResidualBlockRight
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    (p : iota × Fin (n + 1)) :
    platformReferenceCut k a hk ha ha2 hthreshold
        ⟨platformResidualRefinementMass C n p,
          platformResidualRefinementMass_mem_Icc C n p⟩ <
      platformResidualBlockRight C k a hk ha ha2 hthreshold p.1 := by
  exact platformReferenceCut_strictMono k a hk ha ha2 hthreshold
    (platformResidualRefinementMass_lt_rightMass C n p)

end

end Erdos1038
