/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RobustHallScalar

/-!
# A scalar union bound for sampled robust Hall witnesses

For two balanced sides of size `M`, each orientation has at most `4^M`
prospective Hall obstructions.  Every obstruction uses at most
`Delta*M+1` witness groups.  Thus the full sigma index set has cardinality at
most `2 * 4^M * (Delta*M+1)`, which replaces the dependent finite type in the
sampling inequality by one explicit scalar.
-/

namespace Erdos207

open Finset
open scoped NNReal

lemma card_hallObstruction_le
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    Fintype.card (HallObstruction A B) ≤
      2 ^ (Fintype.card A + Fintype.card B) := by
  calc
    Fintype.card (HallObstruction A B) ≤
        Fintype.card (Finset A × Finset B) := Fintype.card_subtype_le _
    _ = 2 ^ (Fintype.card A + Fintype.card B) := by
      simp [pow_add]

lemma card_smallHallObstruction_le
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    Fintype.card (SmallHallObstruction A B) ≤
      2 ^ (Fintype.card A + Fintype.card B) := by
  exact (Fintype.card_subtype_le _).trans
    (card_hallObstruction_le A B)

/-- A balanced pair of `M`-element sides has at most `2*4^M` oriented small
Hall obstructions. -/
lemma card_orientedSmallHallObstruction_le
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (hcard : Fintype.card A = Fintype.card B) :
    Fintype.card (OrientedSmallHallObstruction A B) ≤
      2 * 4 ^ Fintype.card B := by
  rw [Fintype.card_sum]
  have hleft := card_smallHallObstruction_le A B
  have hright := card_smallHallObstruction_le B A
  have hp : 2 ^ (Fintype.card B + Fintype.card B) =
      4 ^ Fintype.card B := by
    rw [pow_add, ← mul_pow]
    norm_num
  have hleft' : Fintype.card (SmallHallObstruction A B) ≤
      4 ^ Fintype.card B := by
    calc
      Fintype.card (SmallHallObstruction A B) ≤
          2 ^ (Fintype.card A + Fintype.card B) := hleft
      _ = 2 ^ (Fintype.card B + Fintype.card B) := by rw [hcard]
      _ = 4 ^ Fintype.card B := hp
  have hright' : Fintype.card (SmallHallObstruction B A) ≤
      4 ^ Fintype.card B := by
    calc
      Fintype.card (SmallHallObstruction B A) ≤
          2 ^ (Fintype.card B + Fintype.card A) := hright
      _ = 2 ^ (Fintype.card B + Fintype.card B) := by rw [hcard]
      _ = 4 ^ Fintype.card B := hp
  omega

lemma orientedSmallHallSize_le
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (hcard : Fintype.card A = Fintype.card B)
    (o : OrientedSmallHallObstruction A B) :
    orientedSmallHallSize o ≤ Fintype.card B := by
  rcases o with o | o
  · simpa [orientedSmallHallSize, hcard] using o.1.1.1.card_le_univ
  · simpa [orientedSmallHallSize] using o.1.1.1.card_le_univ

/-- Explicit cardinality bound for every sampled witness-group index. -/
theorem card_orientedSmallHallGroupSigma_le
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (Delta : ℕ) (hcard : Fintype.card A = Fintype.card B) :
    Fintype.card
        (Σ o : OrientedSmallHallObstruction A B,
          OrientedSmallHallGroupIndex Delta o) ≤
      2 * 4 ^ Fintype.card B * (Delta * Fintype.card B + 1) := by
  rw [Fintype.card_sigma]
  calc
    ∑ o : OrientedSmallHallObstruction A B,
        Fintype.card (OrientedSmallHallGroupIndex Delta o) ≤
        ∑ _o : OrientedSmallHallObstruction A B,
          (Delta * Fintype.card B + 1) := by
      apply Finset.sum_le_sum
      intro o _ho
      simp only [OrientedSmallHallGroupIndex, Fintype.card_fin]
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left Delta (orientedSmallHallSize_le hcard o)) 1
    _ = Fintype.card (OrientedSmallHallObstruction A B) *
        (Delta * Fintype.card B + 1) := by simp
    _ ≤ (2 * 4 ^ Fintype.card B) *
        (Delta * Fintype.card B + 1) :=
      Nat.mul_le_mul_right _ (card_orientedSmallHallObstruction_le A B hcard)
    _ = 2 * 4 ^ Fintype.card B *
        (Delta * Fintype.card B + 1) := rfl

/-- The explicit obstruction-count scalar implies the exact sampling union
bound consumed by the robust link-cover theorem. -/
theorem orientedSmallHall_sampling_lt_one_of_scalar
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (Delta groupSize : ℕ) (sampleProbability : ℝ≥0)
    (hcard : Fintype.card A = Fintype.card B)
    (hsmall :
      (2 * 4 ^ Fintype.card B *
          (Delta * Fintype.card B + 1) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1) :
    (Fintype.card
      (Σ o : OrientedSmallHallObstruction A B,
        OrientedSmallHallGroupIndex Delta o) : ℝ≥0) *
      (1 - sampleProbability) ^ groupSize < 1 := by
  apply lt_of_le_of_lt _ hsmall
  exact mul_le_mul_of_nonneg_right (by
    exact_mod_cast card_orientedSmallHallGroupSigma_le Delta hcard) zero_le

/-- Fully scalar Hall-mixing and sampling hypotheses, together with the
state-dependent deletion cutoffs, produce the safe link extension. -/
theorem HasLinkDegreeCodegreeBounds.hasLinkCoverExtension_of_scalars
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {available P : TripleSystemOn V}
    {K : BipartiteLink V} {d D codegree : ℕ}
    (htyp : HasLinkDegreeCodegreeBounds available K d D codegree)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hbalanced : K.left.card = K.right.card)
    (hpositive : 0 < K.right.card)
    (hdensityLe : density ≤ d)
    (hmixingScalar : ∀ s : ℕ, cutoff < s → s ≤ K.right.card →
      K.right.card * (D + codegree * s) <
        s * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hdensityScalar : K.right.card * candidate ≤
      density * (K.right.card / 2))
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (hsampleScalar :
      (2 * 4 ^ K.right.card *
          (Delta * K.right.card + 1) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hleaveLeft : ∀ a : ↥K.left,
      (leaveGraph P).Adj K.center a.1)
    (hleaveRight : ∀ b : ↥K.right,
      (leaveGraph P).Adj K.center b.1)
    (hdegreeLeft : ∀ a : ↥K.left,
      (coveredGraph P).degree K.center + (coveredGraph P).degree a.1 ≤
        degreeCutoff)
    (hdegreeRight : ∀ b : ↥K.right,
      (coveredGraph P).degree K.center + (coveredGraph P).degree b.1 ≤
        degreeCutoff)
    (hrootLeft :
      ∀ (R : Finset (↥K.left × ↥K.right)) (a : ↥K.left),
        (rootedActiveForbiddenConfigurations F
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) K.center a.1).card ≤ rootCutoff)
    (hrootRight :
      ∀ (R : Finset (↥K.left × ↥K.right)) (b : ↥K.right),
        (rootedActiveForbiddenConfigurations F
          (P ∪ linkReservoirTriangles K.center K.leftEmbedding
            K.rightEmbedding K.center_ne_left K.center_ne_right
            K.left_ne_right R) K.center b.1).card ≤ rootCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    HasLinkCoverExtension F available P K := by
  have hmoments := balancedLink_secondMomentScalars_of_uniform K d D
    codegree density cutoff hbalanced hpositive hdensityLe hmixingScalar
  have hcard : Fintype.card ↥K.left = Fintype.card ↥K.right := by
    simpa using hbalanced
  have hsample := orientedSmallHall_sampling_lt_one_of_scalar
    Delta groupSize sampleProbability hcard (by
      simpa using hsampleScalar)
  exact htyp.hasLinkCoverExtension Delta groupSize density candidate cutoff
    degreeCutoff rootCutoff familyCutoff hbalanced hpositive hmoments.1
      hmoments.2 hdegreeScalar hdensityScalar hcandidateScalar
      sampleProbability hprob hsample hPpacking hPavoid hfamily hleaveLeft
      hleaveRight hdegreeLeft hdegreeRight hrootLeft hrootRight
      hdeletionScalar

end Erdos207
