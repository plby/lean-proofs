/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DynamicDegreeControl
import ErdosProblems.Erdos207.LinkReservoirRootedMoment
import ErdosProblems.Erdos207.LinkSideDensityScalar

/-!
# State-independent scalar bounds for dynamic residual links

Residual link sides are bounded by the degree of their center in the fixed
stage graph.  Conversely, the minimum available-link degree bounds the side
size from below.  These two elementary facts turn several quantified link
inequalities into fixed natural-number inequalities.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

lemma IsResidualBipartition.right_card_le_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : TripleSystemOn V} {center : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G P center K) :
    K.right.card ≤ (residualNeighbors G P center).card := by
  rw [← hK.2.1]
  exact card_le_card subset_union_right

lemma IsResidualBipartition.right_card_le_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : TripleSystemOn V} {center : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G P center K) :
    K.right.card ≤ G.degree center :=
  hK.right_card_le_residual.trans
    (residualNeighbors_card_le_degree P center)

/-- One fixed upper bound on all stage degrees discharges the normalized
second-moment scalar for every dynamic residual link. -/
lemma IsResidualBipartition.mixing_scalar_of_degree_upper
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : TripleSystemOn V} {center : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G P center K)
    (sideMax d D codegree density cutoff : ℕ)
    (hdegree : G.degree center ≤ sideMax)
    (hscalar : sideMax * (D + codegree * sideMax) <
      (cutoff + 1) * (d - density) ^ 2) :
    ∀ s : ℕ, cutoff < s → s ≤ K.right.card →
      K.right.card * (D + codegree * s) <
        s * (d - density) ^ 2 := by
  intro s hcut hs
  have hM : K.right.card ≤ sideMax :=
    hK.right_card_le_degree.trans hdegree
  calc
    K.right.card * (D + codegree * s) ≤
        sideMax * (D + codegree * sideMax) := by
      exact Nat.mul_le_mul hM (Nat.add_le_add_left
        (Nat.mul_le_mul_left codegree (hs.trans hM)) D)
    _ < (cutoff + 1) * (d - density) ^ 2 := hscalar
    _ ≤ s * (d - density) ^ 2 := by
      exact Nat.mul_le_mul_right ((d - density) ^ 2)
        (Nat.succ_le_iff.mpr hcut)

/-- The robust-Hall obstruction failure expression is monotone in the link
side size. -/
lemma IsResidualBipartition.sampling_scalar_of_degree_upper
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : TripleSystemOn V} {center : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G P center K)
    (sideMax Delta groupSize : ℕ)
    (sampleProbability epsilon : ℝ≥0)
    (hdegree : G.degree center ≤ sideMax)
    (hscalar : epsilon +
      (2 * 4 ^ sideMax * (Delta * sideMax + 1) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1) :
    epsilon +
      (2 * 4 ^ K.right.card * (Delta * K.right.card + 1) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1 := by
  have hM : K.right.card ≤ sideMax :=
    hK.right_card_le_degree.trans hdegree
  have hpow : 4 ^ K.right.card ≤ 4 ^ sideMax :=
    pow_le_pow_right₀ (by omega) hM
  have hlinear : Delta * K.right.card + 1 ≤ Delta * sideMax + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left Delta hM) 1
  have hcoefficient :
      2 * 4 ^ K.right.card * (Delta * K.right.card + 1) ≤
        2 * 4 ^ sideMax * (Delta * sideMax + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hpow) hlinear
  apply lt_of_le_of_lt _ hscalar
  gcongr <;> norm_num

/-- For a balanced residual link, the total number of endpoints is at most
twice any uniform upper bound on the stage degree. -/
lemma IsResidualBipartition.card_sum_sides_le_two_mul_degree_upper
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : TripleSystemOn V} {center : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G P center K)
    (sideMax : ℕ) (hdegree : G.degree center ≤ sideMax) :
    Fintype.card (↥K.left ⊕ ↥K.right) ≤ 2 * sideMax := by
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, hK.2.2]
  have hM := hK.right_card_le_degree.trans hdegree
  omega

/-- A uniform stage-degree bound replaces the link-dependent endpoint count
in the rooted-threat moment envelope. -/
theorem IsResidualBipartition.rootedBad_le_of_degree_extension_scalar
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : TripleSystemOn V} {center : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G P center K)
    (F : ForbiddenFamilyOn V) (sampleProbability : ℝ≥0)
    (hprob : sampleProbability ≤ 1)
    (sideMax : ℕ) (hdegree : G.degree center ≤ sideMax)
    (kappa epsilon : ℝ≥0) {familyCutoff momentOrder : ℕ}
    (rootCutoff : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ x : ↥K.left ⊕ ↥K.right,
      HasExtensionBound
        (fun z : RootedThreatWitness V F K.center (linkSideEndpoint K x) =>
          relativeRootedThreatRemainder P z)
        (fun _ => sampleProbability) kappa)
    (hscalar : (2 * sideMax : ℝ≥0) *
      ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
          momentOrder) /
        (rootCutoff + 1 : ℝ≥0) ^ momentOrder) ≤ epsilon) :
    (FiniteLaw.independentBits
      (fun _ : ↥K.left × ↥K.right => sampleProbability)
      (fun _ => hprob)).probability (fun omega =>
        ¬ ((∀ a : ↥K.left,
          (rootedActiveForbiddenConfigurations F
            (P ∪ linkReservoirTriangles K.center K.leftEmbedding
              K.rightEmbedding K.center_ne_left K.center_ne_right
              K.left_ne_right (FiniteLaw.selectedByBits omega))
            K.center a.1).card ≤ rootCutoff) ∧
        (∀ b : ↥K.right,
          (rootedActiveForbiddenConfigurations F
            (P ∪ linkReservoirTriangles K.center K.leftEmbedding
              K.rightEmbedding K.center_ne_left K.center_ne_right
              K.left_ne_right (FiniteLaw.selectedByBits omega))
            K.center b.1).card ≤ rootCutoff))) ≤ epsilon := by
  apply independentBits_probability_linkReservoir_rootedBad_le_of_scalar
    F P K sampleProbability hprob kappa epsilon rootCutoff hfamily hkappa
  apply (mul_le_mul_of_nonneg_right _ zero_le).trans hscalar
  exact_mod_cast hK.card_sum_sides_le_two_mul_degree_upper sideMax hdegree

end

end Erdos207
