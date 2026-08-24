/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 266.
https://www.erdosproblems.com/forum/thread/266

Informal authors:
- Vjekoslav Kovač
- Terence Tao

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos266.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/266.lean
-/
import ErdosProblems.Erdos266.Erdos266Block
import ErdosProblems.Erdos266.Erdos266Diagonal
import ErdosProblems.Erdos266.Erdos266Series

/-!
# Erdős Problem 266

Kovač and Tao disproved the proposed assertion.  The construction below is a
specialization of their simultaneous block-approximation argument to the
positive integral shifts needed here.  The absence of a monotonicity condition
in the formal statement lets us use geometric block scales.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos266

noncomputable section

private lemma two_mul_M_le_N (k : ℕ) : 2 * M k ≤ N k := by
  rw [← M_sq]
  have hM4 : 4 ≤ M k := by
    rw [M]
    exact Nat.le_pow (a := 4) (by omega)
  nlinarith

private def constructionThreshold : ℕ → ℕ :=
  absorptionThreshold Erdos266Block.blockEpsilon Erdos266Block.blockD
    Erdos266Block.blockEpsilon_pos Erdos266Block.blockD_nonneg

private def constructionDim (k : ℕ) : ℕ :=
  activeDim constructionThreshold k

private lemma constructionDim_zero : constructionDim 0 = 0 := by
  exact Nat.eq_zero_of_le_zero (activeDim_le constructionThreshold 0)

private lemma constructionDim_mono : Monotone constructionDim :=
  activeDim_mono constructionThreshold

private lemma constructionDim_step (k : ℕ) :
    constructionDim (k + 1) ≤ constructionDim k + 1 :=
  activeDim_succ_le constructionThreshold k

private lemma constructionDim_le (k : ℕ) : constructionDim k ≤ k + 1 :=
  (activeDim_le constructionThreshold k).trans (Nat.le_succ k)

private lemma constructionDim_unbounded (i : ℕ) :
    ∃ k, i < constructionDim k := by
  let k := schedule constructionThreshold (i + 1)
  refine ⟨k, ?_⟩
  have hle : i + 1 ≤ activeDim constructionThreshold k :=
    scheduled_le_activeDim constructionThreshold (by rfl)
  simpa [constructionDim] using hle

private lemma schedule_zero_le_of_constructionDim_pos {k : ℕ}
    (hkpos : 0 < constructionDim k) : schedule constructionThreshold 0 ≤ k := by
  by_contra hk
  have hzero : activeDim constructionThreshold k = 0 := by
    rw [activeDim, Nat.findGreatest_eq_iff]
    refine ⟨Nat.zero_le _, ?_, ?_⟩
    · simp
    · intro n _hn _hnk hnstart
      apply hk
      exact ((schedule_strictMono constructionThreshold).monotone (Nat.zero_le n)).trans hnstart
  exact (Nat.ne_of_gt hkpos) (by simpa [constructionDim] using hzero)

/-- A block chosen at stage `k` is a total integer tuple.  Only its first
`constructionDim k` entries are used, but the total representation makes the
recursive choice type independent of `k`. -/
private def admissibleBlock (k : ℕ) (b : ℕ → ℤ) : Prop :=
  ∀ j, |(b j : ℝ)| ≤ M k

private def stageActualBlock (k : ℕ) (b : ℕ → ℤ) (i : ℕ) : ℝ :=
  ∑ j : Fin (constructionDim k), reciprocalCoordinate (i + 1)
    (((((j.1 + 1) * N k : ℕ) : ℝ)) + b j.1)

private lemma stageActualBlock_eq_actualCoordinateBlock
    (z : ℕ → ℕ → ℤ) (hz : OffsetsBounded M z) (i k : ℕ) :
    stageActualBlock k (z k) i = actualCoordinateBlock constructionDim z i k := by
  unfold stageActualBlock actualCoordinateBlock
  apply Finset.sum_congr rfl
  intro j _hj
  rw [blockNat_cast N_pos two_mul_M_le_N hz]
  push_cast
  rfl

private theorem refineBlock (k : ℕ)
    (error : Fin (constructionDim k) → ℝ)
    (herror : ∀ i, |error i| ≤
      coordinateRadius Erdos266Block.blockEpsilon constructionDim i k) :
    ∃ b : ℕ → ℤ, admissibleBlock k b ∧ ∀ i,
      |error i + referenceCoordinateBlock constructionDim i k -
          stageActualBlock k b i| ≤
        coordinateRadius Erdos266Block.blockEpsilon constructionDim i (k + 1) := by
  let d := constructionDim k
  let q : Fin d → ℝ := fun i => -error i
  have hq : ∀ i, |q i| ≤
      Erdos266Block.blockEpsilon d * (M k : ℝ) / (N k : ℝ) ^ (i.1 + 2) := by
    intro i
    simpa [q, d, coordinateRadius] using herror i
  obtain ⟨z, hz, hzerr⟩ :=
    Erdos266Block.discrete_block_approximation_uniform d (N k) (M k)
      (N_pos k) (one_le_M k)
      (four_mul_dim_mul_M_le_N (by simpa [d] using constructionDim_le k))
      q hq
  let b : ℕ → ℤ := fun j => if h : j < d then z ⟨j, h⟩ else 0
  have hb : admissibleBlock k b := by
    intro j
    by_cases h : j < d
    · simpa [b, h] using hz ⟨j, h⟩
    · simp [b, h]
  refine ⟨b, hb, ?_⟩
  intro i
  have href : referenceCoordinateBlock constructionDim i.1 k =
      Erdos266Block.referenceBlock d (N k) i := by
    unfold referenceCoordinateBlock Erdos266Block.referenceBlock
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Erdos266Block.coord_eq_reciprocalCoordinate]
  have hactual : stageActualBlock k b i.1 =
      Erdos266Block.perturbedBlock d (N k) z i := by
    unfold stageActualBlock Erdos266Block.perturbedBlock
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Erdos266Block.coord_eq_reciprocalCoordinate]
    have hjlt : j.1 < d := j.isLt
    simp [b, hjlt]
  have hdpos : 0 < constructionDim k :=
    (Nat.zero_le i.1).trans_lt i.isLt
  have hk0 := schedule_zero_le_of_constructionDim_pos hdpos
  have habsPair := activeDim_absorbs Erdos266Block.blockEpsilon Erdos266Block.blockD
    Erdos266Block.blockEpsilon_pos Erdos266Block.blockD_nonneg
    (k := k) (by simpa [constructionThreshold] using hk0)
  have habs :
      Erdos266Block.blockD d *
          (1 / (N k : ℝ) ^ (i.1 + 2) +
            (M k : ℝ) ^ 2 / (N k : ℝ) ^ (i.1 + 3)) ≤
        Erdos266Block.blockEpsilon (constructionDim (k + 1)) *
          (M (k + 1) : ℝ) / (N (k + 1) : ℝ) ^ (i.1 + 2) := by
    rcases activeDim_succ_eq_or_eq_succ constructionThreshold k with hsame | hsucc
    · rw [show constructionDim (k + 1) = d by simpa [constructionDim, d] using hsame]
      exact habsPair.1 i.1 i.isLt
    · rw [show constructionDim (k + 1) = d + 1 by simpa [constructionDim, d] using hsucc]
      exact habsPair.2 i.1 i.isLt
  have herr := hzerr i
  rw [← href, ← hactual] at herr
  have hfinal := herr.trans habs
  dsimp [q] at hfinal
  simpa [coordinateRadius, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfinal

private def constructionScheme : Erdos266Diagonal.Scheme (ℕ → ℤ) where
  dim := constructionDim
  dim_zero := constructionDim_zero
  dim_mono := constructionDim_mono
  dim_step := constructionDim_step
  dim_unbounded := constructionDim_unbounded
  refBlock := referenceCoordinateBlock constructionDim
  actualBlock := stageActualBlock
  admissible := admissibleBlock
  radius := coordinateRadius Erdos266Block.blockEpsilon constructionDim
  tail := referenceCoordinateTail constructionDim
  radius_pos := coordinateRadius_pos _ _ Erdos266Block.blockEpsilon_pos
  tail_succ := referenceCoordinateTail_succ constructionDim constructionDim_le
  refine := refineBlock

private def chosenOffsets (k j : ℕ) : ℤ :=
  constructionScheme.choice k j

private lemma chosenOffsets_bounded : OffsetsBounded M chosenOffsets := by
  intro k j
  have h := constructionScheme.choice_admissible k
  exact h j

private lemma stageActualBlock_chosen_eq (i k : ℕ) :
    stageActualBlock k (constructionScheme.choice k) i =
      actualCoordinateBlock constructionDim chosenOffsets i k := by
  exact stageActualBlock_eq_actualCoordinateBlock chosenOffsets chosenOffsets_bounded i k

private theorem summable_chosen_actual_blocks (i : ℕ) :
    Summable (fun k => constructionScheme.actualBlock k
      (constructionScheme.choice k) i) := by
  have h := summable_actualCoordinateBlock constructionDim chosenOffsets
    chosenOffsets_bounded constructionDim_le i
  convert h using 1
  funext k
  exact stageActualBlock_chosen_eq i k

private theorem construction_target_eq_tsum (i : ℕ) :
    (constructionScheme.target i : ℝ) =
      ∑' k, stageActualBlock k (constructionScheme.choice k) i := by
  apply constructionScheme.target_eq_tsum
  · exact summable_chosen_actual_blocks
  · exact tendsto_referenceCoordinateTail constructionDim
  · exact tendsto_coordinateRadius Erdos266Block.blockEpsilon constructionDim
      (fun d => (Erdos266Block.blockEpsilon_pos d).le)
      Erdos266Block.blockEpsilon_le_one

private theorem rational_block_coordinate (i : ℕ) :
    ∃ q : ℚ,
      (∑' p : Erdos266Diagonal.Scheme.BlockIndex constructionDim,
        reciprocalCoordinate (i + 1)
          (blockNat N chosenOffsets p.1 p.2.1 : ℝ)) = (q : ℝ) := by
  refine ⟨constructionScheme.target i, ?_⟩
  calc
    (∑' p : Erdos266Diagonal.Scheme.BlockIndex constructionDim,
        reciprocalCoordinate (i + 1)
          (blockNat N chosenOffsets p.1 p.2.1 : ℝ)) =
        ∑' k, actualCoordinateBlock constructionDim chosenOffsets i k :=
      tsum_actualCoordinateBlock constructionDim chosenOffsets chosenOffsets_bounded
        constructionDim_le i
    _ = ∑' k, stageActualBlock k (constructionScheme.choice k) i := by
      apply tsum_congr
      intro k
      exact (stageActualBlock_chosen_eq i k).symm
    _ = (constructionScheme.target i : ℝ) := (construction_target_eq_tsum i).symm

private def blockEmbedding (n : ℕ) :
    Erdos266Diagonal.Scheme.BlockIndex constructionDim :=
  ⟨schedule constructionThreshold (n + 1),
    ⟨0, by
      have hle : n + 1 ≤ constructionDim (schedule constructionThreshold (n + 1)) := by
        simpa [constructionDim] using
          (scheduled_le_activeDim constructionThreshold
            (show schedule constructionThreshold (n + 1) ≤
              schedule constructionThreshold (n + 1) from le_rfl))
      omega⟩⟩

private lemma blockEmbedding_injective : Function.Injective blockEmbedding := by
  intro n m hnm
  have hs : schedule constructionThreshold (n + 1) =
      schedule constructionThreshold (m + 1) := congrArg Sigma.fst hnm
  have hsucc : n + 1 = m + 1 :=
    (schedule_strictMono constructionThreshold).injective hs
  omega

private noncomputable def blockEnumeration :
    ℕ ≃ Erdos266Diagonal.Scheme.BlockIndex constructionDim := by
  letI : Infinite (Erdos266Diagonal.Scheme.BlockIndex constructionDim) :=
    Infinite.of_injective blockEmbedding blockEmbedding_injective
  exact nonempty_equiv_of_countable.some

/-- The positive-integer sequence witnessing the negative solution of
Problem 266. -/
private def counterexampleSequence (n : ℕ) : ℕ :=
  let p := blockEnumeration n
  blockNat N chosenOffsets p.1 p.2.1

private lemma counterexampleSequence_pos (n : ℕ) :
    1 ≤ counterexampleSequence n := by
  dsimp [counterexampleSequence]
  exact blockNat_pos N_pos two_mul_M_le_N chosenOffsets_bounded _ _

private theorem summable_counterexample_reciprocals :
    Summable (fun n => (1 : ℝ) / counterexampleSequence n) := by
  have hsigma := summable_reciprocal_blocks constructionDim N M chosenOffsets
    N_pos two_mul_M_le_N chosenOffsets_bounded constructionDim_le summable_succ_div_N
  have hreindex :=
    (Erdos266Diagonal.Scheme.summable_reindex_iff constructionDim
      (fun p : Erdos266Diagonal.Scheme.BlockIndex constructionDim =>
        (1 : ℝ) / blockNat N chosenOffsets p.1 p.2.1) blockEnumeration).2 hsigma
  simpa [counterexampleSequence] using hreindex

private theorem rational_counterexample_coordinates :
    ∀ i : ℕ, 1 ≤ i →
      ∃ q : ℚ,
        (∑' n, reciprocalCoordinate i (counterexampleSequence n : ℝ)) = (q : ℝ) := by
  intro i hi
  obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
  obtain ⟨q, hq⟩ := rational_block_coordinate r
  refine ⟨q, ?_⟩
  calc
    (∑' n, reciprocalCoordinate (r + 1) (counterexampleSequence n : ℝ)) =
        ∑' p : Erdos266Diagonal.Scheme.BlockIndex constructionDim,
          reciprocalCoordinate (r + 1)
            (blockNat N chosenOffsets p.1 p.2.1 : ℝ) := by
      simpa [counterexampleSequence] using
        (Erdos266Diagonal.Scheme.tsum_reindex_eq constructionDim
          (fun p : Erdos266Diagonal.Scheme.BlockIndex constructionDim =>
            reciprocalCoordinate (r + 1)
              (blockNat N chosenOffsets p.1 p.2.1 : ℝ)) blockEnumeration)
    _ = (q : ℝ) := hq

/-- Erdős Problem 266 has a negative answer: there is a positive reciprocal-
summable sequence for which every positive integral shifted sum is rational. -/
theorem not_erdos_266 :
    ¬ ∀ (a : ℕ → ℕ), ((∀ n : ℕ, a n ≥ 1) ∧ Summable ((1 : ℝ) / a ·)) →
      ∃ t ≥ (1 : ℕ), Irrational (∑' n, (1 : ℝ) / ((a n) + t)) := by
  intro hclaim
  obtain ⟨t, ht, hirr⟩ := hclaim counterexampleSequence
    ⟨counterexampleSequence_pos, summable_counterexample_reciprocals⟩
  obtain ⟨q, hq⟩ := rational_tsum_shift_of_rational_coordinate_tsums
    counterexampleSequence counterexampleSequence_pos
    summable_counterexample_reciprocals rational_counterexample_coordinates t ht
  have hirr' : Irrational
      (∑' n, (1 : ℝ) / ((counterexampleSequence n : ℝ) + t)) := by
    simpa only [Nat.cast_add] using hirr
  rw [hq] at hirr'
  exact q.not_irrational hirr'

end

end Erdos266

#print axioms Erdos266.not_erdos_266

alias _root_.Erdos266.erdos_266 := _root_.Erdos266.not_erdos_266
