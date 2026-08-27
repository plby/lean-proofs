import ErdosProblems.Erdos4.TiltedPartitionCapMass

/-! Retained root incidence gives a quantitative lower bound for the covering degree. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [Nonempty I]

open Classical in
noncomputable def partitionRetainedWeight (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : C) (o : Ω) : ℝ :=
  if partitionNormalizer ν P hC R o ≤ 2
    then eventWeight ν (blockEvent R (partitionRoot P v).val) o else 0

theorem partitionRetainedWeight_nonneg (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : C) (o : Ω) :
    0 ≤ partitionRetainedWeight ν P hC R v o := by
  unfold partitionRetainedWeight
  split_ifs
  · exact eventWeight_nonneg ν _ o
  · rfl

noncomputable def partitionCoverDegree (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : ℕ) (o : Ω) : ℝ :=
  ∑ p, (partitionChoiceLaw ν (P p) hC R o).prob (fun e => v ∈ selectedPart (P p) e)

omit [Nonempty I] in
theorem partitionCoverDegree_nonneg (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : ℕ) (o : Ω) :
    0 ≤ partitionCoverDegree ν P hC R v o := Finset.sum_nonneg (fun _p _ => FiniteLaw.prob_nonneg _ _)

theorem partitionRootNormalizer_sub_loss (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : C) (o : Ω) :
    partitionRootNormalizer ν P R v o - partitionRootCapLoss ν P hC R v o =
      ν.prob (R v.val) * (∑ p, partitionRetainedWeight ν (P p) hC R v o) / Fintype.card I := by
  classical
  unfold partitionRootNormalizer partitionRootCapLoss
  rw [← mul_sub, ← FiniteLaw.mean_sub]
  have heq : (uniformLabelLaw I).mean (fun p =>
      eventWeight ν (blockEvent R (partitionRoot (P p) v).val) o - partitionLostWeight ν (P p) hC R v o) =
      (uniformLabelLaw I).mean (fun p => partitionRetainedWeight ν (P p) hC R v o) := by
    apply (uniformLabelLaw I).mean_congr
    intro p
    by_cases h : partitionNormalizer ν (P p) hC R o ≤ 2
    · simp [partitionLostWeight, partitionRetainedWeight, h, not_lt.mpr h]
    · simp [partitionLostWeight, partitionRetainedWeight, h, lt_of_not_ge h]
  rw [heq, uniformLabelLaw_mean]
  ring

omit [Nonempty I] in
theorem retained_sum_div_le_degree (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : C) (o : Ω)
    {B : ℝ} (_hB : 0 < B) (hparts : ∀ p, ((P p).parts.card : ℝ) ≤ B) :
    (∑ p, partitionRetainedWeight ν (P p) hC R v o) / (2 * B) ≤
      partitionCoverDegree ν P hC R v.val o := by
  classical
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p _
  rw [partitionChoiceLaw_vertex]
  change partitionRetainedWeight ν (P p) hC R v o / (2 * B) ≤
    partitionRetainedWeight ν (P p) hC R v o / (2 * ((P p).parts.card : ℝ))
  exact div_le_div_of_nonneg_left (partitionRetainedWeight_nonneg ν (P p) hC R v o)
    (mul_pos (by norm_num) (Nat.cast_pos.mpr (part_count_pos (P p) hC))) (by linarith [hparts p])

theorem partitionCoverDegree_lower (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : C) (o : Ω)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B) (hq : ν.prob (R v.val) ≤ Q)
    (hparts : ∀ p, ((P p).parts.card : ℝ) ≤ B)
    (hroot : 1 / 2 ≤ partitionRootNormalizer ν P R v o)
    (hloss : partitionRootCapLoss ν P hC R v o ≤ 1 / 4) :
    (Fintype.card I : ℝ) / (8 * B * Q) ≤ partitionCoverDegree ν P hC R v.val o := by
  let S := ∑ p, partitionRetainedWeight ν (P p) hC R v o
  have hS : 0 ≤ S := Finset.sum_nonneg (fun p _ => partitionRetainedWeight_nonneg ν (P p) hC R v o)
  have hmpos : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hmargin : 1 / 4 ≤ partitionRootNormalizer ν P R v o - partitionRootCapLoss ν P hC R v o := by linarith
  rw [partitionRootNormalizer_sub_loss] at hmargin
  have hsum := (le_div_iff₀ hmpos).mp hmargin
  change (1 / 4) * (Fintype.card I : ℝ) ≤ ν.prob (R v.val) * S at hsum
  have hQsum := mul_le_mul_of_nonneg_right hq hS
  have hdegree := (div_le_iff₀ (show 0 < 2 * B by positivity)).mp
    (retained_sum_div_le_degree ν P hC R v o hB hparts)
  change S ≤ partitionCoverDegree ν P hC R v.val o * (2 * B) at hdegree
  apply (div_le_iff₀ (show 0 < 8 * B * Q by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hdegree hQ.le]

end Erdos4.Tilted
