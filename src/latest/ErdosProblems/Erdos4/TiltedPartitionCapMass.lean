import ErdosProblems.Erdos4.TiltedPartitionLaw
import ErdosProblems.Erdos4.TiltedNormalizerVariance

/-! Aggregate cap loss is controlled by the unrooted normalizer variances. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [Nonempty I]

noncomputable def partitionRootNormalizer (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (R : ℕ → Ω → Prop) (v : C) (o : Ω) : ℝ :=
  ν.prob (R v.val) * (uniformLabelLaw I).mean
    (fun p => eventWeight ν (blockEvent R (partitionRoot (P p) v).val) o)

open Classical in
noncomputable def partitionLostWeight (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : C) (o : Ω) : ℝ :=
  if 2 < partitionNormalizer ν P hC R o
    then eventWeight ν (blockEvent R (partitionRoot P v).val) o else 0

noncomputable def partitionRootCapLoss (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : C) (o : Ω) : ℝ :=
  ν.prob (R v.val) * (uniformLabelLaw I).mean (fun p => partitionLostWeight ν (P p) hC R v o)

theorem partitionLostWeight_nonneg (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : C) (o : Ω) :
    0 ≤ partitionLostWeight ν P hC R v o := by
  unfold partitionLostWeight
  split_ifs
  · exact eventWeight_nonneg ν _ o
  · rfl

theorem partitionRootCapLoss_nonneg (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : C) (o : Ω) :
    0 ≤ partitionRootCapLoss ν P hC R v o :=
  mul_nonneg (ν.prob_nonneg _) ((uniformLabelLaw I).mean_nonneg
    (fun p => partitionLostWeight_nonneg ν (P p) hC R v o))

theorem partitionRootCapLoss_zero (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (v : C) (o : Ω)
    (hnot : ¬R v.val o) : partitionRootCapLoss ν P hC R v o = 0 := by
  have hzero (p : I) : eventWeight ν (blockEvent R (partitionRoot (P p) v).val) o = 0 := by
    have he : ¬blockEvent R (partitionRoot (P p) v).val o :=
      fun he => hnot (blockEvent_root (P p) R v o he)
    simp [eventWeight, he]
  have hlost (p : I) : partitionLostWeight ν (P p) hC R v o = 0 := by
    simp only [partitionLostWeight, hzero p, ite_self]
  simp only [partitionRootCapLoss, hlost, FiniteLaw.mean_const, mul_zero]

open Classical in
theorem total_rootCapLoss_pointwise (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop)
    {Q B : ℝ} (hQ : 0 ≤ Q) (_hB : 0 ≤ B) (hq : ∀ v : C, ν.prob (R v.val) ≤ Q)
    {K : ℕ} (hsize : ∀ p, ∀ E ∈ (P p).parts, E.card ≤ K)
    (hparts : ∀ p, ((P p).parts.card : ℝ) ≤ B) (o : Ω) :
    (∑ v : C, partitionRootCapLoss ν P hC R v o) ≤
      Q * K * B * (uniformLabelLaw I).mean (fun p =>
        if 2 < partitionNormalizer ν (P p) hC R o then partitionNormalizer ν (P p) hC R o else 0) := by
  have heq : (∑ v : C, partitionRootCapLoss ν P hC R v o) =
      (uniformLabelLaw I).mean (fun p => ∑ v : C,
        ν.prob (R v.val) * partitionLostWeight ν (P p) hC R v o) := by
    rw [FiniteLaw.mean_finset_sum]
    apply Finset.sum_congr rfl
    intro v _
    exact ((uniformLabelLaw I).mean_const_mul _ _).symm
  rw [heq, ← FiniteLaw.mean_const_mul]
  apply (uniformLabelLaw I).mean_mono
  intro p
  by_cases hbad : 2 < partitionNormalizer ν (P p) hC R o
  · simp only [partitionLostWeight, if_pos hbad]
    have hh := weighted_sum_partitionRoots_le (P p)
      (fun E => eventWeight ν (blockEvent R E.val) o) (fun E => eventWeight_nonneg ν _ o)
      (fun v => ν.prob (R v.val)) hQ hq (hsize p)
    rw [partitionNormalizer_sum ν (P p) hC R o] at hh
    apply hh.trans
    have hZ : 0 ≤ partitionNormalizer ν (P p) hC R o :=
      eventNormalizer_nonneg ν (uniformPartLaw (P p) hC) (fun E => blockEvent R E.val) o
    have hm := mul_le_mul_of_nonneg_right (hparts p) hZ
    nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ Q * (K : ℝ) by positivity)]
  · simp only [partitionLostWeight, if_neg hbad, mul_zero, Finset.sum_const_zero, le_refl]

open Classical in
theorem total_rootCapLoss_mean_le (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop)
    {Q B δ : ℝ} (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hq : ∀ v : C, ν.prob (R v.val) ≤ Q)
    {K : ℕ} (hsize : ∀ p, ∀ E ∈ (P p).parts, E.card ≤ K)
    (hparts : ∀ p, ((P p).parts.card : ℝ) ≤ B)
    (hvariance : ∀ p, ν.mean (fun o => (partitionNormalizer ν (P p) hC R o - 1) ^ 2) ≤ δ) :
    (∑ v : C, ν.mean (partitionRootCapLoss ν P hC R v)) ≤ 2 * Q * K * B * δ := by
  rw [← FiniteLaw.mean_finset_sum]
  calc
    _ ≤ ν.mean (fun o => Q * K * B * (uniformLabelLaw I).mean (fun p =>
        if 2 < partitionNormalizer ν (P p) hC R o then partitionNormalizer ν (P p) hC R o else 0)) :=
      ν.mean_mono (total_rootCapLoss_pointwise ν P hC R hQ hB hq hsize hparts)
    _ = Q * K * B * (uniformLabelLaw I).mean (fun p => ν.mean (fun o =>
        if 2 < partitionNormalizer ν (P p) hC R o then partitionNormalizer ν (P p) hC R o else 0)) := by
      rw [FiniteLaw.mean_const_mul, mean_swap]
    _ ≤ Q * K * B * (2 * δ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ (uniformLabelLaw I).mean (fun _p => 2 * δ) := by
          apply (uniformLabelLaw I).mean_mono
          intro p
          exact (cap_tail_mean_le ν _).trans (mul_le_mul_of_nonneg_left (hvariance p) (by norm_num))
        _ = _ := (uniformLabelLaw I).mean_const _
    _ = _ := by ring

end Erdos4.Tilted
