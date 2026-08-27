import ErdosProblems.Erdos4.TiltedPartitionDegree
import ErdosProblems.Erdos4.TiltedConditionedWeights
import ErdosProblems.Erdos4.TiltedRetainedExponential
import ErdosProblems.Erdos4.TiltedIndependentCover

/-! The two variance estimates imply a finite covering bound for the actual capped block choices. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [Nonempty I]

open Classical in
noncomputable def partitionMissCost (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (o : Ω) : ℝ :=
  ∑ v : C, if R v.val o then Real.exp (-partitionCoverDegree ν P hC R v.val o) else 0

open Classical in
theorem partitionMissCost_mean_le (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (o₀ : Ω)
    {Q B δroot δblock : ℝ} (hQ : 0 < Q) (hB : 0 < B) (hδroot : 0 ≤ δroot)
    (hR : ∀ v : C, ν.prob (R v.val) ≠ 0) (hq : ∀ v : C, ν.prob (R v.val) ≤ Q)
    {K : ℕ} (hsize : ∀ p, ∀ E ∈ (P p).parts, E.card ≤ K)
    (hparts : ∀ p, ((P p).parts.card : ℝ) ≤ B)
    (hroot : ∀ v : C, (ν.condition (R v.val) o₀).mean
      (fun o => (partitionRootNormalizer ν P R v o - 1) ^ 2) ≤ δroot)
    (hblock : ∀ p, ν.mean (fun o => (partitionNormalizer ν (P p) hC R o - 1) ^ 2) ≤ δblock) :
    ν.mean (partitionMissCost ν P hC R) ≤
      (C.card : ℝ) * Q * (4 * δroot + Real.exp (-(Fintype.card I : ℝ) / (8 * B * Q))) +
        8 * Q * K * B * δblock := by
  let d := (Fintype.card I : ℝ) / (8 * B * Q)
  have hper (v : C) : ν.mean (fun o => if R v.val o then
      Real.exp (-partitionCoverDegree ν P hC R v.val o) else 0) ≤
      ν.prob (R v.val) * (4 * δroot + Real.exp (-d)) +
        4 * ν.mean (partitionRootCapLoss ν P hC R v) := by
    let νv := ν.condition (R v.val) o₀
    have ht := retained_exponential_mean_le νv (partitionRootNormalizer ν P R v)
      (partitionRootCapLoss ν P hC R v) (partitionCoverDegree ν P hC R v.val) d
      (partitionRootCapLoss_nonneg ν P hC R v) (partitionCoverDegree_nonneg ν P hC R v.val)
      (fun o _ hw hl => partitionCoverDegree_lower ν P hC R v o hQ hB (hq v) hparts hw hl)
    have ht' : νv.mean (fun o => Real.exp (-partitionCoverDegree ν P hC R v.val o)) ≤
        4 * δroot + 4 * νv.mean (partitionRootCapLoss ν P hC R v) + Real.exp (-d) :=
      ht.trans (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (hroot v) (by norm_num)) le_rfl) le_rfl)
    have hloss := condition_mean_mul_eq ν (R v.val) o₀ (hR v)
      (partitionRootCapLoss ν P hC R v) (fun o ho => partitionRootCapLoss_zero ν P hC R v o ho)
    rw [mean_on_event_eq_condition ν (R v.val) o₀ (hR v)]
    calc
      _ ≤ ν.prob (R v.val) * (4 * δroot +
          4 * νv.mean (partitionRootCapLoss ν P hC R v) + Real.exp (-d)) :=
        mul_le_mul_of_nonneg_left ht' (ν.prob_nonneg _)
      _ = ν.prob (R v.val) * (4 * δroot + Real.exp (-d)) +
          4 * (ν.prob (R v.val) * νv.mean (partitionRootCapLoss ν P hC R v)) := by ring
      _ = _ := by rw [hloss]
  have hsumq : (∑ v : C, ν.prob (R v.val)) ≤ (C.card : ℝ) * Q := by
    calc
      _ ≤ ∑ _v : C, Q := Finset.sum_le_sum (fun v _ => hq v)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hloss := total_rootCapLoss_mean_le ν P hC R hQ.le hB.le hq hsize hparts hblock
  change ν.mean (fun o => ∑ v : C, if R v.val o then
    Real.exp (-partitionCoverDegree ν P hC R v.val o) else 0) ≤ _
  rw [FiniteLaw.mean_finset_sum]
  calc
    _ ≤ ∑ v : C, (ν.prob (R v.val) * (4 * δroot + Real.exp (-d)) +
        4 * ν.mean (partitionRootCapLoss ν P hC R v)) := Finset.sum_le_sum (fun v _ => hper v)
    _ = (∑ v : C, ν.prob (R v.val)) * (4 * δroot + Real.exp (-d)) +
        4 * ∑ v : C, ν.mean (partitionRootCapLoss ν P hC R v) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ ((C.card : ℝ) * Q) * (4 * δroot + Real.exp (-d)) +
        4 * (2 * Q * K * B * δblock) := add_le_add
      (mul_le_mul_of_nonneg_right hsumq (by positivity))
      (mul_le_mul_of_nonneg_left hloss (by norm_num))
    _ = _ := by
      have heq : -((Fintype.card I : ℝ) / (8 * B * Q)) = -(Fintype.card I : ℝ) / (8 * B * Q) := by ring
      dsimp [d]
      rw [heq]
      ring

omit [Nonempty I] in
open Classical in
theorem exists_partition_cover [DecidableEq I] (ν : FiniteLaw Ω) {C : Finset ℕ}
    (P : I → Finpartition C) (hC : C.Nonempty) (R : ℕ → Ω → Prop) (o : Ω) :
    ∃ choice : ∀ p, Option (P p).parts,
      (∀ p, 0 < (partitionChoiceLaw ν (P p) hC R o).weight (choice p)) ∧
      ((((C.filter (fun v => R v o)).filter
        (fun v => ∀ p, v ∉ selectedPart (P p) (choice p))).card : ℝ)) ≤ partitionMissCost ν P hC R o := by
  obtain ⟨choice, hpos, hcount⟩ := exists_independent_cover
    (fun p => partitionChoiceLaw ν (P p) hC R o) (fun p => selectedPart (P p))
    (C.filter (fun v => R v o))
  have heq : (∑ v ∈ C.filter (fun v => R v o), Real.exp (-partitionCoverDegree ν P hC R v o)) =
      partitionMissCost ν P hC R o := by
    rw [Finset.sum_filter]
    exact (Finset.sum_coe_sort C (fun v =>
      if R v o then Real.exp (-partitionCoverDegree ν P hC R v o) else 0)).symm
  exact ⟨choice, hpos, hcount.trans_eq heq⟩

end Erdos4.Tilted
