import ErdosProblems.Erdos4.FGKMTProductApprox
import ErdosProblems.Erdos4.FGKMTConditionalSurvival

/-! Conditional error estimates for the actual finite covering round. -/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem mean_prod_one_sub_error {Ω I : Type*} [Fintype Ω] [Fintype I]
    (ν : FiniteLaw Ω) (a : I → Ω → ℝ) {d η ζ : ℝ}
    (ha0 : ∀ i W, 0 ≤ a i W) (ha1 : ∀ i W, a i W ≤ 1) (hd : 0 ≤ d)
    (hmean : ν.mean (fun W => |(∑ i, a i W) - d|) ≤ η)
    (hsq : ν.mean (fun W => ∑ i, a i W ^ 2) ≤ ζ) :
    |ν.mean (fun W => ∏ i, (1 - a i W)) - Real.exp (-d)| ≤ η + ζ := by
  rw [← ν.mean_const (Real.exp (-d)), ← FiniteLaw.mean_sub]
  calc
    _ ≤ ν.mean (fun W => |(∏ i, (1 - a i W)) - Real.exp (-d)|) := ν.abs_mean_le _
    _ ≤ ν.mean (fun W => (∑ i, a i W ^ 2) + |(∑ i, a i W) - d|) := by
      apply ν.mean_mono
      intro W
      exact (abs_sub_le _ (Real.exp (-(∑ i, a i W))) _).trans
        (add_le_add
          (prod_one_sub_exp_error Finset.univ (fun i => a i W)
            (fun i _hi => ha0 i W) (fun i _hi => ha1 i W))
          (abs_exp_neg_sub_le (Finset.sum_nonneg (fun i _hi => ha0 i W)) hd))
    _ = ν.mean (fun W => ∑ i, a i W ^ 2) +
        ν.mean (fun W => |(∑ i, a i W) - d|) := ν.mean_add _ _
    _ ≤ η + ζ := by linarith

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem round_survival_ratio (ν : FiniteLaw (Finset V))
    (μ : I → FiniteLaw (Finset V)) (p : V → ℝ) (hp : ∀ v, 0 < p v)
    (t : ℝ) (T : Finset V) (hT : survival ν T ≠ 0) :
    survival (roundLaw ν μ p hp t) T / survival ν T =
      (conditionSurvival ν T).mean (fun W =>
        ∏ i, (1 - (selectLaw (μ i) p hp t W).prob (fun e => ¬Disjoint T e))) := by
  rw [round_survival]
  exact (ν.condition_mean (fun W => T ⊆ W) ∅ hT _).symm

/-- Degree concentration and the sum of squared individual hit probabilities
control the survival ratio in a round. All probabilities here refer to
the constructed selection law, with its trimming and normalization. -/
theorem round_survival_error (ν : FiniteLaw (Finset V))
    (μ : I → FiniteLaw (Finset V)) (p : V → ℝ) (hp : ∀ v, 0 < p v)
    (t : ℝ) (T : Finset V) (hT : survival ν T ≠ 0) {d η ζ : ℝ} (hd : 0 ≤ d)
    (hmean : (conditionSurvival ν T).mean (fun W =>
      |(∑ i, (selectLaw (μ i) p hp t W).prob (fun e => ¬Disjoint T e)) - d|) ≤ η)
    (hsq : (conditionSurvival ν T).mean (fun W =>
      ∑ i, (selectLaw (μ i) p hp t W).prob (fun e => ¬Disjoint T e) ^ 2) ≤ ζ) :
    |survival (roundLaw ν μ p hp t) T / survival ν T - Real.exp (-d)| ≤ η + ζ := by
  rw [round_survival_ratio ν μ p hp t T hT]
  exact mean_prod_one_sub_error (conditionSurvival ν T)
    (fun i W => (selectLaw (μ i) p hp t W).prob (fun e => ¬Disjoint T e))
    (fun i W => (selectLaw (μ i) p hp t W).prob_nonneg _)
    (fun i W => (selectLaw (μ i) p hp t W).prob_le_one _) hd hmean hsq

end Erdos4.FGKMT
