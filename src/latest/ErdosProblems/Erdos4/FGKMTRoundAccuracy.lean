import ErdosProblems.Erdos4.FGKMTMeanHitError

/-!
# Quantitative propagation of joint survival accuracy

This uses the actual independent edge choices and survivor-set law.
The cardinality budget is preserved: conditioning is bounded by its
reciprocal probability, so only `A ≥ 2r` is required at every round.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem relative_product_error {a q b ε L : ℝ} (hb : 0 < b)
    (ha : |a - 1| ≤ ε) (hq : |q - b| ≤ L) :
    |a * q / b - 1| ≤ ε + (1 + ε) * L / b := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans ha
  have hL : 0 ≤ L := (abs_nonneg _).trans hq
  have habs : |a| ≤ 1 + ε := by
    have hh := abs_add_le (a - 1) 1
    have heq : a - 1 + 1 = a := by ring
    rw [heq, abs_one] at hh
    linarith
  have heq : a * q / b - 1 = (a - 1) + a * (q - b) / b := by field_simp; ring
  rw [heq]
  calc
    _ ≤ |a - 1| + |a * (q - b) / b| := abs_add_le _ _
    _ = |a - 1| + |a| * |q - b| / b := by rw [abs_div, abs_mul, abs_of_pos hb]
    _ ≤ ε + (1 + ε) * L / b := add_le_add ha
      (div_le_div_of_nonneg_right (mul_le_mul habs hq (abs_nonneg _) (by linarith)) hb.le)

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

noncomputable def nextModel (μ : I → FiniteLaw (Finset V)) (p : V → ℝ) (v : V) : ℝ :=
  p v * Real.exp (-(vertexDegree μ v / p v))

theorem nextModel_pos (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) : ∀ v, 0 < nextModel μ p v :=
  fun v => mul_pos (hp v) (Real.exp_pos _)

theorem nextModel_le (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    (hp : ∀ v, 0 < p v) : ∀ v, nextModel μ p v ≤ p v := by
  intro v
  apply mul_le_of_le_one_right (hp v).le
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (div_nonneg (vertexDegree_nonneg μ v) (hp v).le)

theorem setProduct_nextModel (μ : I → FiniteLaw (Finset V)) (p : V → ℝ) (T : Finset V) :
    setProduct (nextModel μ p) T = setProduct p T * Real.exp (-testDegree μ p T) := by
  unfold setProduct nextModel testDegree
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]

theorem round_survival_close (ν : FiniteLaw (Finset V))
    {μ : I → FiniteLaw (Finset V)} {p : V → ℝ} {r A : ℕ} {κ δ ε t D : ℝ}
    (h : RoundBounds μ p r κ δ D) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) (hacc : SurvivalAccurate ν p A ε) (hrA : 2 * r ≤ A)
    (T : Finset V) (hT : T.card ≤ A) :
    |survival (roundLaw ν μ p h.model_pos t) T / survival ν T -
      Real.exp (-testDegree μ p T)| ≤ roundLoss r A κ δ ε t D := by
  have hTpos := survival_pos_of_accurate ν p h.model_pos (by linarith : ε < 1) hacc hT
  apply round_survival_error ν μ p h.model_pos t T (ne_of_gt hTpos)
    (testDegree_nonneg μ p h.model_pos T)
    (selected_total_mean_error ν h hε0 hε1 ht0 ht1 hacc hrA T hT)
  calc
    _ ≤ (conditionSurvival ν T).mean (fun _W => roundSquareLoss r A κ δ) := by
      apply (conditionSurvival ν T).mean_mono
      intro W
      apply (selection_meeting_sq_sum μ p h.kappa_pos h.kappa_le_one ht1 h.model_lower
        h.edge_size h.source_scale h.source_marginal h.source_scale_sq W T).trans
      apply div_le_div_of_nonneg_right _ (pow_pos h.kappa_pos _).le
      have hcard : (T.card : ℝ) ^ 2 ≤ (A : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hT) 2
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcard (by norm_num)) (sq_nonneg δ)
    _ = _ := FiniteLaw.mean_const _ _

noncomputable def roundNextError (r A : ℕ) (κ δ ε t D : ℝ) : ℝ :=
  ε + (1 + ε) * Real.exp ((A : ℝ) * D) * roundLoss r A κ δ ε t D

theorem round_accuracy (ν : FiniteLaw (Finset V))
    {μ : I → FiniteLaw (Finset V)} {p : V → ℝ} {r A : ℕ} {κ δ ε t D : ℝ}
    (h : RoundBounds μ p r κ δ D) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) (hacc : SurvivalAccurate ν p A ε) (hrA : 2 * r ≤ A) :
    SurvivalAccurate (roundLaw ν μ p h.model_pos t) (nextModel μ p) A
      (roundNextError r A κ δ ε t D) := by
  intro T hT
  have hP := setProduct_pos p h.model_pos T
  have hS := survival_pos_of_accurate ν p h.model_pos (by linarith : ε < 1) hacc hT
  have hL := roundLoss_nonneg r A h.kappa_pos h.delta_nonneg hε0 ht0.le h.degree_nonneg
  have hround := round_survival_close ν h hε0 hε1 ht0 ht1 hacc hrA T hT
  have hscalar := relative_product_error (Real.exp_pos (-testDegree μ p T)) (hacc T hT) hround
  have heq : (survival ν T / setProduct p T) *
      (survival (roundLaw ν μ p h.model_pos t) T / survival ν T) /
        Real.exp (-testDegree μ p T) =
      survival (roundLaw ν μ p h.model_pos t) T / setProduct (nextModel μ p) T := by
    rw [setProduct_nextModel]
    field_simp
  rw [heq] at hscalar
  apply hscalar.trans
  unfold roundNextError
  rw [Real.exp_neg, div_inv_eq_mul]
  have hexp := Real.exp_le_exp.mpr (testDegree_le h T hT)
  have hmul := mul_le_mul_of_nonneg_left hexp
    (mul_nonneg (by linarith : 0 ≤ 1 + ε) hL)
  nlinarith

end Erdos4.FGKMT
