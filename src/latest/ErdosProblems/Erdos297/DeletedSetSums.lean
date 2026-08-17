/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Statement

/-!
# Deleting a density-zero set from bounded sums

This file packages the elementary estimate used whenever the
Liu--Sawhney smooth-number reduction deletes `o(N)` denominators.  A sum of
uniformly bounded real terms over such an exceptional set is itself `o(N)`;
after division by `N` it therefore tends to zero.

The final part records uniform bounds for the three kernels which occur in
the entropy optimization: the logistic selection probability, the
log-partition function, and binary entropy.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos297.DeletedSetSums

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The generic deletion estimate -/

/-- The norm of a finite sum of terms bounded by `C` is at most `C` times
the cardinality of the indexing set. -/
lemma norm_sum_le_card_mul {α : Type*} (s : Finset α) (f : α → ℝ) (C : ℝ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ C) :
    ‖∑ i ∈ s, f i‖ ≤ C * (s.card : ℝ) := by
  calc
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, C := by
      exact Finset.sum_le_sum fun i hi ↦ hf i hi
    _ = C * (s.card : ℝ) := by simp [mul_comm]

/-- A uniformly bounded sum over a set of cardinality `o(N)` is `o(N)`. -/
theorem sum_isLittleO_of_card_isLittleO {α : Type*}
    (D : ℕ → Finset α) (u : ℕ → α → ℝ) (C : ℝ)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    (hu : ∀ᶠ N in atTop, ∀ i ∈ D N, ‖u N i‖ ≤ C) :
    (fun N : ℕ ↦ ∑ i ∈ D N, u N i)
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  apply (Asymptotics.IsBigO.of_bound C ?_).trans_isLittleO hD
  filter_upwards [hu] with N hN
  have hcardnorm : ‖((D N).card : ℝ)‖ = ((D N).card : ℝ) :=
    by rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (D N).card)]
  rw [hcardnorm]
  exact norm_sum_le_card_mul (D N) (u N) C hN

/-- Normalized form of `sum_isLittleO_of_card_isLittleO`. -/
theorem tendsto_sum_div_of_card_isLittleO {α : Type*}
    (D : ℕ → Finset α) (u : ℕ → α → ℝ) (C : ℝ)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    (hu : ∀ᶠ N in atTop, ∀ i ∈ D N, ‖u N i‖ ≤ C) :
    Tendsto (fun N : ℕ ↦ (∑ i ∈ D N, u N i) / (N : ℝ))
      atTop (𝓝 0) :=
  (sum_isLittleO_of_card_isLittleO D u C hD hu).tendsto_div_nhds_zero

/-- If `D N ⊆ S N`, deleting `D N` from `S N` changes the sum by `o(N)`.
This is the literal difference of the deleted and original sums. -/
theorem sdiff_sum_sub_sum_isLittleO {α : Type*}
    (S D : ℕ → Finset α) (u : ℕ → α → ℝ) (C : ℝ)
    (hsub : ∀ N, D N ⊆ S N)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    (hu : ∀ᶠ N in atTop, ∀ i ∈ D N, ‖u N i‖ ≤ C) :
    (fun N : ℕ ↦
      (∑ i ∈ S N \ D N, u N i) - ∑ i ∈ S N, u N i)
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  have hsmall := (sum_isLittleO_of_card_isLittleO D u C hD hu).neg_left
  apply hsmall.congr'
  · filter_upwards with N
    have hsum := Finset.sum_sdiff (f := u N) (hsub N)
    linarith
  · rfl

/-- Normalized form of `sdiff_sum_sub_sum_isLittleO`. -/
theorem tendsto_sdiff_sum_sub_sum_div_of_card_isLittleO {α : Type*}
    (S D : ℕ → Finset α) (u : ℕ → α → ℝ) (C : ℝ)
    (hsub : ∀ N, D N ⊆ S N)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    (hu : ∀ᶠ N in atTop, ∀ i ∈ D N, ‖u N i‖ ≤ C) :
    Tendsto (fun N : ℕ ↦
      ((∑ i ∈ S N \ D N, u N i) - ∑ i ∈ S N, u N i) / (N : ℝ))
      atTop (𝓝 0) :=
  (sdiff_sum_sub_sum_isLittleO S D u C hsub hD hu).tendsto_div_nhds_zero

/-! ## Uniform bounds for the Erdős 297 kernels -/

lemma selectionProbability_nonneg (lam x : ℝ) :
    0 ≤ selectionProbability lam x := by
  rw [selectionProbability]
  split_ifs
  · exact le_rfl
  · positivity

lemma selectionProbability_le_one (lam x : ℝ) :
    selectionProbability lam x ≤ 1 := by
  rw [selectionProbability]
  split_ifs
  · exact zero_le_one
  · have hden : 1 ≤ 1 + Real.exp (lam / x) := by
      linarith [Real.exp_pos (lam / x)]
    exact (div_le_one (by positivity)).2 hden

/-- The logistic probability is bounded in norm by one, without any sign
condition on the parameter or the argument. -/
lemma norm_selectionProbability_le_one (lam x : ℝ) :
    ‖selectionProbability lam x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (selectionProbability_nonneg lam x)]
  exact selectionProbability_le_one lam x

/-- For nonnegative `lam` and `x`, the log-partition kernel lies in
`[0, log 2]`. -/
lemma norm_freeEnergyKernel_le_log_two {lam x : ℝ}
    (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    ‖freeEnergyKernel lam x‖ ≤ Real.log 2 := by
  rw [freeEnergyKernel]
  split_ifs with hx0
  · simpa using log_two_pos.le
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hexp_le : Real.exp (-lam / x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) hxpos.le
    have harg_pos : 0 < 1 + Real.exp (-lam / x) := by positivity
    have harg_one : 1 ≤ 1 + Real.exp (-lam / x) := by
      linarith [Real.exp_pos (-lam / x)]
    have harg_two : 1 + Real.exp (-lam / x) ≤ 2 := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg harg_one)]
    exact Real.log_le_log harg_pos harg_two

/-- The form of the log-partition summand used directly in finite products. -/
lemma norm_discreteLogPartition_le_log_two (lam : ℝ) (N n : ℕ)
    (hlam : 0 ≤ lam) :
    ‖Real.log (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ)))‖ ≤
      Real.log 2 := by
  have hexponent : -lam * (N : ℝ) / (n : ℝ) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) (Nat.cast_nonneg N))
      (Nat.cast_nonneg n)
  have hexp_le : Real.exp (-lam * (N : ℝ) / (n : ℝ)) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr hexponent
  have harg_pos : 0 < 1 + Real.exp (-lam * (N : ℝ) / (n : ℝ)) := by
    positivity
  have harg_one : 1 ≤ 1 + Real.exp (-lam * (N : ℝ) / (n : ℝ)) := by
    linarith [Real.exp_pos (-lam * (N : ℝ) / (n : ℝ))]
  have harg_two : 1 + Real.exp (-lam * (N : ℝ) / (n : ℝ)) ≤ 2 := by
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg harg_one)]
  exact Real.log_le_log harg_pos harg_two

/-- Binary entropy is bounded in norm by `log 2` on its probability range. -/
lemma norm_binEntropy_le_log_two {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖Real.binEntropy p‖ ≤ Real.log 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.binEntropy_nonneg hp0 hp1)]
  exact Real.binEntropy_le_log_two

lemma norm_binEntropy_selectionProbability_le_log_two (lam x : ℝ) :
    ‖Real.binEntropy (selectionProbability lam x)‖ ≤ Real.log 2 :=
  norm_binEntropy_le_log_two (selectionProbability_nonneg lam x)
    (selectionProbability_le_one lam x)

/-! ## Ready-to-use deletion consequences -/

theorem selectionProbability_sum_isLittleO
    (D : ℕ → Finset ℕ)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    (lam : ℝ) :
    (fun N : ℕ ↦ ∑ n ∈ D N,
      selectionProbability lam ((n : ℝ) / (N : ℝ)))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  apply sum_isLittleO_of_card_isLittleO D
    (fun N n ↦ selectionProbability lam ((n : ℝ) / (N : ℝ))) 1 hD
  filter_upwards with N n hn
  exact norm_selectionProbability_le_one _ _

theorem tendsto_selectionProbability_sum_div
    (D : ℕ → Finset ℕ)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    (lam : ℝ) :
    Tendsto (fun N : ℕ ↦
      (∑ n ∈ D N, selectionProbability lam ((n : ℝ) / (N : ℝ))) /
        (N : ℝ)) atTop (𝓝 0) :=
  (selectionProbability_sum_isLittleO D hD lam).tendsto_div_nhds_zero

theorem freeEnergyKernel_sum_isLittleO
    (D : ℕ → Finset ℕ)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (fun N : ℕ ↦ ∑ n ∈ D N,
      freeEnergyKernel lam ((n : ℝ) / (N : ℝ)))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  apply sum_isLittleO_of_card_isLittleO D
    (fun N n ↦ freeEnergyKernel lam ((n : ℝ) / (N : ℝ))) (Real.log 2) hD
  filter_upwards with N n hn
  exact norm_freeEnergyKernel_le_log_two hlam
    (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg N))

theorem tendsto_freeEnergyKernel_sum_div
    (D : ℕ → Finset ℕ)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun N : ℕ ↦
      (∑ n ∈ D N, freeEnergyKernel lam ((n : ℝ) / (N : ℝ))) /
        (N : ℝ)) atTop (𝓝 0) :=
  (freeEnergyKernel_sum_isLittleO D hD hlam).tendsto_div_nhds_zero

theorem discreteLogPartition_sum_isLittleO
    (D : ℕ → Finset ℕ)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (fun N : ℕ ↦ ∑ n ∈ D N,
      Real.log (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ))))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  apply sum_isLittleO_of_card_isLittleO D
    (fun N n ↦ Real.log (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ))))
    (Real.log 2) hD
  filter_upwards with N n hn
  exact norm_discreteLogPartition_le_log_two lam N n hlam

theorem tendsto_discreteLogPartition_sum_div
    (D : ℕ → Finset ℕ)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun N : ℕ ↦
      (∑ n ∈ D N,
        Real.log (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ)))) /
        (N : ℝ)) atTop (𝓝 0) :=
  (discreteLogPartition_sum_isLittleO D hD hlam).tendsto_div_nhds_zero

theorem binaryEntropy_sum_isLittleO
    (D : ℕ → Finset ℕ)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    (lam : ℝ) :
    (fun N : ℕ ↦ ∑ n ∈ D N,
      Real.binEntropy (selectionProbability lam ((n : ℝ) / (N : ℝ))))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  apply sum_isLittleO_of_card_isLittleO D
    (fun N n ↦ Real.binEntropy
      (selectionProbability lam ((n : ℝ) / (N : ℝ)))) (Real.log 2) hD
  filter_upwards with N n hn
  exact norm_binEntropy_selectionProbability_le_log_two _ _

theorem tendsto_binaryEntropy_sum_div
    (D : ℕ → Finset ℕ)
    (hD : (fun N : ℕ ↦ ((D N).card : ℝ))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    (lam : ℝ) :
    Tendsto (fun N : ℕ ↦
      (∑ n ∈ D N,
        Real.binEntropy (selectionProbability lam ((n : ℝ) / (N : ℝ)))) /
        (N : ℝ)) atTop (𝓝 0) :=
  (binaryEntropy_sum_isLittleO D hD lam).tendsto_div_nhds_zero

end

end Erdos297.DeletedSetSums

#print axioms Erdos297.DeletedSetSums.tendsto_sdiff_sum_sub_sum_div_of_card_isLittleO
#print axioms Erdos297.DeletedSetSums.binaryEntropy_sum_isLittleO
