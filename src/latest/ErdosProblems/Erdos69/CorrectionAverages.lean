import ErdosProblems.Erdos69.CompositeTails
import ErdosProblems.Erdos69.JointResidues

/-! # Mean correction for composite dilations -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem summable_mean (μ : FiniteLaw Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ x, Summable (fun k ↦ f k x)) :
    Summable (fun k ↦ μ.mean (f k)) := by
  exact summable_sum (fun x _ ↦ (hf x).mul_left (μ.mass x))

theorem mean_tsum (μ : FiniteLaw Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ x, Summable (fun k ↦ f k x)) :
    μ.mean (fun x ↦ ∑' k, f k x) = ∑' k, μ.mean (f k) := by
  unfold mean
  calc
    _ = ∑ x, ∑' k, μ.mass x * f k x :=
      Finset.sum_congr rfl (fun x _ ↦ ((hf x).tsum_mul_left (μ.mass x)).symm)
    _ = _ := (Summable.tsum_finsetSum (fun x _ ↦ (hf x).mul_left (μ.mass x))).symm

theorem mean_div_const (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.mean (fun x ↦ f x / c) = μ.mean f / c := by
  simp only [div_eq_mul_inv, mean_mul_const]

theorem uniform_divisibility_mean_le (T p Q b : ℕ) (hT : 0 < T)
    (hp : 0 < p) (hQ : Q.Coprime p) :
    (uniform T hT).mean (fun t ↦ if p ∣ b + Q * t.val then (1 : ℝ) else 0) ≤
      (1 : ℝ) / p + 1 / T := by
  rw [uniform_mean_indicator T hT (fun t ↦ p ∣ b + Q * t)]
  have h := affineResidueFrequency_error T p Q b hT hp hQ
  have hupper := (abs_le.mp h).2
  change (T.count (fun t ↦ p ∣ b + Q * t) : ℝ) / T ≤ _
  unfold affineResidueCount at hupper
  linarith

theorem uniform_divisibilityTail_le (T p Q b : ℕ) (hT : 0 < T)
    (hp : 0 < p) (hQ : Q.Coprime p) :
    (uniform T hT).mean (fun t ↦ divisibilityTail p (b + Q * t.val)) ≤
      (1 : ℝ) / p + 1 / T := by
  let f : ℕ → Fin T → ℝ := fun k t ↦
    (if p ∣ b + Q * t.val + (k + 1) then (1 : ℝ) else 0) / 2 ^ (k + 1)
  have hf (t : Fin T) : Summable (fun k ↦ f k t) := summable_divisibilityTail _ _
  have heq : (uniform T hT).mean (fun t ↦ divisibilityTail p (b + Q * t.val)) =
      ∑' k, (uniform T hT).mean (f k) := mean_tsum _ f hf
  rw [heq, ← tsum_constant_binary_weights ((1 : ℝ) / p + 1 / T)]
  apply Summable.tsum_le_tsum _ (summable_mean _ f hf) (summable_constant_binary_weights _)
  intro k
  dsimp [f]
  rw [mean_div_const]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := uniform_divisibility_mean_le T p Q (b + (k + 1)) hT hp hQ
  simpa only [Nat.add_right_comm] using h

theorem uniform_compositeCorrection_le (T a Q b : ℕ) (hT : 0 < T)
    (hQ : ∀ p ∈ a.primeFactors, Q.Coprime p) :
    (uniform T hT).mean (fun t ↦ compositeCorrection a (b + Q * t.val)) ≤
      (∑ p ∈ a.primeFactors, (1 : ℝ) / p) + (omegaCount a : ℝ) / T := by
  simp only [compositeCorrection, mean_sum]
  calc
    _ ≤ ∑ p ∈ a.primeFactors, ((1 : ℝ) / p + 1 / T) := by
      apply Finset.sum_le_sum
      intro p hp
      exact uniform_divisibilityTail_le T p Q b hT
        (Nat.mem_primeFactors.mp hp).1.pos (hQ p hp)
    _ = _ := by simp [Finset.sum_add_distrib, omegaCount, div_eq_mul_inv]

end Erdos69.Elementary.FiniteLaw
