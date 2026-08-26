import ErdosProblems.Erdos69.AffineResidueModel
import ErdosProblems.Erdos69.EvenMomentTransfer
import ErdosProblems.Erdos69.ExponentialMoments

/-! # Quantitative characteristic-function comparison on an affine progression -/

open scoped BigOperators

namespace Erdos69.Elementary.FiniteLaw

variable {ρ ι : Type*} [Fintype ρ] [Fintype ι] [DecidableEq ρ] [DecidableEq ι]

theorem categorical_product_mean_exp_le (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hc : ∀ j, Fintype.card ι ≤ p j) (c : ι → ℝ) (hzero : ∑ i, c i = 0)
    (t ε : ℝ) (hmass : ∑ i, |c i| ≤ ε) (hsmall : |t| * ε ≤ 1) :
    (independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).mean
      (fun x ↦ Real.exp (t * ∑ j, optionalValue c (x j))) ≤
        Real.exp (t ^ 2 * ε ^ 2 * ∑ j, (1 : ℝ) / p j) := by
  have h := independentProduct_mean_exp_le
    (fun j ↦ categorical ι (p j) (hp j) (hc j)) (fun _ ↦ optionalValue c) t
    (fun j ↦ t ^ 2 * ε ^ 2 / p j)
    (fun j ↦ categorical_mean_exp_le (p j) (hp j) (hc j) c hzero t ε hmass hsmall)
  convert h using 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem affine_fourier_transfer (p : ρ → ℕ) (hp : ∀ j, 0 < p j)
    (hcop : Pairwise (fun i j ↦ (p i).Coprime (p j)))
    (Q b : ℕ) (hQ : ∀ j, Q.Coprime (p j)) (s : ι → ℕ)
    (hs : ∀ j i k, s i ≡ s k [MOD p j] → i = k)
    (hc : ∀ j, Fintype.card ι ≤ p j) (c : ι → ℝ) (hzero : ∑ i, c i = 0)
    (ε B : ℝ) (hmass : ∑ i, |c i| ≤ ε) (hsmall : 4 * Real.pi * ε ≤ 1)
    (hB : 1 ≤ B) (hsize : (Fintype.card ρ : ℝ) * ε ≤ B)
    (T : ℕ) (hT : 0 < T) (m : ℕ) (hm : 0 < m) (hme : Even m) :
    ‖(uniform T hT).complexMean (fun t ↦ fourierPhase
        (∑ j, ∑ i, c i * (if p j ∣ b + Q * t.val + s i then (1 : ℝ) else 0))) -
      (independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))).complexMean
        (fun x ↦ fourierPhase (∑ j, optionalValue c (x j)))‖ ≤
      (B ^ m / T) * (1 + m) * Real.exp (2 * Real.pi) +
        4 * m * Real.exp ((4 * Real.pi) ^ 2 * ε ^ 2 * ∑ j, (1 : ℝ) / p j) *
          (1 / 2 : ℝ) ^ m := by
  let μ := uniform T hT
  let ν := independentProduct (fun j ↦ categorical ι (p j) (hp j) (hc j))
  let X : Fin T → ℝ := fun t ↦
    ∑ j, ∑ i, c i * (if p j ∣ b + Q * t.val + s i then (1 : ℝ) else 0)
  let Y : (ρ → Option ι) → ℝ := fun x ↦ ∑ j, optionalValue c (x j)
  have hBn : 0 ≤ B := by linarith
  have hmoment (k : ℕ) (hk : k ≤ m) :
      |μ.mean (fun x ↦ X x ^ k) - ν.mean (fun y ↦ Y y ^ k)| ≤ B ^ m / T := by
    have h := affine_moment_error p hp hcop Q b hQ s hs hc c T hT k
    apply h.trans
    calc
      _ ≤ (1 : ℝ) / T * B ^ k := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans hsize
      _ ≤ (1 : ℝ) / T * B ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hk) (by positivity)
      _ = _ := by ring
  have hplus := categorical_product_mean_exp_le p hp hc c hzero (4 * Real.pi) ε hmass
    (by simpa only [abs_of_pos (by positivity : 0 < 4 * Real.pi)] using hsmall)
  have hminus := categorical_product_mean_exp_le p hp hc c hzero (-(4 * Real.pi)) ε hmass
    (by simpa only [abs_neg, abs_of_pos (by positivity : 0 < 4 * Real.pi)] using hsmall)
  simp only [neg_sq] at hminus
  exact fourier_even_transfer μ ν X Y m hm hme (B ^ m / T) _ (by positivity)
    hmoment hplus hminus

end Erdos69.Elementary.FiniteLaw
