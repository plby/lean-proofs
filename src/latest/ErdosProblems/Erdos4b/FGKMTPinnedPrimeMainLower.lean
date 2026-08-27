/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedMainExponential
import ErdosProblems.Erdos4b.FGKMTPrimeIntervalLower
import ErdosProblems.Erdos4b.FGKMTDimensionLossAbsorption

/-!
# A quantitative lower bound for the complete prime main mass

The ordinary presieve witness is transported to the prime presieve, and
the prime count is the literal count on (floor(x/2),x]. All dimension
thresholds precede the varying arithmetic parameters.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def commonPinnedPrimeMainTerm (m W M R Q A B : ℕ)
    (h : Fin (m + 1) → ℕ) (j : Fin (m + 1)) : ℝ :=
  primePreSieveDensity W Q (fun i => (h i : ℤ)) j *
    (commonPinnedPrimeSet A B).card * commonPinnedMainTerm m M R

theorem commonPinnedPrimeMainTerm_ge_exp_cube {m B0 W R Q x : ℕ} {H : ℝ}
    (hH : 0 ≤ H) (hm : 1 ≤ m) (hlog : 10000 ≤ Real.log (m + 1 : ℕ))
    (hB0 : B0 = 1 ∨ B0.Prime) (hW : 0 < W) (hBW : B0.Coprime W) (hQ : Q.Coprime W)
    (hR : 1 ≤ Real.log (R : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ B0 * W)
    (hsize : (W : ℝ) ≤ Real.exp (H * (m + 1 : ℕ) ^ 2))
    (hcount : (x : ℝ) * Real.exp (-9 * dimensionLogLossScale x) ≤
      (commonPinnedPrimeSet (x / 2) x).card)
    (h : Fin (m + 1) → ℕ) (j : Fin (m + 1)) {n : ℤ}
    (hn : preSieveCondition W (fun i => (h i : ℤ)) n) :
    (x : ℝ) * Real.exp (-(4 * H + 20) * (m + 1 : ℕ) ^ 3 - 9 * dimensionLogLossScale x) ≤
      commonPinnedPrimeMainTerm m W (B0 * W) R Q (x / 2) x h j := by
  let k : ℝ := (m + 1 : ℕ)
  let S := dimensionLogLossScale x
  have hk1 : 1 ≤ k := by dsimp [k]; exact_mod_cast (by omega : 1 ≤ m + 1)
  have hk23 : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk1 (by omega)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hdensity : Real.exp (-H * k ^ 2) ≤ primePreSieveDensity W Q (fun i => (h i : ℤ)) j := by
    have he : Real.exp (-H * k ^ 2) ≤ 1 / (W : ℝ) := by
      simpa only [neg_mul] using exp_neg_le_inv_of_le_exp hWpos hsize
    exact he.trans (primePreSieveDensity_ge_inv_of_witness hW hQ _ j hn)
  have hdensity0 := (Real.exp_pos _).le.trans hdensity
  have hmain := commonPinnedMainTerm_ge_exp_cube hH hm hlog hB0 hW hBW hR hsmall hsize
  have hmain0 := (Real.exp_pos _).le.trans hmain
  calc
    _ ≤ (x : ℝ) * Real.exp (-H * k ^ 2 - 9 * S - (3 * H + 20) * k ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg x)
      apply Real.exp_monotone
      change -(4 * H + 20) * k ^ 3 - 9 * S ≤ _
      have hcost := mul_le_mul_of_nonneg_left hk23 hH
      nlinarith
    _ = Real.exp (-H * k ^ 2) * ((x : ℝ) * Real.exp (-9 * S)) *
        Real.exp (-(3 * H + 20) * k ^ 3) := by
      simp only [sub_eq_add_neg, Real.exp_add, neg_mul]
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul hdensity hcount (by positivity) hdensity0) hmain
      (Real.exp_pos _).le (mul_nonneg hdensity0 (Nat.cast_nonneg _))

theorem eventually_commonPinnedPrimeMainTerm_exp_lower {H e : ℝ}
    (hH : 0 < H) (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop, ∀ m B0 W R Q : ℕ,
      1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      (m + 1 : ℕ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
      (B0 = 1 ∨ B0.Prime) → 0 < W → B0.Coprime W → Q.Coprime W →
      1 ≤ Real.log (R : ℝ) →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ B0 * W) →
      (W : ℝ) ≤ Real.exp (H * (m + 1 : ℕ) ^ 2) →
      ∀ h : Fin (m + 1) → ℕ, ∀ j : Fin (m + 1), ∀ n : ℤ,
        preSieveCondition W (fun i => (h i : ℤ)) n →
        (x : ℝ) * Real.exp (-e * Real.sqrt (Real.log (x : ℝ))) ≤
          commonPinnedPrimeMainTerm m W (B0 * W) R Q (x / 2) x h j := by
  have hC : 0 < 4 * H + 29 := by positivity
  filter_upwards [eventually_commonPinnedPrimeSet_half_exp_lower,
    eventually_uniform_cubeDimension_loss hC he] with x hcount hsmall
  intro m B0 W R Q hm hlog hdim hB0 hW hBW hQ hR hprimes hsize h j n hn
  let k : ℝ := (m + 1 : ℕ)
  let S := dimensionLogLossScale x
  have hk1 : 1 ≤ k := by dsimp [k]; exact_mod_cast (by omega : 1 ≤ m + 1)
  have hk3 : 1 ≤ k ^ 3 := one_le_pow₀ hk1
  have hS1 : 1 ≤ S := one_le_dimensionLogLossScale x
  have hS0 : 0 ≤ S := zero_le_one.trans hS1
  have hcost1 : (4 * H + 20) * k ^ 3 ≤ (4 * H + 20) * k ^ 3 * S := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hS1 (by positivity : 0 ≤ (4 * H + 20) * k ^ 3)
  have hcost2 : 9 * S ≤ 9 * k ^ 3 * S := by
    have h := mul_le_mul_of_nonneg_right hk3 (by positivity : 0 ≤ 9 * S)
    nlinarith
  have hcost : (4 * H + 20) * k ^ 3 + 9 * S ≤ e * Real.sqrt (Real.log (x : ℝ)) := by
    apply le_trans _ (hsmall (m + 1) hdim)
    change _ ≤ (4 * H + 29) * k ^ 3 * S
    nlinarith
  calc
    _ ≤ (x : ℝ) * Real.exp (-(4 * H + 20) * k ^ 3 - 9 * S) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg x)
      exact Real.exp_monotone (by linarith)
    _ ≤ _ := commonPinnedPrimeMainTerm_ge_exp_cube hH.le hm hlog hB0 hW hBW hQ hR
      hprimes hsize hcount h j hn

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedPrimeMainTerm_ge_exp_cube
#print axioms Erdos4b.FGKMT.eventually_commonPinnedPrimeMainTerm_exp_lower
