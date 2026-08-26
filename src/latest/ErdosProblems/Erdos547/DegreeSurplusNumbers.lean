import ErdosProblems.Erdos547.SetupMargins

/-!
# Numerical degree surplus after regularity losses and tree coating
-/

namespace Erdos547

theorem coating_scale_bound (a s η : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) (hη : 0 ≤ η)
    (hsbound : s ≤ a / 1000) (hηbound : η ≤ a / 10000) (hηone : η ≤ 1 / 10) :
    (1 + 10 * s) * (1 + 10 * η) ≤ 1 + a / 4 := by
  have hh := mul_le_mul_of_nonneg_left (show 10 * η ≤ 1 by linarith only [hηone])
    (show 0 ≤ 10 * s by positivity)
  nlinarith only [hh, hsbound, hηbound, ha]

theorem degree_surplus_after_losses (a n N m l ε d δ target high low : ℝ)
    (ha : 0 < a) (haone : a ≤ 1) (hn : 0 < n) (hm : 0 ≤ m)
    (hε : 0 ≤ ε) (hd : 0 ≤ d) (hδ : 0 ≤ δ)
    (hN : N ≤ 2 * n) (hml : m * l ≤ 2 * n)
    (hparameters : 8 * ε + 4 * d + 2 * δ ≤ a / 8)
    (hl : 32 ≤ a * l) (hlarge : 8 ≤ a * n)
    (htarget : target ≤ (1 + a / 4) * n)
    (hhigh : (1 + a) * (n - 1) - ((4 * ε + d + δ) * N + 2 * m) ≤ m * high)
    (hlow : (1 + a) * (n - 1) / 2 - ((2 * ε + d) * N + m) ≤ m * low) :
    target < m * high ∧ target < 2 * m * low := by
  have hml' := mul_le_mul_of_nonneg_left hml ha.le
  have hl' := mul_le_mul_of_nonneg_right hl hm
  have hmterm : 2 * m ≤ a * n / 8 := by nlinarith only [hml', hl']
  have hmaxN := mul_le_mul_of_nonneg_left hN (show 0 ≤ 4 * ε + d + δ by positivity)
  have hminN := mul_le_mul_of_nonneg_left hN (show 0 ≤ 4 * ε + 2 * d by positivity)
  have hparamn := mul_le_mul_of_nonneg_right hparameters hn.le
  have hdn := mul_nonneg hd hn.le
  have hδn := mul_nonneg hδ hn.le
  have hmaxloss : (4 * ε + d + δ) * N + 2 * m ≤ a * n / 4 := by
    nlinarith only [hmaxN, hparamn, hdn, hmterm]
  have hminloss : 2 * ((2 * ε + d) * N + m) ≤ a * n / 4 := by
    nlinarith only [hminN, hparamn, hδn, hmterm]
  have hadd : 1 + a ≤ a * n / 4 := by nlinarith only [hlarge, haone]
  have hstrict := mul_pos ha hn
  constructor
  · nlinarith only [hhigh, hmaxloss, hadd, htarget, hstrict]
  · nlinarith only [hlow, hminloss, hadd, htarget, hstrict]

end Erdos547

#print axioms Erdos547.coating_scale_bound
#print axioms Erdos547.degree_surplus_after_losses
