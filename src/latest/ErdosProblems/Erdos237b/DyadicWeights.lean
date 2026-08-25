import ErdosProblems.Erdos237b.ProductWeights
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dyadic weights for a qualitative large-dimension candidate

Use the interval `[2^j, 2^(j+1)] / (8 L k)` with height `2^(-j)`,
for `j < L`. The normalized squared weights have expected upper endpoint
at most `1 / (4 k)`. Thus half their product mass lies below total upper
endpoint `1/2`. If `k ≥ 2^L`, any further interval still fits inside the
unit simplex.

These are finite identities and bounds for the proposed step-function
candidate. The identification with Maynard's integrals and the general sieve
asymptotics are separate obligations; this file makes no prime-count claim.
-/

namespace Erdos237b

open Finset
open scoped BigOperators

noncomputable def dyadicNormalizer (L : ℕ) : ℝ :=
  ∑ j : Fin L, (1 / 2 : ℝ) ^ (j : ℕ)

theorem one_le_dyadicNormalizer {L : ℕ} (hL : 0 < L) :
    1 ≤ dyadicNormalizer L := by
  have h := single_le_sum (f := fun j : Fin L => (1 / 2 : ℝ) ^ (j : ℕ))
    (fun j _ => by positivity) (mem_univ (⟨0, hL⟩ : Fin L))
  simpa [dyadicNormalizer] using h

theorem dyadicNormalizer_lt_two (L : ℕ) : dyadicNormalizer L < 2 := by
  have h := geom_sum_eq (x := (1 / 2 : ℝ)) (by norm_num) L
  have hpos : 0 < (1 / 2 : ℝ) ^ L := by positivity
  rw [← Fin.sum_univ_eq_sum_range] at h
  change (∑ j : Fin L, (1 / 2 : ℝ) ^ (j : ℕ)) < 2
  rw [h]
  norm_num
  linarith

noncomputable def dyadicProbability (L : ℕ) (j : Fin L) : ℝ :=
  (1 / 2 : ℝ) ^ (j : ℕ) / dyadicNormalizer L

noncomputable def dyadicUpper (L k : ℕ) (j : Fin L) : ℝ :=
  (2 : ℝ) ^ ((j : ℕ) + 1) / (8 * L * k)

theorem dyadicProbability_nonneg {L : ℕ} (hL : 0 < L) (j : Fin L) :
    0 ≤ dyadicProbability L j := by
  apply div_nonneg (by positivity)
  exact (zero_le_one.trans (one_le_dyadicNormalizer hL))

theorem sum_dyadicProbability {L : ℕ} (hL : 0 < L) :
    ∑ j : Fin L, dyadicProbability L j = 1 := by
  simp only [dyadicProbability, ← sum_div]
  exact div_self (ne_of_gt (zero_lt_one.trans_le (one_le_dyadicNormalizer hL)))

theorem dyadicUpper_nonneg (L k : ℕ) (j : Fin L) :
    0 ≤ dyadicUpper L k j := by
  unfold dyadicUpper
  positivity

theorem dyadicUpper_le_half {L k : ℕ} (hL : 0 < L) (hk : 2 ^ L ≤ k)
    (j : Fin L) : dyadicUpper L k j ≤ 1 / 2 := by
  have hkpos : 0 < k := (pow_pos (by decide : 0 < (2 : ℕ)) L).trans_le hk
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hkr : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hpow : (2 : ℝ) ^ ((j : ℕ) + 1) ≤ (k : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ L := pow_le_pow_right₀ (by norm_num) j.isLt
      _ ≤ k := by exact_mod_cast hk
  unfold dyadicUpper
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * L * k)).2
  nlinarith

theorem dyadicUpper_mul_probability {L k : ℕ} (j : Fin L) :
    dyadicUpper L k j * dyadicProbability L j =
      2 / (8 * L * k * dyadicNormalizer L) := by
  unfold dyadicUpper dyadicProbability
  rw [div_mul_div_comm, pow_succ]
  have hpow : (2 : ℝ) ^ (j : ℕ) * (1 / 2 : ℝ) ^ (j : ℕ) = 1 := by
    rw [← mul_pow]
    norm_num
  congr 1
  nlinarith [hpow]

theorem sum_dyadic_firstMoment {L k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    ∑ j : Fin L, dyadicUpper L k j * dyadicProbability L j =
      1 / (4 * k * dyadicNormalizer L) := by
  simp_rw [dyadicUpper_mul_probability]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hZ : dyadicNormalizer L ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (one_le_dyadicNormalizer hL))
  field_simp
  ring

theorem dyadic_mean_le_quarter {L k n : ℕ}
    (hL : 0 < L) (hk : 0 < k) (hn : n ≤ k) :
    (n : ℝ) * (∑ j : Fin L, dyadicUpper L k j * dyadicProbability L j) ≤ 1 / 4 := by
  rw [sum_dyadic_firstMoment hL hk]
  have hZ := one_le_dyadicNormalizer hL
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hnr : (n : ℝ) ≤ k := by exact_mod_cast hn
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity : 0 < 4 * (k : ℝ) * dyadicNormalizer L)).2
  nlinarith

/-- The coarse first-moment bound retains half the box mass in all
dimensions `n ≤ k`, uniformly in the number of dyadic intervals. -/
theorem half_le_dyadic_good_mass {L k n : ℕ}
    (hL : 0 < L) (hk : 0 < k) (hn : n ≤ k) :
    1 / 2 ≤ ∑ x : Fin n → Fin L,
      if (∑ i, dyadicUpper L k (x i)) ≤ 1 / 2
      then ∏ i, dyadicProbability L (x i) else 0 := by
  apply half_le_product_mass_below_cutoff (dyadicProbability L) (dyadicUpper L k)
    (sum_dyadicProbability hL) (dyadicProbability_nonneg hL)
    (dyadicUpper_nonneg L k) (1 / 2) (by norm_num)
  simpa only [Fintype.card_fin, show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num]
    using dyadic_mean_le_quarter hL hk hn

noncomputable def dyadicHeight (L : ℕ) (j : Fin L) : ℝ :=
  (1 / 2 : ℝ) ^ (j : ℕ)

noncomputable def dyadicLength (L k : ℕ) (j : Fin L) : ℝ :=
  (2 : ℝ) ^ (j : ℕ) / (8 * L * k)

theorem dyadicLength_nonneg (L k : ℕ) (j : Fin L) : 0 ≤ dyadicLength L k j := by
  unfold dyadicLength
  positivity

theorem dyadicUpper_eq_two_mul_length (L k : ℕ) (j : Fin L) :
    dyadicUpper L k j = 2 * dyadicLength L k j := by
  unfold dyadicUpper dyadicLength
  rw [pow_succ]
  ring

theorem dyadicUpper_sub_length (L k : ℕ) (j : Fin L) :
    dyadicUpper L k j - dyadicLength L k j = dyadicLength L k j := by
  rw [dyadicUpper_eq_two_mul_length]
  ring

theorem dyadicHeight_mul_length (L k : ℕ) (j : Fin L) :
    dyadicHeight L j * dyadicLength L k j = 1 / (8 * L * k) := by
  unfold dyadicHeight dyadicLength
  rw [← mul_div_assoc, ← mul_pow]
  norm_num

theorem dyadicHeight_sq_mul_length (L k : ℕ) (j : Fin L) :
    dyadicHeight L j ^ 2 * dyadicLength L k j =
      (1 / 2 : ℝ) ^ (j : ℕ) / (8 * L * k) := by
  rw [pow_two, mul_assoc, dyadicHeight_mul_length]
  simp only [dyadicHeight, mul_one_div]

theorem sum_dyadicHeight_mul_length {L k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    ∑ j : Fin L, dyadicHeight L j * dyadicLength L k j = 1 / (8 * k) := by
  simp_rw [dyadicHeight_mul_length]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

theorem sum_dyadicHeight_sq_mul_length (L k : ℕ) :
    ∑ j : Fin L, dyadicHeight L j ^ 2 * dyadicLength L k j =
      dyadicNormalizer L / (8 * L * k) := by
  simp_rw [dyadicHeight_sq_mul_length]
  rw [← sum_div]
  rfl

/-- The one-dimensional weighted sums have an arbitrarily large ratio
after multiplication by half the number of coordinates. This is the scalar
bound used in the proposed box-truncation argument. -/
theorem dyadic_scalar_ratio_lower_bound {L k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    (L : ℝ) / 32 < (k : ℝ) / 2 *
      (∑ j : Fin L, dyadicHeight L j * dyadicLength L k j) ^ 2 /
        (∑ j : Fin L, dyadicHeight L j ^ 2 * dyadicLength L k j) := by
  rw [sum_dyadicHeight_mul_length hL hk, sum_dyadicHeight_sq_mul_length]
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hZpos : 0 < dyadicNormalizer L :=
    zero_lt_one.trans_le (one_le_dyadicNormalizer hL)
  have hZlt := dyadicNormalizer_lt_two L
  have heq : (k : ℝ) / 2 * (1 / (8 * k)) ^ 2 /
      (dyadicNormalizer L / (8 * L * k)) = (L : ℝ) / (16 * dyadicNormalizer L) := by
    field_simp
    ring
  rw [heq]
  exact div_lt_div_of_pos_left hLr (by positivity) (by linarith)

end Erdos237b
