import ErdosProblems.Erdos140.Bookkeeping

/-!
# Stable numerical choices for the concrete supply

The final analytic supply still chooses its rank budget from the local
Chang dimension. Once that positive budget is fixed, the two reciprocal
Bohr-child denominators below are uniform in every state whose rank is at
most the accumulated 1024 times d-plus-one budget.
-/

open Finset
open scoped NNReal

namespace Erdos140.ConcreteNumerics

noncomputable section

/-- Uniform upper bound for the rank of a state after at most
1024 times d-plus-one steps. -/
def rankCap (d rankCost : ℕ) : ℕ :=
  1024 * (d + 1) * rankCost

/-- Reciprocal denominator for the first Bourgain child. The factor
819200 = 400 * 2048 pays simultaneously for rank regularity and the
epsilonDense = 1/512 narrowing inequality. -/
def mOne (d rankCost : ℕ) : ℕ :=
  819200 * rankCap d rankCost * 2 ^ d

/-- Reciprocal denominator for the second, Holder-small child. Its
coefficient is deliberately coarse and leaves room for the endpoint-density
loss used by the boundary-width estimate. -/
def mTwo (d rankCost : ℕ) : ℕ :=
  76800 * rankCap d rankCost * 2 ^ (d + 1)

lemma rankCap_pos {d rankCost : ℕ} (hrankCost : 0 < rankCost) :
    0 < rankCap d rankCost := by
  unfold rankCap
  positivity

lemma one_le_rankCap {d rankCost : ℕ} (hrankCost : 0 < rankCost) :
    1 ≤ rankCap d rankCost :=
  Nat.one_le_iff_ne_zero.mpr (rankCap_pos hrankCost).ne'

lemma max_rank_le_rankCap {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost) :
    max r 1 ≤ rankCap d rankCost := by
  exact max_le hrank (one_le_rankCap hrankCost)

lemma mOne_pos {d rankCost : ℕ} (hrankCost : 0 < rankCost) :
    0 < mOne d rankCost := by
  unfold mOne
  exact Nat.mul_pos
    (Nat.mul_pos (by norm_num) (rankCap_pos hrankCost))
    (pow_pos (by norm_num) _)

lemma mTwo_pos {d rankCost : ℕ} (hrankCost : 0 < rankCost) :
    0 < mTwo d rankCost := by
  unfold mTwo
  exact Nat.mul_pos
    (Nat.mul_pos (by norm_num) (rankCap_pos hrankCost))
    (pow_pos (by norm_num) _)

/-- The first denominator is certainly at least 100 times rank, as needed
for rank-regular Bohr estimates. -/
lemma hundred_mul_max_rank_le_mOne {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost) :
    100 * max r 1 ≤ mOne d rankCost := by
  have hmax := max_rank_le_rankCap hrankCost hrank
  unfold mOne
  calc
    100 * max r 1 ≤ 100 * rankCap d rankCost :=
      Nat.mul_le_mul_left 100 hmax
    _ ≤ 819200 * rankCap d rankCost * 2 ^ d := by
      have hcoeff : 100 ≤ 819200 := by omega
      calc
        100 * rankCap d rankCost ≤ 819200 * rankCap d rankCost :=
          Nat.mul_le_mul_right _ hcoeff
        _ ≤ 819200 * rankCap d rankCost * 2 ^ d :=
          Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)

/-- Concrete first-scale rank condition in the exact NNReal shape used by
ReciprocalStepBounds.scale_rank. -/
lemma inv_mOne_le_rank_scale {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost) :
    ((mOne d rankCost : NNReal)⁻¹) ≤
      1 / (100 * (max r 1 : ℕ) : NNReal) := by
  rw [one_div]
  have hleft : (0 : NNReal) < mOne d rankCost := by
    exact_mod_cast mOne_pos hrankCost
  have hright : (0 : NNReal) < 100 * (max r 1 : ℕ) := by
    positivity
  apply (inv_le_inv₀ hleft hright).2
  exact_mod_cast hundred_mul_max_rank_le_mOne hrankCost hrank

/-- The same first denominator also discharges the exact density-narrowing
scale inequality at epsilonDense = 1/512 on a dyadic density state. -/
lemma mOne_scale_density {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost)
    {density : ℝ}
    (hdensity : 1 / (2 : ℝ) ^ d ≤ density) :
    400 * ((max r 1 : ℕ) : ℝ) *
        ((((mOne d rankCost : ℕ) : NNReal)⁻¹ : NNReal) : ℝ) ≤
      (1 / 512 : ℝ) * density / 4 := by
  change 400 * ((max r 1 : ℕ) : ℝ) *
      (mOne d rankCost : ℝ)⁻¹ ≤ (1 / 512 : ℝ) * density / 4
  have hmax := max_rank_le_rankCap hrankCost hrank
  have hboundNat :
      819200 * max r 1 * 2 ^ d ≤ mOne d rankCost := by
    unfold mOne
    exact Nat.mul_le_mul_right (2 ^ d)
      (Nat.mul_le_mul_left 819200 hmax)
  have hbound :
      (819200 : ℝ) * (max r 1 : ℕ) * (2 : ℝ) ^ d ≤
        (mOne d rankCost : ℝ) := by
    exact_mod_cast hboundNat
  have hmPos : (0 : ℝ) < mOne d rankCost := by
    exact_mod_cast mOne_pos hrankCost
  have hbasePos :
      (0 : ℝ) < (819200 : ℝ) * (max r 1 : ℕ) * (2 : ℝ) ^ d := by
    positivity
  have hinv :
      (mOne d rankCost : ℝ)⁻¹ ≤
        ((819200 : ℝ) * (max r 1 : ℕ) * (2 : ℝ) ^ d)⁻¹ :=
    (inv_le_inv₀ hmPos hbasePos).2 hbound
  calc
    400 * ((max r 1 : ℕ) : ℝ) * (mOne d rankCost : ℝ)⁻¹ ≤
        400 * ((max r 1 : ℕ) : ℝ) *
          ((819200 : ℝ) * (max r 1 : ℕ) * (2 : ℝ) ^ d)⁻¹ := by
      gcongr
    _ = (1 / 2048 : ℝ) * (1 / (2 : ℝ) ^ d) := by
      have hrpos : (0 : ℝ) < (max r 1 : ℕ) := by positivity
      have hpowPos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
      field_simp
      ring
    _ ≤ (1 / 2048 : ℝ) * density := by
      gcongr
    _ = (1 / 512 : ℝ) * density / 4 := by ring

/-- The second denominator is at least 200 times rank, enough for the
doubled-middle Holder-small inclusion. -/
lemma two_hundred_mul_max_rank_le_mTwo {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost) :
    200 * max r 1 ≤ mTwo d rankCost := by
  have hmax := max_rank_le_rankCap hrankCost hrank
  unfold mTwo
  calc
    200 * max r 1 ≤ 200 * rankCap d rankCost :=
      Nat.mul_le_mul_left 200 hmax
    _ ≤ 76800 * rankCap d rankCost * 2 ^ (d + 1) := by
      have hcoeff : 200 ≤ 76800 := by omega
      calc
        200 * rankCap d rankCost ≤ 76800 * rankCap d rankCost :=
          Nat.mul_le_mul_right _ hcoeff
        _ ≤ 76800 * rankCap d rankCost * 2 ^ (d + 1) :=
          Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)

/-- Concrete doubled-middle scale condition in the exact NNReal shape
needed by Holder approximation. -/
lemma two_inv_mTwo_le_rank_scale {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost) :
    (mTwo d rankCost : NNReal)⁻¹ + (mTwo d rankCost : NNReal)⁻¹ ≤
      1 / (100 * (max r 1 : ℕ) : NNReal) := by
  have hden := two_hundred_mul_max_rank_le_mTwo hrankCost hrank
  have hleft : (0 : NNReal) < mTwo d rankCost := by
    exact_mod_cast mTwo_pos hrankCost
  have hright : (0 : NNReal) < 200 * (max r 1 : ℕ) := by
    positivity
  have hinv :
      (mTwo d rankCost : NNReal)⁻¹ ≤
        (200 * (max r 1 : ℕ) : NNReal)⁻¹ := by
    apply (inv_le_inv₀ hleft hright).2
    exact_mod_cast hden
  calc
    (mTwo d rankCost : NNReal)⁻¹ + (mTwo d rankCost : NNReal)⁻¹ ≤
        (200 * (max r 1 : ℕ) : NNReal)⁻¹ +
          (200 * (max r 1 : ℕ) : NNReal)⁻¹ :=
      add_le_add hinv hinv
    _ = 1 / (100 * (max r 1 : ℕ) : NNReal) := by
      have hrpos : (0 : NNReal) < (max r 1 : ℕ) := by positivity
      field_simp
      norm_num

end

end Erdos140.ConcreteNumerics

#print axioms Erdos140.ConcreteNumerics.inv_mOne_le_rank_scale
#print axioms Erdos140.ConcreteNumerics.mOne_scale_density
#print axioms Erdos140.ConcreteNumerics.two_inv_mTwo_le_rank_scale
