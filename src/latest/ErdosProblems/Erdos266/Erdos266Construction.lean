import ErdosProblems.Erdos266.Erdos266Coordinates

/-!
# Block sequences for Erdős problem 266

This file contains the bookkeeping which turns bounded integral perturbations
of positive block centres into a positive summable family of natural numbers.
It is independent of the analytic construction which chooses the
perturbations.
-/

open scoped BigOperators

namespace Erdos266

/-- The integer represented by the `j`-th point in block `k`. -/
def blockInt (L : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (k : ℕ) (j : ℕ) : ℤ :=
  (((j + 1) * L k : ℕ) : ℤ) + z k j

/-- The corresponding natural denominator.  Positivity is proved below from
the perturbation bound. -/
def blockNat (L : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (k : ℕ) (j : ℕ) : ℕ :=
  (blockInt L z k j).toNat

/-- Every perturbation in block `k` has absolute value at most `R k`. -/
def OffsetsBounded (R : ℕ → ℕ) (z : ℕ → ℕ → ℤ) : Prop :=
  ∀ k j, |(z k j : ℝ)| ≤ R k

lemma blockInt_cast (L : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (k j : ℕ) :
    ((blockInt L z k j : ℤ) : ℝ) =
      ((j + 1 : ℕ) : ℝ) * L k + z k j := by
  simp [blockInt, Nat.cast_mul]

lemma blockInt_pos {L R : ℕ → ℕ} {z : ℕ → ℕ → ℤ}
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (k j : ℕ) :
    0 < blockInt L z k j := by
  have hzlower : -((R k : ℕ) : ℝ) ≤ (z k j : ℝ) :=
    neg_le_of_abs_le (hz k j)
  have hbase : ((L k : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * L k := by
    have hj : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    calc
      ((L k : ℕ) : ℝ) = 1 * (L k : ℝ) := by ring
      _ ≤ ((j + 1 : ℕ) : ℝ) * L k :=
        mul_le_mul_of_nonneg_right hj (Nat.cast_nonneg _)
  have hR : (2 : ℝ) * R k ≤ L k := by exact_mod_cast hRL k
  have hLreal : (0 : ℝ) < L k := by exact_mod_cast hL k
  have hreal : (0 : ℝ) < ((blockInt L z k j : ℤ) : ℝ) := by
    rw [blockInt_cast]
    nlinarith
  exact_mod_cast hreal

lemma blockNat_pos {L R : ℕ → ℕ} {z : ℕ → ℕ → ℤ}
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (k j : ℕ) :
    0 < blockNat L z k j := by
  have h := blockInt_pos hL hRL hz k j
  simp only [blockNat]
  omega

lemma blockNat_cast {L R : ℕ → ℕ} {z : ℕ → ℕ → ℤ}
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (k j : ℕ) :
    ((blockNat L z k j : ℕ) : ℝ) =
      ((j + 1 : ℕ) : ℝ) * L k + z k j := by
  have hnonneg : 0 ≤ blockInt L z k j := (blockInt_pos hL hRL hz k j).le
  have htoNat : (((blockInt L z k j).toNat : ℕ) : ℤ) = blockInt L z k j :=
    Int.toNat_of_nonneg hnonneg
  have hcast := congrArg (fun x : ℤ => (x : ℝ)) htoNat
  simpa only [blockNat, Int.cast_natCast, blockInt_cast] using hcast

lemma half_L_le_blockNat {L R : ℕ → ℕ} {z : ℕ → ℕ → ℤ}
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (k j : ℕ) :
    ((L k : ℕ) : ℝ) / 2 ≤ blockNat L z k j := by
  rw [blockNat_cast hL hRL hz]
  have hzlower : -((R k : ℕ) : ℝ) ≤ (z k j : ℝ) :=
    neg_le_of_abs_le (hz k j)
  have hbase : ((L k : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * L k := by
    have hj : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    have hLreal : (0 : ℝ) < L k := by exact_mod_cast hL k
    nlinarith
  have hR : (2 : ℝ) * R k ≤ L k := by exact_mod_cast hRL k
  nlinarith

lemma reciprocal_blockNat_le {L R : ℕ → ℕ} {z : ℕ → ℕ → ℤ}
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (k j : ℕ) :
    (1 : ℝ) / blockNat L z k j ≤ 2 / L k := by
  have hLreal : (0 : ℝ) < L k := by exact_mod_cast hL k
  have hhalfpos : (0 : ℝ) < (L k : ℝ) / 2 := div_pos hLreal (by norm_num)
  have hrecip := one_div_le_one_div_of_le hhalfpos (half_L_le_blockNat hL hRL hz k j)
  calc
    (1 : ℝ) / blockNat L z k j ≤ 1 / ((L k : ℝ) / 2) := hrecip
    _ = 2 / L k := by field_simp

/-- Reciprocal summability of the sigma-indexed family of all block points. -/
theorem summable_reciprocal_blocks
    (d L R : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (hd : ∀ k, d k ≤ k + 1)
    (hseries : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / L k)) :
    Summable (fun p : Σ k, Fin (d k) =>
      (1 : ℝ) / blockNat L z p.1 p.2.1) := by
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  constructor
  · intro k
    exact Summable.of_finite
  · have houter : Summable (fun k : ℕ => 2 * (((k + 1 : ℕ) : ℝ) / L k)) :=
      hseries.mul_left 2
    refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => by positivity) ?_ houter
    intro k
    rw [tsum_fintype]
    calc
      (∑ j : Fin (d k), (1 : ℝ) / blockNat L z k j.1)
          ≤ ∑ _j : Fin (d k), (2 : ℝ) / L k := by
              exact Finset.sum_le_sum fun j _ => reciprocal_blockNat_le hL hRL hz k j.1
      _ = (d k : ℝ) * (2 / L k) := by simp
      _ ≤ (k + 1 : ℝ) * (2 / L k) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd k) (by positivity)
      _ = 2 * (((k + 1 : ℕ) : ℝ) / L k) := by push_cast; ring

/-- Every positive triangular coordinate is summable on the block family. -/
theorem summable_coordinate_blocks
    (d L R : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (hd : ∀ k, d k ≤ k + 1)
    (hseries : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / L k))
    (i : ℕ) (hi : 1 ≤ i) :
    Summable (fun p : Σ k, Fin (d k) =>
      reciprocalCoordinate i (blockNat L z p.1 p.2.1 : ℝ)) := by
  apply Summable.of_nonneg_of_le
    (fun p => reciprocalCoordinate_nonneg i (Nat.cast_nonneg _))
    (fun p => ?_)
    (summable_reciprocal_blocks d L R z hL hRL hz hd hseries)
  have hp : (0 : ℝ) < blockNat L z p.1 p.2.1 := by
    exact_mod_cast blockNat_pos hL hRL hz p.1 p.2.1
  calc
    reciprocalCoordinate i (blockNat L z p.1 p.2.1 : ℝ)
        ≤ ((blockNat L z p.1 p.2.1 : ℝ))⁻¹ :=
          reciprocalCoordinate_le_inv i hi hp
    _ = (1 : ℝ) / blockNat L z p.1 p.2.1 := by simp [one_div]

/-- Regroup a coordinate `tsum` by blocks. -/
theorem tsum_coordinate_blocks
    (d L R : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (hL : ∀ k, 0 < L k) (hRL : ∀ k, 2 * R k ≤ L k)
    (hz : OffsetsBounded R z) (hd : ∀ k, d k ≤ k + 1)
    (hseries : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) / L k))
    (i : ℕ) (hi : 1 ≤ i) :
    (∑' p : Σ k, Fin (d k),
      reciprocalCoordinate i (blockNat L z p.1 p.2.1 : ℝ)) =
      ∑' k, ∑ j : Fin (d k),
        reciprocalCoordinate i (blockNat L z k j.1 : ℝ) := by
  have hs := summable_coordinate_blocks d L R z hL hRL hz hd hseries i hi
  rw [hs.tsum_sigma]
  congr 1
  funext k
  rw [tsum_fintype]

end Erdos266
