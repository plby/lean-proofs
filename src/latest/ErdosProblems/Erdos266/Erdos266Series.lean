import ErdosProblems.Erdos266.Erdos266Construction
import ErdosProblems.Erdos266.Erdos266Scales

/-!
# Coordinate block series for Erdős problem 266

These definitions and lemmas connect the geometric scales with the abstract
diagonal construction.  They contain no finite-dimensional approximation:
only positivity, comparison, regrouping, and tail identities.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos266

noncomputable section

/-- The unperturbed contribution of geometric block `k` in coordinate `i+1`. -/
def referenceCoordinateBlock (dim : ℕ → ℕ) (i k : ℕ) : ℝ :=
  ∑ j : Fin (dim k), reciprocalCoordinate (i + 1)
    ((((j.1 + 1) * N k : ℕ) : ℝ))

/-- The contribution after applying a total family of integral offsets. -/
def actualCoordinateBlock (dim : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (i k : ℕ) : ℝ :=
  ∑ j : Fin (dim k), reciprocalCoordinate (i + 1)
    (blockNat N z k j.1 : ℝ)

lemma referenceCoordinateBlock_nonneg (dim : ℕ → ℕ) (i k : ℕ) :
    0 ≤ referenceCoordinateBlock dim i k := by
  exact Finset.sum_nonneg fun _ _ => reciprocalCoordinate_nonneg _ (by positivity)

lemma referenceCoordinateBlock_le (dim : ℕ → ℕ)
    (hdim : ∀ k, dim k ≤ k + 1) (i k : ℕ) :
    referenceCoordinateBlock dim i k ≤ ((k + 1 : ℕ) : ℝ) / N k := by
  calc
    referenceCoordinateBlock dim i k
        ≤ ∑ _j : Fin (dim k), (1 : ℝ) / N k := by
          unfold referenceCoordinateBlock
          apply Finset.sum_le_sum
          intro j _
          have hpoint : (0 : ℝ) < (((j.1 + 1) * N k : ℕ) : ℝ) := by
            exact_mod_cast Nat.mul_pos (Nat.succ_pos j.1) (N_pos k)
          calc
            reciprocalCoordinate (i + 1) ((((j.1 + 1) * N k : ℕ) : ℝ))
                ≤ ((((j.1 + 1) * N k : ℕ) : ℝ))⁻¹ :=
                  reciprocalCoordinate_le_inv (i + 1) (by omega) hpoint
            _ ≤ (N k : ℝ)⁻¹ := by
                  apply inv_anti₀ (by exact_mod_cast N_pos k)
                  exact_mod_cast Nat.le_mul_of_pos_left (N k) (Nat.succ_pos j.1)
            _ = (1 : ℝ) / N k := by simp [one_div]
    _ = (dim k : ℝ) * (1 / N k) := by simp
    _ ≤ (k + 1 : ℝ) * (1 / N k) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdim k) (by positivity)
    _ = ((k + 1 : ℕ) : ℝ) / N k := by push_cast; ring

theorem summable_referenceCoordinateBlock (dim : ℕ → ℕ)
    (hdim : ∀ k, dim k ≤ k + 1) (i : ℕ) :
    Summable (referenceCoordinateBlock dim i) := by
  exact Summable.of_nonneg_of_le
    (referenceCoordinateBlock_nonneg dim i)
    (referenceCoordinateBlock_le dim hdim i)
    summable_succ_div_N

/-- The unperturbed tail beginning at stage `k`. -/
def referenceCoordinateTail (dim : ℕ → ℕ) (i k : ℕ) : ℝ :=
  ∑' n, referenceCoordinateBlock dim i (n + k)

lemma referenceCoordinateTail_succ (dim : ℕ → ℕ)
    (hdim : ∀ k, dim k ≤ k + 1) (i k : ℕ) :
    referenceCoordinateTail dim i k =
      referenceCoordinateBlock dim i k + referenceCoordinateTail dim i (k + 1) := by
  unfold referenceCoordinateTail
  rw [(summable_nat_add_iff k).2 (summable_referenceCoordinateBlock dim hdim i) |>.tsum_eq_zero_add]
  simp only [Nat.zero_add]
  congr 1
  apply tsum_congr
  intro n
  apply congrArg (referenceCoordinateBlock dim i)
  omega

theorem tendsto_referenceCoordinateTail (dim : ℕ → ℕ) (i : ℕ) :
    Tendsto (referenceCoordinateTail dim i) atTop (𝓝 0) := by
  unfold referenceCoordinateTail
  convert (tendsto_sum_nat_add (referenceCoordinateBlock dim i)) using 1

lemma actualCoordinateBlock_nonneg (dim : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (_hpos : ∀ k j, 0 < blockNat N z k j) (i k : ℕ) :
    0 ≤ actualCoordinateBlock dim z i k := by
  exact Finset.sum_nonneg fun j _ =>
    reciprocalCoordinate_nonneg _ (Nat.cast_nonneg _)

/-- Bounded offsets make every actual coordinate block series summable. -/
theorem summable_actualCoordinateBlock
    (dim : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (hz : OffsetsBounded M z) (hdim : ∀ k, dim k ≤ k + 1) (i : ℕ) :
    Summable (actualCoordinateBlock dim z i) := by
  have htwoM : ∀ k, 2 * M k ≤ N k := by
    intro k
    rw [← M_sq]
    have hM4 : 4 ≤ M k := by
      rw [M]
      exact Nat.le_pow (a := 4) (by omega)
    nlinarith
  have hsigma := summable_coordinate_blocks dim N M z N_pos htwoM hz hdim
    summable_succ_div_N (i + 1) (by omega)
  have hsplit := (summable_sigma_of_nonneg (fun _ =>
    reciprocalCoordinate_nonneg _ (Nat.cast_nonneg _))).mp hsigma
  convert hsplit.2 using 1
  funext k
  rw [tsum_fintype]
  rfl

/-- Regroup the sigma-indexed coordinate series as the series of actual blocks. -/
theorem tsum_actualCoordinateBlock
    (dim : ℕ → ℕ) (z : ℕ → ℕ → ℤ)
    (hz : OffsetsBounded M z) (hdim : ∀ k, dim k ≤ k + 1) (i : ℕ) :
    (∑' p : Σ k, Fin (dim k),
      reciprocalCoordinate (i + 1) (blockNat N z p.1 p.2.1 : ℝ)) =
      ∑' k, actualCoordinateBlock dim z i k := by
  have htwoM : ∀ k, 2 * M k ≤ N k := by
    intro k
    rw [← M_sq]
    have hM4 : 4 ≤ M k := by
      rw [M]
      exact Nat.le_pow (a := 4) (by omega)
    nlinarith
  simpa only [actualCoordinateBlock] using
    (tsum_coordinate_blocks dim N M z N_pos htwoM hz hdim
      summable_succ_div_N (i + 1) (by omega))

/-- The nested-box radius used for coordinate `i` at stage `k`. -/
def coordinateRadius (ε : ℕ → ℝ) (dim : ℕ → ℕ) (i k : ℕ) : ℝ :=
  ε (dim k) * (M k : ℝ) / (N k : ℝ) ^ (i + 2)

lemma coordinateRadius_pos (ε : ℕ → ℝ) (dim : ℕ → ℕ)
    (hε : ∀ d, 0 < ε d) (i k : ℕ) :
    0 < coordinateRadius ε dim i k := by
  unfold coordinateRadius
  exact div_pos (mul_pos (hε (dim k)) (by exact_mod_cast M_pos k))
    (pow_pos (by exact_mod_cast N_pos k) _)

lemma coordinateRadius_le_inv_N (ε : ℕ → ℝ) (dim : ℕ → ℕ)
    (_hε0 : ∀ d, 0 ≤ ε d) (hε1 : ∀ d, ε d ≤ 1) (i k : ℕ) :
    coordinateRadius ε dim i k ≤ (1 : ℝ) / N k := by
  have hN : (0 : ℝ) < N k := by exact_mod_cast N_pos k
  have hden : (0 : ℝ) < (N k : ℝ) ^ (i + 2) := pow_pos hN _
  have hM : (0 : ℝ) ≤ M k := by positivity
  have hMN : (M k : ℝ) ≤ N k := by exact_mod_cast M_le_N k
  have hpowNat : N k ^ 2 ≤ N k ^ (i + 2) :=
    Nat.pow_le_pow_right (one_le_N k) (by omega)
  have hpow : (N k : ℝ) ^ 2 ≤ (N k : ℝ) ^ (i + 2) := by
    exact_mod_cast hpowNat
  calc
    coordinateRadius ε dim i k
        ≤ 1 * (M k : ℝ) / (N k : ℝ) ^ (i + 2) := by
          unfold coordinateRadius
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hε1 (dim k)) hM) hden.le
    _ ≤ 1 * (N k : ℝ) / (N k : ℝ) ^ (i + 2) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hMN (by norm_num)) hden.le
    _ ≤ 1 * (N k : ℝ) / (N k : ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_left (by positivity) (pow_pos hN 2) hpow
    _ = (1 : ℝ) / N k := by field_simp

theorem tendsto_coordinateRadius (ε : ℕ → ℝ) (dim : ℕ → ℕ)
    (hε0 : ∀ d, 0 ≤ ε d) (hε1 : ∀ d, ε d ≤ 1) (i : ℕ) :
    Tendsto (coordinateRadius ε dim i) atTop (𝓝 0) := by
  have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / N k) atTop (𝓝 0) := by
    have hs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 0 / (N k : ℝ)) :=
      summable_polynomial_div_N 0
    simpa using hs.tendsto_atTop_zero
  exact squeeze_zero'
    (Eventually.of_forall fun k => by
      unfold coordinateRadius
      exact div_nonneg (mul_nonneg (hε0 (dim k)) (by positivity)) (by positivity))
    (Eventually.of_forall (coordinateRadius_le_inv_N ε dim hε0 hε1 i)) hinv

end

end Erdos266
