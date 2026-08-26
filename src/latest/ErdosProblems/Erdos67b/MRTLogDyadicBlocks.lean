import ErdosProblems.Erdos67b.MRTAllFrequencies

/-! # Exact anchored dyadic decomposition of a logarithmically weighted window -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

def mrtLogWindowBlockCount (W : ℕ) : ℕ := Nat.log 2 W + 2

def mrtWeightedDyadicBlock (N X j : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ n ∈ dyadicNatBlock N j, if n ≤ X then g n / n else 0

theorem mrtLogWindow_lower_bounds {X W : ℕ} (hW : 0 < W) (hWX : W ≤ X) :
    0 < X / W ∧ X ≤ 2 * W * (X / W) := by
  have hN : 0 < X / W := Nat.div_pos hWX hW
  have hnext : X < (X / W + 1) * W :=
    (Nat.div_lt_iff_lt_mul hW).1 (Nat.lt_succ_self _)
  refine ⟨hN, ?_⟩
  calc
    X ≤ (X / W + 1) * W := hnext.le
    _ ≤ (2 * (X / W)) * W := Nat.mul_le_mul_right W (by omega)
    _ = _ := by ring

theorem mrtLogWindow_dyadic_cover {X W : ℕ} (hW : 0 < W) (hWX : W ≤ X) :
    X ≤ 2 ^ mrtLogWindowBlockCount W * (X / W) := by
  have hpow := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) W
  have htwopow : 2 * W ≤ 2 ^ mrtLogWindowBlockCount W := by
    calc
      _ ≤ 2 * 2 ^ (Nat.log 2 W + 1) := Nat.mul_le_mul_left 2 hpow.le
      _ = _ := by simp only [mrtLogWindowBlockCount, pow_succ]; ring
  exact (mrtLogWindow_lower_bounds hW hWX).2.trans
    (Nat.mul_le_mul_right (X / W) htwopow)

theorem mrtSum_Ioc_weighted_eq_blocks (N X J : ℕ) (g : ℕ → ℝ)
    (hcover : X ≤ 2 ^ J * N) :
    (∑ n ∈ Finset.Ioc N X, g n / n) =
      ∑ j ∈ Finset.range J, mrtWeightedDyadicBlock N X j g := by
  have hset : (dyadicNatWindow N J).filter (fun n ↦ n ≤ X) = Finset.Ioc N X := by
    ext n
    simp only [Finset.mem_filter, mem_dyadicNatWindow, Finset.mem_Ioc]
    omega
  rw [← hset, Finset.sum_filter, sum_dyadicNatWindow_eq_sum_blocks]
  rfl

theorem mrtElliott_weighted_eq_blocks {X W : ℕ} (hW : 0 < W) (hWX : W ≤ X)
    (g : ℕ → ℝ) :
    (∑ n ∈ elliottLogWindow X W, g n / n) =
      ∑ j ∈ Finset.range (mrtLogWindowBlockCount W), mrtWeightedDyadicBlock (X / W) X j g := by
  rw [elliottLogWindow_eq_Ioc hW]
  exact mrtSum_Ioc_weighted_eq_blocks _ _ _ g (mrtLogWindow_dyadic_cover hW hWX)

theorem mrtWeightedDyadicBlock_eq_Ioc (N X j : ℕ) (g : ℕ → ℝ) :
    mrtWeightedDyadicBlock N X j g =
      ∑ n ∈ Finset.Ioc (2 ^ j * N) (2 * (2 ^ j * N)), if n ≤ X then g n / n else 0 := by
  unfold mrtWeightedDyadicBlock dyadicNatBlock
  rw [show 2 ^ (j + 1) * N = 2 * (2 ^ j * N) by rw [pow_succ]; ring]

theorem mrtWeighted_Ioc_truncated_le {Y : ℕ} (hY : 0 < Y) (X : ℕ) (g : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) {δ : ℝ} (hsum : (∑ n ∈ Finset.Ioc Y (2 * Y), g n) ≤ δ * Y) :
    (∑ n ∈ Finset.Ioc Y (2 * Y), if n ≤ X then g n / n else 0) ≤ δ := by
  have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
  calc
    _ ≤ ∑ n ∈ Finset.Ioc Y (2 * Y), g n / n := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs
      · exact le_refl _
      · exact div_nonneg (hg n) (Nat.cast_nonneg n)
    _ ≤ ∑ n ∈ Finset.Ioc Y (2 * Y), g n / Y := by
      apply Finset.sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_left (hg n) hYreal
        (by exact_mod_cast (Finset.mem_Ioc.1 hn).1.le)
    _ = (∑ n ∈ Finset.Ioc Y (2 * Y), g n) / Y := (Finset.sum_div _ _ _).symm
    _ ≤ δ := (div_le_iff₀ hYreal).2 hsum

theorem mrtWeightedDyadicBlock_le_one {N : ℕ} (hN : 0 < N) (X j : ℕ) (g : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) (hg1 : ∀ n, 0 < n → g n ≤ 1) :
    mrtWeightedDyadicBlock N X j g ≤ 1 := by
  rw [mrtWeightedDyadicBlock_eq_Ioc]
  apply mrtWeighted_Ioc_truncated_le (Nat.mul_pos (pow_pos (by norm_num) _) hN) X g hg
  calc
    _ ≤ ∑ _n ∈ Finset.Ioc (2 ^ j * N) (2 * (2 ^ j * N)), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hg1 n ((Nat.zero_le _).trans_lt (Finset.mem_Ioc.1 hn).1)
    _ = _ := by
      have hcard : (Finset.Ioc (2 ^ j * N) (2 * (2 ^ j * N))).card = 2 ^ j * N := by
        rw [Nat.card_Ioc]
        omega
      simp [hcard]

theorem mrtWeightedDyadicBlock_eq_zero {N X j : ℕ} (hX : X ≤ 2 ^ j * N) (g : ℕ → ℝ) :
    mrtWeightedDyadicBlock N X j g = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hlow := (mem_dyadicNatBlock.1 hn).1
  simp only [show ¬n ≤ X by omega, ↓reduceIte]

theorem mrtSum_blocks_le_early_add {J B : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (a : ℕ → ℝ)
    (htrivial : ∀ j ∈ Finset.range J, a j ≤ 1)
    (hgood : ∀ j ∈ Finset.range J, B ≤ j → a j ≤ δ) :
    (∑ j ∈ Finset.range J, a j) ≤ B + δ * J := by
  classical
  have hcard : ((Finset.range J).filter (fun j ↦ j < B)).card ≤ B := by
    apply (Finset.card_le_card (show (Finset.range J).filter (fun j ↦ j < B) ⊆
        Finset.range B from fun j hj ↦ Finset.mem_range.2 (Finset.mem_filter.1 hj).2)).trans_eq
    exact Finset.card_range B
  have hcardR : (((Finset.range J).filter (fun j ↦ j < B)).card : ℝ) ≤ B := by
    exact_mod_cast hcard
  calc
    _ ≤ ∑ j ∈ Finset.range J, ((if j < B then (1 : ℝ) else 0) + δ) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases h : j < B
      · simp only [h, ↓reduceIte]
        exact (htrivial j hj).trans (le_add_of_nonneg_right hδ)
      · simpa only [h, ↓reduceIte, zero_add] using hgood j hj (by omega)
    _ = ((Finset.range J).filter (fun j ↦ j < B)).card + δ * J := by
      rw [Finset.sum_add_distrib, Finset.sum_boole]
      simp [mul_comm]
    _ ≤ _ := add_le_add hcardR (le_refl _)

end

end Erdos67b
