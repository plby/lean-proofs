/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The roots within logarithmic distance of `1` have zero logarithmic density.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointBounds

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem intervalRootCount_mono (ε : ℕ → ℝ) (n : ℕ) {l₁ l₂ u₁ u₂ : ℝ}
    (hl : l₂ ≤ l₁) (hu : u₁ ≤ u₂) :
    intervalRootCount ε n l₁ u₁ ≤ intervalRootCount ε n l₂ u₂ := by
  classical
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxroot, hxI⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxroot, hl.trans hxI.1, hxI.2.trans hu⟩

theorem log_div_le_double_on_block {n m : ℕ} (hn : 1 < n) (hnm : n ≤ m) (hmn : m ≤ 2 * n) :
    Real.log m / m ≤ 2 * (Real.log n / n) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hmn' : (m : ℝ) ≤ 2 * n := by exact_mod_cast hmn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlogm : Real.log m ≤ 2 * Real.log n := by
    calc
      Real.log m ≤ Real.log (2 * n) := Real.log_le_log hm₀ hmn'
      _ = Real.log 2 + Real.log n := Real.log_mul (by norm_num) hn₀.ne'
      _ ≤ _ := by have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn₂; linarith
  calc
    Real.log m / m ≤ (2 * Real.log n) / m := div_le_div_of_nonneg_right hlogm hm₀.le
    _ ≤ (2 * Real.log n) / n := div_le_div_of_nonneg_left (by positivity) hn₀ hnm'
    _ = _ := mul_div_assoc _ _ _

theorem endpointCenter_block_le {C : ℝ} (hC : 0 ≤ C) {n m : ℕ}
    (hn : 1 < n) (hnm : n ≤ m) (hmn : m ≤ 2 * n) :
    endpointCenter (2 * C) n ≤ endpointCenter C m := by
  have h := mul_le_mul_of_nonneg_left (log_div_le_double_on_block hn hnm hmn) hC
  dsimp [endpointCenter]
  simp only [mul_div_assoc] at *
  nlinarith

theorem nat_log_two_tendsto : Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  exact (eventually_ge_atTop (2 ^ k)).mono fun _ h ↦ Nat.le_log_of_pow_le (by norm_num) h

theorem ae_endpoint_bound {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η) :
    ∀ᵐ ε ∂sequenceLaw, ∀ᶠ n : ℕ in atTop,
      (intervalRootCount ε n (endpointCenter C n) 1 : ℝ) ≤ η * Real.log n := by
  filter_upwards [ae_endpoint_dyadic_bound (2 * C) hη] with ε hε
  filter_upwards [nat_log_two_tendsto.eventually hε, eventually_ge_atTop 2] with n hn hn₂
  have hn₀ : n ≠ 0 := by omega
  have hlogNat : Nat.log 2 n ≠ 0 := (Nat.log_pos (by norm_num) hn₂).ne'
  have hN : 1 < (2 : ℕ) ^ Nat.log 2 n := one_lt_pow₀ (by norm_num) hlogNat
  have hNn : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn₀
  have hnN : n ≤ 2 * (2 : ℕ) ^ Nat.log 2 n := by
    have h := (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n).le
    simpa only [pow_succ, mul_comm] using h
  have hmono := intervalRootCount_mono ε n (endpointCenter_block_le hC hN hNn hnN) (le_refl 1)
  have hmono' : (intervalRootCount ε n (endpointCenter C n) 1 : ℝ) ≤
      (intervalRootCount ε n (endpointCenter (2 * C) (2 ^ Nat.log 2 n)) 1 : ℝ) := by
    exact_mod_cast hmono
  have hbound := hn n hNn hnN
  have hlog : Real.log (2 ^ Nat.log 2 n : ℕ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast (show 0 < (2 : ℕ) ^ Nat.log 2 n by positivity))
      (by exact_mod_cast hNn)
  exact (hmono'.trans hbound).trans (mul_le_mul_of_nonneg_left hlog hη.le)

/-- The endpoint estimate is proved for the original infinite sign sequence and
counts distinct roots, including a possible root at `1`. -/
theorem ae_endpointRootCount_div_log_tendsto_zero {C : ℝ} (hC : 0 ≤ C) :
    ∀ᵐ ε ∂sequenceLaw,
      Tendsto (fun n : ℕ ↦ (intervalRootCount ε n (endpointCenter C n) 1 : ℝ) / Real.log n)
        atTop (𝓝 0) := by
  have h : ∀ᵐ ε ∂sequenceLaw, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      (intervalRootCount ε n (endpointCenter C n) 1 : ℝ) ≤ (1 / (k + 1 : ℝ)) * Real.log n := by
    apply ae_all_iff.mpr
    intro k
    exact ae_endpoint_bound hC (by positivity)
  filter_upwards [h] with ε hε
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    exact hb.trans_le (div_nonneg (Nat.cast_nonneg _) hlog)
  · intro b hb
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hb
    filter_upwards [hε k, eventually_ge_atTop 2] with n hn hn₂
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    exact ((div_le_iff₀ hlog).mpr hn).trans_lt hk

end Erdos521
