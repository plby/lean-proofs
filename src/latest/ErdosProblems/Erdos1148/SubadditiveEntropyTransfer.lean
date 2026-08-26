import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Transferring long-block entropy lower bounds to fixed blocks -/

namespace Erdos1148.DukeArithmetic

open Filter
open scoped Topology

theorem subadditive_block_upper_bound {u : ℕ → ℝ} (hsub : Subadditive u)
    (hnonneg : ∀ n, 0 ≤ u n) {C : ℝ} (hC : 0 ≤ C)
    (hlinear : ∀ n, u n ≤ n * C) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    u n ≤ (n : ℝ) * (u k / k) + k * C := by
  have hsplit := hsub.apply_mul_add_le (n / k) k (n % k)
  rw [Nat.mul_comm (n / k) k, Nat.div_add_mod] at hsplit
  have hq : ((n / k : ℕ) : ℝ) * k ≤ (n : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self n k
  have hr : ((n % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt n hk).le
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmain : ((n / k : ℕ) : ℝ) * u k ≤ (n : ℝ) * (u k / k) := by
    apply (mul_le_mul_iff_left₀ hkR).mp
    calc
      ((n / k : ℕ) : ℝ) * u k * k =
          (((n / k : ℕ) : ℝ) * k) * u k := by ring
      _ ≤ (n : ℝ) * u k := mul_le_mul_of_nonneg_right hq (hnonneg k)
      _ = ((n : ℝ) * (u k / k)) * k := by field_simp
  calc
    u n ≤ ((n / k : ℕ) : ℝ) * u k + u (n % k) := hsplit
    _ ≤ (n : ℝ) * (u k / k) + ((n % k : ℕ) : ℝ) * C :=
      add_le_add hmain (hlinear _)
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hr hC)

theorem subadditive_fixed_block_lower_of_long_blocks {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → ℕ → ℝ) (v : ℕ → ℝ) (N : ι → ℕ)
    (hsub : ∀ i, Subadditive (u i)) (hnonneg : ∀ i n, 0 ≤ u i n)
    {C : ℝ} (hC : 0 ≤ C) (hlinear : ∀ i n, u i n ≤ n * C)
    (hN : Tendsto N l atTop) (hfixed : ∀ k, Tendsto (fun i => u i k) l (𝓝 (v k)))
    {a : ℝ} (hlower : ∀ᶠ i in l, a ≤ u i (N i) / N i)
    {k : ℕ} (hk : 0 < k) : a ≤ v k / k := by
  have hNR : Tendsto (fun i => (N i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hN
  have hvanish : Tendsto (fun i => (k : ℝ) * C / N i) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hNR
  have hlim : Tendsto (fun i => u i k / k + (k : ℝ) * C / N i) l
      (𝓝 (v k / k)) := by
    simpa only [add_zero] using ((hfixed k).div_const (k : ℝ)).add hvanish
  apply ge_of_tendsto hlim
  filter_upwards [hlower, hN.eventually (eventually_ge_atTop 1)] with i hi hNi
  have hnR : (0 : ℝ) < N i := by exact_mod_cast (show 0 < N i by omega)
  have hbound := subadditive_block_upper_bound (hsub i) (hnonneg i) hC (hlinear i) hk (N i)
  have hdiv := div_le_div_of_nonneg_right hbound hnR.le
  have heq : ((N i : ℝ) * (u i k / k) + k * C) / N i =
      u i k / k + (k : ℝ) * C / N i := by
    rw [add_div, mul_div_cancel_left₀ _ hnR.ne']
  exact hi.trans (hdiv.trans_eq heq)

end Erdos1148.DukeArithmetic
