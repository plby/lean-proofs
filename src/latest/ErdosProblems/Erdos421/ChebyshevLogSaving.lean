import ErdosProblems.Erdos421.PrimeErrorPrefixSaving
import Mathlib.NumberTheory.Chebyshev

/-! # A quantitative prime number theorem for Mathlib's Chebyshev psi function -/

namespace Erdos421

open Complex Filter Topology

theorem primeErrorPrefix_eq_psi_sub_floor (x : ℝ) :
    primeErrorPrefix x = ((Chebyshev.psi x - (⌊x⌋₊ : ℝ) : ℝ) : ℂ) := by
  have hψ : Chebyshev.psi x =
      ∑ n ∈ Finset.range ⌊x⌋₊, ArithmeticFunction.vonMangoldt (n + 1) := by
    rw [Chebyshev.psi_eq_sum_Icc, ← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ']
    simp only [ArithmeticFunction.map_zero, add_zero]
  have hterm : ∀ n : ℕ, LSeries.term primeErrorCoefficient 0 (n + 1) =
      (ArithmeticFunction.vonMangoldt (n + 1) : ℂ) - 1 := by
    intro n
    rw [LSeries.term_of_ne_zero (by omega : n + 1 ≠ 0), cpow_zero, div_one, primeErrorCoefficient]
  rw [primeErrorPrefix, finiteRealPrefix, Finset.sum_range_succ']
  simp only [LSeries.term_zero, add_zero, hterm, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hψ]
  push_cast
  rfl

theorem chebyshev_psi_log_saving {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ x : ℝ, X₀ ≤ x → |Chebyshev.psi x - x| ≤ ε * x / (Real.log x) ^ A := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨X₁, _, hsave⟩ := primeErrorPrefix_log_saving hA hhalf
  have hratio := (isLittleO_log_rpow_rpow_atTop A
    (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hlarge : ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ ε * x / (Real.log x) ^ A := by
    filter_upwards [eventually_ge_atTop (max X₁ 2), hratio.eventually (gt_mem_nhds hhalf)]
      with x hx hsmall
    have hxX : X₁ ≤ x := (le_max_left _ _).trans hx
    have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
    have hxp : 0 < x := by linarith
    have hL : 0 < Real.log x := Real.log_pos (by linarith)
    have hp : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hL A
    have hsmall' : (Real.log x) ^ A / x ≤ ε / 2 := by
      simpa only [Real.rpow_one] using hsmall.le
    have hnum := (div_le_iff₀ hxp).mp hsmall'
    have hone : 1 ≤ (ε / 2) * x / (Real.log x) ^ A := (one_le_div hp).mpr hnum
    have hprefix := hsave x hxX
    rw [primeErrorPrefix_eq_psi_sub_floor, Complex.norm_real, Real.norm_eq_abs] at hprefix
    have hfloor : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
      have hlo := Nat.floor_le hxp.le
      have hhi := Nat.lt_floor_add_one x
      apply abs_le.mpr
      constructor <;> linarith
    calc
      _ = |(Chebyshev.psi x - (⌊x⌋₊ : ℝ)) + ((⌊x⌋₊ : ℝ) - x)| := by congr 1; ring
      _ ≤ |Chebyshev.psi x - (⌊x⌋₊ : ℝ)| + |(⌊x⌋₊ : ℝ) - x| := abs_add_le _ _
      _ ≤ ((ε / 2) * x / (Real.log x) ^ A) + 1 := add_le_add hprefix hfloor
      _ ≤ ((ε / 2) * x / (Real.log x) ^ A) + ((ε / 2) * x / (Real.log x) ^ A) :=
        add_le_add le_rfl hone
      _ = _ := by ring
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max X₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro x hx
  exact hX₀ x ((le_max_left X₀ 2).trans hx)

end Erdos421
