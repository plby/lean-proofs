import ErdosProblems.Erdos745.MeanBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Critical lower tightness from tree-component windows -/

open Filter
open scoped BigOperators Topology

namespace Erdos745

theorem criticalScale_nonneg (n : ℕ) : 0 ≤ criticalScale n := by
  unfold criticalScale
  positivity

theorem criticalScale_cube (n : ℕ) : criticalScale n ^ 3 = (n : ℝ) ^ 2 := by
  rw [criticalScale, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num

theorem criticalScale_tendsto : Tendsto criticalScale atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
    tendsto_natCast_atTop_atTop

theorem four_mul_criticalScale_le {n : ℕ} (hn : 64 ≤ n) :
    4 * criticalScale n ≤ n := by
  apply (pow_le_pow_iff_left₀ (mul_nonneg (by norm_num) (criticalScale_nonneg n))
    (Nat.cast_nonneg n) (by decide : (3 : ℕ) ≠ 0)).mp
  rw [mul_pow, criticalScale_cube]
  have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num only [show (4 : ℝ) ^ 3 = 64 by norm_num]
  calc
    64 * (n : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hnR (sq_nonneg _)
    _ = _ := by ring

theorem critical_window_mean_bound {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hmn : 4 * m ≤ n) (hscale : (2 * (m : ℝ)) ^ 3 ≤ 8 * (n : ℝ) ^ 2) :
    Real.exp (-19) * (n : ℝ) / (4 * Real.sqrt 2 * (m : ℝ) * Real.sqrt m) ≤
      ∑ k ∈ Finset.Icc m (2 * m), treeMean 1 n k := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsqrt : Real.sqrt (m : ℝ) ≠ 0 := by positivity
  let a := Real.exp (-19) * (n : ℝ) /
    ((2 * (m : ℝ)) ^ 2 * Real.sqrt (2 * (m : ℝ)))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc m (2 * m)) : a ≤ treeMean 1 n k := by
    obtain ⟨hkm, hk2m⟩ := Finset.mem_Icc.mp hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk2mR : (k : ℝ) ≤ 2 * m := by exact_mod_cast hk2m
    have hden : (k : ℝ) ^ 2 * Real.sqrt k ≤
        (2 * (m : ℝ)) ^ 2 * Real.sqrt (2 * (m : ℝ)) := by
      exact mul_le_mul (pow_le_pow_left₀ hkR.le hk2mR 2) (Real.sqrt_le_sqrt hk2mR)
        (Real.sqrt_nonneg _) (sq_nonneg _)
    calc
      a ≤ Real.exp (-19) * (n : ℝ) / ((k : ℝ) ^ 2 * Real.sqrt k) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ treeMean 1 n k := critical_treeMean_lower_constant hn (by omega) (by omega)
        ((pow_le_pow_left₀ hkR.le hk2mR 3).trans hscale)
  have hcard : (Finset.Icc m (2 * m)).card = m + 1 := by
    rw [Nat.card_Icc]
    omega
  calc
    _ = (m : ℝ) * a := by
      dsimp [a]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
      ring
    _ ≤ ((m + 1 : ℕ) : ℝ) * a := mul_le_mul_of_nonneg_right (by norm_cast; omega) ha
    _ = ∑ _k ∈ Finset.Icc m (2 * m), a := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ _ := Finset.sum_le_sum hterm

theorem scaled_root_cube_bound {n m : ℕ} {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hm : (m : ℝ) ≤ c * criticalScale n) :
    (m : ℝ) * Real.sqrt m ≤ c * n := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hc3 : c ^ 3 ≤ c ^ 2 := by nlinarith [sq_nonneg c]
  have hcube : (m : ℝ) ^ 3 ≤ c ^ 2 * (n : ℝ) ^ 2 := by
    calc
      _ ≤ (c * criticalScale n) ^ 3 := pow_le_pow_left₀ hm0 hm 3
      _ = c ^ 3 * (n : ℝ) ^ 2 := by rw [mul_pow, criticalScale_cube]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc3 (sq_nonneg _)
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (m : ℝ) * Real.sqrt m)
    (by positivity : 0 ≤ c * (n : ℝ)) (by decide : (2 : ℕ) ≠ 0)).mp
  rw [mul_pow, Real.sq_sqrt hm0, mul_pow]
  nlinarith only [hcube]

theorem critical_window_mean_scaled {n m : ℕ} {c : ℝ} (hn : 64 ≤ n) (hm : 2 ≤ m)
    (hc : 0 < c) (hc1 : c ≤ 1) (hmc : (m : ℝ) ≤ c * criticalScale n) :
    Real.exp (-19) / (4 * Real.sqrt 2 * c) ≤
      ∑ k ∈ Finset.Icc m (2 * m), treeMean 1 n k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmScale : (m : ℝ) ≤ criticalScale n := hmc.trans
    ((mul_le_mul_of_nonneg_right hc1 (criticalScale_nonneg n)).trans_eq (one_mul _))
  have hmn : 4 * m ≤ n := by
    have h := (mul_le_mul_of_nonneg_left hmScale (by norm_num : (0 : ℝ) ≤ 4)).trans
      (four_mul_criticalScale_le hn)
    exact_mod_cast h
  have hscale : (2 * (m : ℝ)) ^ 3 ≤ 8 * (n : ℝ) ^ 2 := by
    calc
      _ ≤ (2 * criticalScale n) ^ 3 := pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left hmScale (by norm_num)) 3
      _ = _ := by rw [mul_pow, criticalScale_cube]; norm_num
  have hroot := scaled_root_cube_bound hc hc1 hmc
  calc
    _ = Real.exp (-19) * (n : ℝ) / (4 * Real.sqrt 2 * (c * n)) := by
      field_simp
    _ ≤ Real.exp (-19) * (n : ℝ) / (4 * Real.sqrt 2 * ((m : ℝ) * Real.sqrt m)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hroot (by positivity))
    _ ≤ _ := by
      rw [← mul_assoc]
      exact critical_window_mean_bound (by omega) hm hmn hscale

/-- The second-largest critical component is bounded away from zero on the
`n^(2/3)` scale, with the full epsilon-dependent probability quantifiers. -/
theorem critical_lower_tightness : CriticalLowerTightness := by
  intro ε hε
  let g : ℝ := Real.exp (-19) / (4 * Real.sqrt 2)
  have hg : 0 < g := by dsimp [g]; positivity
  let c : ℝ := min 1 (min (g / 4) (ε * g / 8))
  have hc : 0 < c := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcg : c ≤ g / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcε : c ≤ ε * g / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hmean4 : 4 ≤ g / c := by
    rw [le_div_iff₀ hc]
    linarith
  have herror : 4 * c / g ≤ ε := by
    rw [div_le_iff₀ hg]
    nlinarith
  refine ⟨c / 2, by positivity, ?_⟩
  have ht : Tendsto (fun n ↦ c * criticalScale n) atTop atTop :=
    Tendsto.const_mul_atTop hc criticalScale_tendsto
  filter_upwards [eventually_ge_atTop (64 : ℕ), ht.eventually (eventually_ge_atTop (2 : ℝ))]
    with n hn hcn
  let m := ⌊c * criticalScale n⌋₊
  have hnonneg : 0 ≤ c * criticalScale n := mul_nonneg hc.le (criticalScale_nonneg n)
  have hm : 2 ≤ m := (Nat.le_floor_iff hnonneg).mpr hcn
  have hmc : (m : ℝ) ≤ c * criticalScale n := Nat.floor_le hnonneg
  have hmlower : c / 2 * criticalScale n ≤ (m : ℝ) := by
    have h := Nat.lt_floor_add_one (c * criticalScale n)
    change c * criticalScale n < (m : ℝ) + 1 at h
    nlinarith
  have hwindow : g / c ≤ ∑ k ∈ Finset.Icc m (2 * m), treeMean 1 n k := by
    simpa only [g, div_div] using critical_window_mean_scaled hn hm hc hc1 hmc
  have hw2 : 2 ≤ ∑ k ∈ Finset.Icc m (2 * m), treeMean 1 n k :=
    (by norm_num : (2 : ℝ) ≤ 4).trans (hmean4.trans hwindow)
  have hfail : 4 / (∑ k ∈ Finset.Icc m (2 * m), treeMean 1 n k) ≤ ε := by
    calc
      _ ≤ 4 / (g / c) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hwindow
      _ = 4 * c / g := by field_simp
      _ ≤ _ := herror
  have hprob := critical_secondLargest_ge_probability (by omega : 2 ≤ n) (by omega : 0 < m)
    (Finset.Icc m (2 * m)) (fun k hk ↦ (Finset.mem_Icc.mp hk).1) hw2
  have hmono : probability 1 n (fun G ↦ m ≤ secondLargestComponentOrder G) ≤
      criticalProbability n (fun G ↦ c / 2 * criticalScale n ≤ secondOrder n G) := by
    rw [← probability_one]
    apply probability_mono
    intro G hG
    have hGR : (m : ℝ) ≤ secondOrder n G := by
      unfold secondOrder
      exact_mod_cast hG
    exact hmlower.trans hGR
  exact (show 1 - ε ≤ 1 - 4 / (∑ k ∈ Finset.Icc m (2 * m), treeMean 1 n k) by linarith).trans
    (hprob.trans hmono)

end Erdos745
