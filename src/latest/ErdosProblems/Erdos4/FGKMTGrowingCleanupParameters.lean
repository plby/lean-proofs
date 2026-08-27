import ErdosProblems.Erdos4.FGKMTGrowingSmoothBound
import ErdosProblems.Erdos4.FGKMTGrowingPrimeSupply

/-! The zero-residue cutoff and smoothness frontier fit the concrete growing interval. -/

namespace Erdos4.FGKMT

open Filter

theorem eventually_growing_zero_parameters {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      0 < x / 32 ∧ growingRandomStart x ≤ growingRandomEnd x ∧
      growingRandomEnd x ≤ x / 32 ∧
      growingGapLength c x ≤ growingRandomStart x * (x / 32) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_growing_gap_length_bounds hc,
    eventually_growing_random_cutoff_logs, eventually_growing_outer_log_budget,
    eventually_growing_random_end_le_radius, eventually_growingRadius_bounds,
    hlog.eventually (eventually_ge_atTop (max 64 c)), eventually_ge_atTop 64]
    with x hlength hcut hlogs hzR hR hlarge hx
  let L := Real.log (x : ℝ)
  have hL64 : 64 ≤ L := (le_max_left _ _).trans hlarge
  have hcL : c ≤ L := (le_max_right _ _).trans hlarge
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hbase : 0 < x / 32 := by omega
  have hRself : growingRadius x ≤ growingRadius x ^ 2 := by nlinarith [hR.1]
  have hzbase : growingRandomEnd x ≤ x / 32 :=
    hzR.trans (hRself.trans (growingRadius_sq_le_source_start hR.1))
  refine ⟨hbase, hcut.2.1, hzbase, ?_⟩
  have hwpos : (0 : ℝ) < growingRandomStart x := by exact_mod_cast (show 0 < growingRandomStart x by omega)
  have hpoww : L ^ 50 ≤ (growingRandomStart x : ℝ) := by
    apply (Real.log_le_log_iff (pow_pos hLpos 50) hwpos).mp
    simpa only [Real.log_pow, Nat.cast_ofNat, L] using hcut.2.2.1
  have hwlarge : 64 * L ^ 2 ≤ (growingRandomStart x : ℝ) := by
    calc
      _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right hL64 (sq_nonneg L)
      _ = L ^ 3 := by ring
      _ ≤ L ^ 50 := pow_le_pow_right₀ hL1 (by norm_num)
      _ ≤ _ := hpoww
  have hYbound : (growingGapLength c x : ℝ) ≤ (x : ℝ) * L ^ 2 := by
    have hscale : growingOuterScale x ≤ L := hlogs.2.2.2.2
    calc
      _ ≤ c * x * growingOuterScale x := hlength.2.2.2.2.2.2
      _ ≤ c * x * L := mul_le_mul_of_nonneg_left hscale (mul_nonneg hc.le hxpos.le)
      _ ≤ L * x * L := by gcongr
      _ = _ := by ring
  have hxb : (x : ℝ) ≤ 64 * ((x / 32 : ℕ) : ℝ) := by
    exact_mod_cast (show x ≤ 64 * (x / 32) by omega)
  have hh : (growingGapLength c x : ℝ) ≤
      (growingRandomStart x : ℝ) * ((x / 32 : ℕ) : ℝ) := by
    calc
      _ ≤ (x : ℝ) * L ^ 2 := hYbound
      _ ≤ (64 * ((x / 32 : ℕ) : ℝ)) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hxb (sq_nonneg L)
      _ = (64 * L ^ 2) * ((x / 32 : ℕ) : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hwlarge (Nat.cast_nonneg _)
  exact_mod_cast hh

end Erdos4.FGKMT
