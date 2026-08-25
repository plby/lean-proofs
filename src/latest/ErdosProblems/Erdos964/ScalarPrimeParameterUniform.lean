import ErdosProblems.Erdos964.ScalarPrimeIntegrandPerturbation
import ErdosProblems.Erdos964.ScalarSupportLogWindows
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform parameter stability on the actual smaller-prime support
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem exists_scalar_prime_integrand_uniform_parameter_error (K : ℕ) (hK : 0 < K)
    (η β : ℝ) (hη : 0 < η) (hηβ : η < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℕ in atTop, ∀ p ∈ scalarSmallPrimeSupport η K t,
      let R := modulusCutoff β t
      let a := Real.log R / Real.log (t ^ 2 : ℕ)
      let z := Real.log p / Real.log R
      |scalarPrimeIntegrand a z - scalarPrimeIntegrand (β / 2) z| ≤ C * |a - β / 2| := by
  have hβ : 0 < β := hη.trans hηβ
  let B := 3 / (2 * β)
  obtain ⟨G, hG⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := B)).exists_bound_of_continuousOn
    continuous_scalarSieveFace.continuousOn
  refine ⟨|G| / (1 / 8 : ℝ) ^ 2, by positivity, ?_⟩
  have hA := (tendsto_order.mp (tendsto_log_scalar_power_radius_div_log_square β hβ)).2
    (7 * β / 12) (by linarith)
  filter_upwards [eventually_scalar_support_log_windows K hK η β hη hηβ hβ1, hA] with t ht hAt
  intro p hp
  dsimp only
  let R := modulusCutoff β t
  let a := Real.log R / Real.log (t ^ 2 : ℕ)
  let z := Real.log p / Real.log R
  have hspec := scalarSmallPrimeSupport_spec η K t p hp
  have hL : 0 < Real.log R := Real.log_pos
    (by exact_mod_cast (show 1 < R by have := ht.1; dsimp only [R]; omega))
  have hz0 : 0 < z := div_pos
    (Real.log_pos (by exact_mod_cast hspec.1.one_lt)) hL
  have hzB : z ≤ B := by
    calc
      z ≤ Real.log (t / (K + 1) : ℕ) / Real.log R :=
        div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast hspec.1.pos)
          (by exact_mod_cast hspec.2.1)) hL.le
      _ ≤ B := ht.2.2.2.2.2.2
  have hGz : |scalarSieveFace z| ≤ |G| := by
    exact (show |scalarSieveFace z| ≤ G by
      simpa only [Real.norm_eq_abs] using hG z ⟨hz0.le, hzB⟩).trans (le_abs_self G)
  have ha0 : 0 ≤ a := div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have haB : (7 * β / 12) * B = 7 / 8 := by dsimp only [B]; field_simp; norm_num
  have hbB : (β / 2) * B = 3 / 4 := by dsimp only [B]; field_simp; norm_num
  have haz : a * z ≤ 7 / 8 := by
    rw [← haB]
    exact mul_le_mul hAt.le hzB hz0.le (by positivity)
  have hbz : β / 2 * z ≤ 3 / 4 := by
    rw [← hbB]
    exact mul_le_mul_of_nonneg_left hzB (by positivity)
  exact scalarPrimeIntegrand_parameter_error a (β / 2) z (1 / 8) |G| hz0.ne'
    (by norm_num) (by linarith) (by linarith) hGz

end Erdos964
