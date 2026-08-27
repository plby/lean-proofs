/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPowerParameters

/-! # The fixed coupled hierarchy supplies the auxiliary degree clock budget -/

namespace Erdos207

theorem neighbor_clock_small_of_power_scale
    (N M t L : ℝ) (R b : ℕ) (hN : 0 < N) (hM : M ≤ N) (ht : 32 ≤ t)
    (hscale : t ^ R ≤ N) (hgap : 2 * b + 1 ≤ R) (hL : N ^ 2 / t ^ (2 * b) ≤ L) :
    19 * M / L ≤ 1 := by
  have htpos : 0 < t := by linarith
  have hLpos : 0 < L := (by positivity : 0 < N ^ 2 / t ^ (2 * b)).trans_le hL
  have hlarge : 19 * t ^ (2 * b) ≤ N :=
    (real_coeff_mul_pow_le_pow (by linarith) (by linarith : (19 : ℝ) ≤ t) hgap).trans hscale
  apply (div_le_one hLpos).mpr
  calc
    19 * M ≤ 19 * N := by linarith only [hM]
    _ ≤ N ^ 2 / t ^ (2 * b) := by
      apply (le_div_iff₀ (pow_pos htpos _)).mpr
      have hm := mul_le_mul_of_nonneg_right hlarge hN.le
      nlinarith only [hm]
    _ ≤ L := hL

theorem KSSSPowerParameters.scalar_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (time : ℝ) (htime : 0 ≤ time) (hfloor : 1 / (t : ℝ) ^ b ≤ ksssEdgeDensity E time) :
    KSSSScalarPowerBounds q b B k a E A time (Fintype.card V) t :=
  ksss_scalar_power_bounds q b B k Rmin a coeff E A time (Fintype.card V) t
    P.edge_pos P.available_pos htime (by exact_mod_cast P.ambient_pos)
    (by exact_mod_cast P.scale_large) (by exact_mod_cast P.power_scale)
    P.edge_floor P.ratio_lower P.ratio_upper hfloor P.coefficient_nonneg P.coefficient_bound P.coefficient_budget

end Erdos207
