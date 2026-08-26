import ErdosProblems.Erdos421.ReferenceWindowFits
import ErdosProblems.Erdos421.ReferenceRoughWindow

/-! # Lower and upper bounds for the actual reference rough windows -/

namespace Erdos421

open Filter Topology

theorem reference_rough_window_bounds {L η : ℝ} (hL : 2 ≤ L) (hη : 0 < η) :
    ∀ᶠ X : ℕ in atTop, ∀ y ∈ Set.Icc (Real.log (X : ℝ)) (Real.log (2 * X : ℝ)),
      (11 / 20 : ℝ) / Real.log (intermediatePrimeCutoff X) - η / Real.log X ≤
        logarithmicRoughWindow (3 * X) (intermediatePrimeCutoff X) ((Real.log X) ^ (-L)) y ∧
      ∀ p ∈ sievePrimes (intermediatePrimeCutoff X) (outerPrimeCutoff X),
        logarithmicRoughWindow (3 * X / p) (intermediatePrimeCutoff X) ((Real.log X) ^ (-L))
          (y - Real.log p) ≤ (23 / 40 : ℝ) / Real.log (intermediatePrimeCutoff X) +
            η / Real.log X := by
  have href := tendsto_natCast_atTop_atTop.eventually
    (logarithmicRoughWindow_reference_asymptotic 3 (by norm_num : (0 : ℝ) < 9 / 20) hL hη)
  filter_upwards [href, eventually_reference_window_fits, eventually_ge_atTop 2]
    with X hrefX hfit hX
  intro y hy
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hxlo : (X : ℝ) ≤ Real.exp y := by
    have h := Real.exp_le_exp.mpr hy.1
    rwa [Real.exp_log hXp] at h
  have hxhi : Real.exp y ≤ (2 * X : ℝ) := by
    have h := Real.exp_le_exp.mpr hy.2
    rwa [Real.exp_log (by positivity : (0 : ℝ) < 2 * X)] at h
  obtain ⟨hparent, harg, hchildren⟩ := hfit.2 (Real.exp y) hxlo hxhi
    ((Real.log X) ^ (-L)) hrefX.2.1
  have hZ1 : (1 : ℝ) < intermediatePrimeCutoff X :=
    by exact_mod_cast (show 1 < intermediatePrimeCutoff X by have h := hparent.cutoff; omega)
  have hLZ := Real.log_pos hZ1
  have hp := hrefX.2.2 (Real.exp y) hparent.scale (3 * X) (intermediatePrimeCutoff X)
    hparent.cutoff hparent.square hparent.power hparent.support
  rw [Real.log_exp] at hp harg
  have hlower := div_le_div_of_nonneg_right
    (finiteBuchstab_lower 3 (u := y / Real.log (intermediatePrimeCutoff X))
      ⟨harg.1, by norm_num; exact harg.2⟩) hLZ.le
  refine ⟨?_, ?_⟩
  · have he := (abs_le.mp hp).1
    linarith
  · intro p hpP
    obtain ⟨hcfit, hcarg⟩ := hchildren p hpP
    have hpp := (Finset.mem_filter.mp hpP).2
    have hpr : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hc := hrefX.2.2 (Real.exp y / p) hcfit.scale (3 * X / p)
      (intermediatePrimeCutoff X) hcfit.cutoff hcfit.square hcfit.power hcfit.support
    have hlog : Real.log (Real.exp y / p) = y - Real.log p := by
      rw [Real.log_div (Real.exp_pos y).ne' hpr.ne', Real.log_exp]
    rw [hlog] at hc hcarg
    have hupper := div_le_div_of_nonneg_right (finiteBuchstab_upper 4 hcarg) hLZ.le
    have he := (abs_le.mp hc).2
    linarith

end Erdos421
