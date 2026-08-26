import ErdosProblems.Erdos1148.UnconditionalCuspBound

/-! # Packet mass above any positive power of the discriminant tends to zero -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

theorem normalizedPacket_cusp_power_tendsto_zero {ι : Type*} {l : Filter ι} {d : ι → ℕ}
    (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hlim : Tendsto d l atTop)
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun i => (normalizedDiscriminantPacket (hd i) (hns i)).real
      (modularCusp ((d i : ℝ) ^ α))) l (𝓝 0) := by
  let ε : ℝ := min α (1 / 4)
  have hε : 0 < ε := lt_min hα (by norm_num)
  obtain ⟨C, hC, hbound⟩ := exists_unconditional_normalizedPacket_cusp_bound hε
  have hεα : ε ≤ α := min_le_left _ _
  have hεquarter : ε ≤ 1 / 4 := min_le_right _ _
  have he1 : ε / 4 - α * 2 < 0 := by linarith
  have he2 : -1 / 8 + ε / 4 < 0 := by linarith
  have hdRlim : Tendsto (fun i => (d i : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hlim
  have hp1 : Tendsto (fun i => (d i : ℝ) ^ (ε / 4 - α * 2)) l (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr he1)).comp hdRlim
  have hp2 : Tendsto (fun i => (d i : ℝ) ^ (-1 / 8 + ε / 4)) l (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr he2)).comp hdRlim
  have hupp : Tendsto (fun i => C * ((d i : ℝ) ^ (ε / 4 - α * 2) +
      (d i : ℝ) ^ (-1 / 8 + ε / 4))) l (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hp1.add hp2).const_mul C
  have hevent : ∀ᶠ i in l,
      (normalizedDiscriminantPacket (hd i) (hns i)).real (modularCusp ((d i : ℝ) ^ α)) ^ 2 ≤
        C * ((d i : ℝ) ^ (ε / 4 - α * 2) + (d i : ℝ) ^ (-1 / 8 + ε / 4)) := by
    filter_upwards [hlim.eventually (eventually_ge_atTop 16),
      ((tendsto_rpow_atTop hα).comp hdRlim).eventually (eventually_ge_atTop 2)] with i hi hheight
    have hdR : (0 : ℝ) < d i := by exact_mod_cast hd i
    have hpow : (d i : ℝ) ^ (ε / 4) / ((d i : ℝ) ^ α) ^ 2 =
        (d i : ℝ) ^ (ε / 4 - α * 2) := by
      rw [← Real.rpow_mul_natCast hdR.le, ← Real.rpow_sub hdR]
      norm_num
    simpa only [Function.comp_def, hpow] using hbound (d i) (hd i) (hns i) hi (base i) _ hheight
  have hsquared := squeeze_zero' (Eventually.of_forall (fun i => sq_nonneg
    ((normalizedDiscriminantPacket (hd i) (hns i)).real (modularCusp ((d i : ℝ) ^ α)))))
    hevent hupp
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsquared
  simpa only [Function.comp_def, Real.sqrt_sq measureReal_nonneg, Real.sqrt_zero] using hsqrt

end Erdos1148.DukeArithmetic
