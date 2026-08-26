import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The area of a unit circular sector

Polar change of variables reduces the sector area to two elementary
one-dimensional integrals. This is the analytic ingredient for identifying
the local sector weights of a tiling with its Euclidean corner angles.
-/

namespace Erdos633

open MeasureTheory Set

noncomputable def unitAngularSector (θ : ℝ) : Set ℂ :=
  {z | ‖z‖ ∈ Ioo (0 : ℝ) 1 ∧ z.arg ∈ Ioo (0 : ℝ) θ}

theorem measurableSet_unitAngularSector (θ : ℝ) : MeasurableSet (unitAngularSector θ) :=
  (measurableSet_Ioo.preimage measurable_norm).inter
    (measurableSet_Ioo.preimage Complex.measurable_arg)

theorem polar_mem_unitAngularSector (θ : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ Complex.polarCoord.target) :
    Complex.polarCoord.symm p ∈ unitAngularSector θ ↔
      p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) θ := by
  have h := Complex.polarCoord.right_inv hp
  rw [Complex.polarCoord_apply] at h
  have hn : ‖Complex.polarCoord.symm p‖ = p.1 := congrArg Prod.fst h
  have ha : (Complex.polarCoord.symm p).arg = p.2 := congrArg Prod.snd h
  change (‖Complex.polarCoord.symm p‖ ∈ Ioo (0 : ℝ) 1 ∧
    (Complex.polarCoord.symm p).arg ∈ Ioo (0 : ℝ) θ) ↔ _
  rw [hn, ha]

theorem polar_sector_indicator (θ : ℝ) (hθ : θ ≤ Real.pi) (p : ℝ × ℝ) :
    polarCoord.target.indicator
      (fun q => q.1 * (unitAngularSector θ).indicator (fun _ => (1 : ℝ))
        (Complex.polarCoord.symm q)) p =
      (Ioo (0 : ℝ) 1).indicator (fun r => r) p.1 *
        (Ioo (0 : ℝ) θ).indicator (fun _ => (1 : ℝ)) p.2 := by
  classical
  by_cases hp : p ∈ Complex.polarCoord.target
  · have hs := polar_mem_unitAngularSector θ p hp
    change p ∈ polarCoord.target at hp
    rw [Set.indicator_of_mem hp]
    by_cases hr : p.1 ∈ Ioo (0 : ℝ) 1
    · by_cases ha : p.2 ∈ Ioo (0 : ℝ) θ
      · rw [Set.indicator_of_mem (hs.mpr ⟨hr, ha⟩),
          Set.indicator_of_mem hr, Set.indicator_of_mem ha]
      · have hnot : Complex.polarCoord.symm p ∉ unitAngularSector θ :=
          fun h => ha (hs.mp h).2
        rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem ha]
        simp only [mul_zero]
    · have hnot : Complex.polarCoord.symm p ∉ unitAngularSector θ :=
        fun h => hr (hs.mp h).1
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hr]
      simp only [mul_zero, zero_mul]
  · change p ∉ polarCoord.target at hp
    rw [Set.indicator_of_notMem hp]
    by_cases hr : p.1 ∈ Ioo (0 : ℝ) 1
    · have ha : p.2 ∉ Ioo (0 : ℝ) θ := by
        intro ha
        apply hp
        exact ⟨hr.1, by linarith [Real.pi_pos, ha.1], ha.2.trans_le hθ⟩
      simp [Set.indicator_of_notMem, ha]
    · simp [Set.indicator_of_notMem, hr]

theorem volume_unitAngularSector_toReal (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    (volume (unitAngularSector θ)).toReal = θ / 2 := by
  have htarget : MeasurableSet polarCoord.target :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hr : (∫ r in Ioo (0 : ℝ) 1, r) = (1 : ℝ) / 2 := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num), integral_id]
    norm_num
  have ha : (∫ _ in Ioo (0 : ℝ) θ, (1 : ℝ)) = θ := by
    rw [integral_const]
    simp [measureReal_restrict_apply MeasurableSet.univ, Real.volume_real_Ioo_of_le hθ0]
  change volume.real (unitAngularSector θ) = θ / 2
  rw [← integral_indicator_one (measurableSet_unitAngularSector θ),
    ← Complex.integral_comp_polarCoord_symm]
  simp only [smul_eq_mul]
  rw [← integral_indicator htarget]
  change (∫ p : ℝ × ℝ, polarCoord.target.indicator
    (fun q => q.1 * (unitAngularSector θ).indicator (fun _ => (1 : ℝ))
      (Complex.polarCoord.symm q)) p) = θ / 2
  simp_rw [polar_sector_indicator θ hθπ]
  rw [Measure.volume_eq_prod, integral_prod_mul,
    integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ioo, hr, ha]
  ring

end Erdos633
