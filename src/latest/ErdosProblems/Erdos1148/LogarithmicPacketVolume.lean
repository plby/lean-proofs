import ErdosProblems.Erdos1148.PeriodPellMatrix
import ErdosProblems.Erdos1148.PacketComponentMeasure

/-!
# An elementary logarithmic lower bound for packet volume

A monic integral form has a period longer than `log d`. This is useful
for divergence of packet volume, but is much weaker than the power
lower bound needed for the equidistribution argument.
-/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups ENNReal

theorem log_discr_lt_monic_period {d : ℤ} (hd : 0 < d) {t : ℤ × ℤ × ℤ} (ha : t.1 = 1)
    (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (γ : SL(2, ℤ)) {s : ℝ} (hs0 : 0 < s)
    (hs : (γ : SL(2, ℝ)) * g = g * diagonalFlow s) : Real.log (d : ℝ) < s := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hρ := Real.sqrt_pos.mpr hdR
  have hmat := integral_period_pellFormMatrix hd g hg γ s hs
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) hmat
  change (γ 1 0 : ℝ) = 2 * (t.1 : ℝ) * (-Real.sinh (s / 2) / Real.sqrt (d : ℝ)) at hentry
  rw [ha, Int.cast_one, mul_one] at hentry
  have hsinh : 0 < Real.sinh (s / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hneg : (γ 1 0 : ℝ) < 0 := by
    rw [hentry]
    exact mul_neg_of_pos_of_neg (by norm_num)
      (div_neg_of_neg_of_pos (neg_neg_of_pos hsinh) hρ)
  have hnegZ : γ 1 0 < 0 := by exact_mod_cast hneg
  have hle : (γ 1 0 : ℝ) ≤ -1 := by exact_mod_cast (show γ 1 0 ≤ -1 by omega)
  have hmul := (div_eq_iff hρ.ne').mp
    (show -2 * Real.sinh (s / 2) / Real.sqrt (d : ℝ) = (γ 1 0 : ℝ) by
      rw [hentry]; ring)
  have hroot : Real.sqrt (d : ℝ) ≤ 2 * Real.sinh (s / 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hle hρ.le]
  have hexp : Real.sqrt (d : ℝ) < Real.exp (s / 2) := by
    rw [Real.sinh_eq] at hroot
    linarith [Real.exp_pos (-(s / 2))]
  have hlog := (Real.log_lt_iff_lt_exp hρ).mpr hexp
  rw [Real.log_sqrt hdR.le] at hlog
  linarith

theorem packet_volume_ge_log_of_monic_form {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (t : IntegralDiscrForm d) (ha : t.1.1 = 1) :
    ENNReal.ofReal (Real.log (d : ℝ)) ≤ discriminantPacket hd hns Set.univ := by
  obtain ⟨o, ho⟩ := exists_closedFlowOrbit_of_integral_form hd hns t.2
  obtain ⟨γ, hγ⟩ := o.period_mem
  have hlog := log_discr_lt_monic_period hd ha o.lift ho γ o.period_pos hγ
  have hm := o.measure_eq_packetOrbit hd hns t (integralFormOrbitMk t) rfl ho
  calc
    ENNReal.ofReal (Real.log (d : ℝ)) ≤ ENNReal.ofReal o.period :=
      ENNReal.ofReal_le_ofReal hlog.le
    _ = (packetOrbit hd hns (integralFormOrbitMk t)).measure Set.univ := by
      rw [← hm, o.measure_univ]
    _ ≤ discriminantPacket hd hns Set.univ :=
      Measure.le_sum (fun q : IntegralFormOrbits d => (packetOrbit hd hns q).measure)
        (integralFormOrbitMk t) Set.univ

def principalFourForm (n : ℤ) : IntegralDiscrForm (4 * n) :=
  ⟨(1, 0, -n), by dsimp [discr]; ring⟩

theorem packet_volume_four_mul_ge_log {n : ℤ} (hd : 0 < 4 * n) (hns : ¬IsSquare (4 * n)) :
    ENNReal.ofReal (Real.log ((4 * n : ℤ) : ℝ)) ≤ discriminantPacket hd hns Set.univ :=
  packet_volume_ge_log_of_monic_form hd hns (principalFourForm n) rfl

end Erdos1148.DukeArithmetic
