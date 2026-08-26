import ErdosProblems.Erdos1148.QuadraticInfinitePlace
import ErdosProblems.Erdos1148.RankOneRegulator
import ErdosProblems.Erdos1148.OrderClassPacketMass

/-! # Comparing primitive periods and packet mass with the field regulator -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped ENNReal

theorem ClosedFlowOrbit.regulator_le_half_period {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (htd : discr t = d)
    (o : ClosedFlowOrbit)
    (ho : Real.sqrt (d : ℝ) • formAction o.lift (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t) :
    NumberField.Units.regulator (QuadraticDiscrAlgebra d) ≤ o.period / 2 := by
  obtain ⟨u, hu⟩ := o.exists_integerUnit_abs_log hd ht htd ho
  have hu' : |Real.log (quadraticRealPlace hd (u : QuadraticDiscrAlgebra d))| = o.period / 2 := by
    rw [quadraticRealPlace_apply]
    exact hu
  have hn : Real.log (quadraticRealPlace hd (u : QuadraticDiscrAlgebra d)) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hu'
    linarith [o.period_pos]
  exact (regulator_le_abs_log_of_two_places (quadraticDiscrAlgebra_card_infinitePlace hd)
    (quadraticRealPlace hd) (quadraticRealPlace_isReal hd) u hn).trans hu'.le

theorem orderClass_mul_regulator_le_packetMass {d : ℤ} [hns : Fact (¬IsSquare d)]
    (hd : 0 < d) (base : PrimitiveIntegralFormOrbits d) :
    (Nat.card (ClassGroup (quadraticOrder d)) : ℝ≥0∞) *
        ENNReal.ofReal (2 * NumberField.Units.regulator (QuadraticDiscrAlgebra d)) ≤
      discriminantPacket hd hns.out Set.univ := by
  have hreg := (packetOrbit hd hns.out base.1).regulator_le_half_period hd base.2
    base.1.out.2 (packetOrbit_form hd hns.out base.1)
  have hperiod : 2 * NumberField.Units.regulator (QuadraticDiscrAlgebra d) ≤
      (packetOrbit hd hns.out base.1).period := by linarith
  exact (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hperiod)).trans
    (orderClass_card_mul_period_le_packetMass hd base)

end Erdos1148.DukeArithmetic
