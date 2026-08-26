import ErdosProblems.Erdos1148.OrderUnitSubgroup
import ErdosProblems.Erdos1148.SubgroupRegulatorBound
import ErdosProblems.Erdos1148.OrderClassPacketMass

/-! # The order-unit index as a factor in the primitive period bound -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped ENNReal

theorem ClosedFlowOrbit.orderUnitSubgroup_finiteIndex {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (htd : discr t = d)
    (o : ClosedFlowOrbit)
    (ho : Real.sqrt (d : ℝ) • formAction o.lift (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t) :
    (orderUnitSubgroup htd).FiniteIndex := by
  obtain ⟨u, hu, hlog⟩ := exists_orderSubgroupUnit_of_primitive_period hd ht htd o ho
  apply unitSubgroup_finiteIndex (quadraticDiscrAlgebra_card_infinitePlace hd)
    (quadraticRealPlace hd) (quadraticRealPlace_isReal hd) (orderUnitSubgroup htd)
    (torsion_le_orderUnitSubgroup hd htd) u hu
  intro hz
  rw [hz, abs_zero] at hlog
  linarith [o.period_pos]

theorem ClosedFlowOrbit.orderUnitIndex_mul_regulator_le_half_period
    {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (htd : discr t = d)
    (o : ClosedFlowOrbit)
    (ho : Real.sqrt (d : ℝ) • formAction o.lift (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t) :
    ((orderUnitSubgroup htd).index : ℝ) * NumberField.Units.regulator (QuadraticDiscrAlgebra d) ≤
      o.period / 2 := by
  obtain ⟨u, hu, hlog⟩ := exists_orderSubgroupUnit_of_primitive_period hd ht htd o ho
  have hn : Real.log (quadraticRealPlace hd (u : QuadraticDiscrAlgebra d)) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hlog
    linarith [o.period_pos]
  exact (unitSubgroup_index_mul_regulator_le (quadraticDiscrAlgebra_card_infinitePlace hd)
    (quadraticRealPlace hd) (quadraticRealPlace_isReal hd) (orderUnitSubgroup htd)
    (torsion_le_orderUnitSubgroup hd htd) u hu hn).trans hlog.le

theorem orderClass_mul_unitIndex_mul_regulator_le_packetMass
    {d : ℤ} [hns : Fact (¬IsSquare d)] (hd : 0 < d) (base : PrimitiveIntegralFormOrbits d) :
    (Nat.card (ClassGroup (quadraticOrder d)) : ℝ≥0∞) *
        ENNReal.ofReal (2 * ((orderUnitSubgroup base.1.out.2).index : ℝ) *
          NumberField.Units.regulator (QuadraticDiscrAlgebra d)) ≤
      discriminantPacket hd hns.out Set.univ := by
  have hreg := (packetOrbit hd hns.out base.1).orderUnitIndex_mul_regulator_le_half_period hd
    base.2 base.1.out.2 (packetOrbit_form hd hns.out base.1)
  have hperiod : 2 * ((orderUnitSubgroup base.1.out.2).index : ℝ) *
      NumberField.Units.regulator (QuadraticDiscrAlgebra d) ≤
      (packetOrbit hd hns.out base.1).period := by linarith
  exact (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hperiod)).trans
    (orderClass_card_mul_period_le_packetMass hd base)

end Erdos1148.DukeArithmetic
