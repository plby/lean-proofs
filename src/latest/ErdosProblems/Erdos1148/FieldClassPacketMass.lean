import ErdosProblems.Erdos1148.OrderClassNumberBound
import ErdosProblems.Erdos1148.OrderUnitIndexPeriod

/-! # Packet mass bounded below by field arithmetic and residue units -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped ENNReal

theorem field_class_mul_residue_index_mul_regulator_le_packetMass
    {d : ℤ} [hns : Fact (¬IsSquare d)] (hd : 0 < d) (base : PrimitiveIntegralFormOrbits d) :
    (Nat.card (ClassGroup (𝓞 (QuadraticDiscrAlgebra d))) : ℝ≥0∞) *
        ((orderResidueUnitSubgroup base.1.out.2).index : ℝ≥0∞) *
        ENNReal.ofReal (2 * NumberField.Units.regulator (QuadraticDiscrAlgebra d)) ≤
      discriminantPacket hd hns.out Set.univ := by
  have hnat := field_class_card_mul_residue_index_le_order_class_card_mul_unit_index
    hd base.1.out.2
  have hcard : (Nat.card (ClassGroup (𝓞 (QuadraticDiscrAlgebra d))) : ℝ≥0∞) *
      ((orderResidueUnitSubgroup base.1.out.2).index : ℝ≥0∞) ≤
      (Nat.card (ClassGroup (quadraticOrder d)) : ℝ≥0∞) *
        ((orderUnitSubgroup base.1.out.2).index : ℝ≥0∞) := by exact_mod_cast hnat
  have hfactor : ENNReal.ofReal (2 * ((orderUnitSubgroup base.1.out.2).index : ℝ) *
      NumberField.Units.regulator (QuadraticDiscrAlgebra d)) =
      ((orderUnitSubgroup base.1.out.2).index : ℝ≥0∞) *
        ENNReal.ofReal (2 * NumberField.Units.regulator (QuadraticDiscrAlgebra d)) := by
    rw [show 2 * ((orderUnitSubgroup base.1.out.2).index : ℝ) *
        NumberField.Units.regulator (QuadraticDiscrAlgebra d) =
        ((orderUnitSubgroup base.1.out.2).index : ℝ) *
          (2 * NumberField.Units.regulator (QuadraticDiscrAlgebra d)) by ring,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hmass := orderClass_mul_unitIndex_mul_regulator_le_packetMass hd base
  rw [hfactor, ← mul_assoc] at hmass
  exact (mul_le_mul' hcard le_rfl).trans hmass

end Erdos1148.DukeArithmetic
