import ErdosProblems.Erdos1148.FieldClassPacketMass
import ErdosProblems.Erdos1148.ResidueUnitLowerBound

/-! # A packet-mass lower bound with the numerical order index -/

namespace Erdos1148.DukeArithmetic

open NumberField
open scoped ENNReal

theorem exists_orderIndex_packetMass_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℤ) [hns : Fact (¬IsSquare d)] (hd : 0 < d)
      (base : PrimitiveIntegralFormOrbits d),
      (Nat.card (ClassGroup (𝓞 (QuadraticDiscrAlgebra d))) : ℝ≥0∞) *
          ENNReal.ofReal (c * (quadraticOrderIndex base.1.out.2 : ℝ) ^ (1 - ε)) *
          ENNReal.ofReal (2 * NumberField.Units.regulator (QuadraticDiscrAlgebra d)) ≤
        discriminantPacket hd hns.out Set.univ := by
  obtain ⟨c, hc, hbound⟩ := exists_residueUnitIndex_lower_bound hε
  refine ⟨c, hc, ?_⟩
  intro d hns hd base
  have hidx : ENNReal.ofReal (c * (quadraticOrderIndex base.1.out.2 : ℝ) ^ (1 - ε)) ≤
      ((orderResidueUnitSubgroup base.1.out.2).index : ℝ≥0∞) := by
    have h := ENNReal.ofReal_le_ofReal (hbound d base.1.out.1 base.1.out.2)
    simpa only [ENNReal.ofReal_natCast] using h
  exact (mul_le_mul' (mul_le_mul' le_rfl hidx) le_rfl).trans
    (field_class_mul_residue_index_mul_regulator_le_packetMass hd base)

end Erdos1148.DukeArithmetic
