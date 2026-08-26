import ErdosProblems.Erdos1148.ZetaResiduePacketMass
import ErdosProblems.Erdos1148.QuadraticSiegelResidue

/-! # The unconditional power lower bound for total discriminant-packet mass -/

namespace Erdos1148.DukeArithmetic

open scoped ENNReal

theorem exists_unconditional_primitive_packetMass_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℤ) [hns : Fact (¬IsSquare d)] (hd : 0 < d),
      PrimitiveIntegralFormOrbits d →
      ENNReal.ofReal (c * (d : ℝ) ^ (1 / 2 - ε)) ≤ discriminantPacket hd hns.out Set.univ := by
  obtain ⟨C, hC, hmass⟩ := exists_zetaResidue_packetMass_lower_bound (half_pos hε)
  obtain ⟨D, hD, hresidue⟩ := exists_quadratic_zetaResidue_lower_bound (half_pos hε)
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro d hns hd base
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hres := hresidue d hd base.1.out.1 base.1.out.2
  have hmul : C * D * (d : ℝ) ^ (1 / 2 - ε) ≤
      C * NumberField.dedekindZeta_residue (QuadraticDiscrAlgebra d) *
        (d : ℝ) ^ (1 / 2 - ε / 2) := by
    calc
      _ = C * (D * (d : ℝ) ^ (-(ε / 2))) * (d : ℝ) ^ (1 / 2 - ε / 2) := by
        have hp : (d : ℝ) ^ (-(ε / 2)) * (d : ℝ) ^ (1 / 2 - ε / 2) =
            (d : ℝ) ^ (1 / 2 - ε) := by
          rw [← Real.rpow_add hdR]
          congr 1
          ring
        rw [← hp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hres hC.le)
        (Real.rpow_nonneg hdR.le _)
  exact (ENNReal.ofReal_le_ofReal hmul).trans (hmass d hd base)

theorem exists_unconditional_packetMass_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℤ) (hd : 0 < d) (hns : ¬IsSquare d), IntegralDiscrForm d →
      ENNReal.ofReal (c * (d : ℝ) ^ (1 / 2 - ε)) ≤ discriminantPacket hd hns Set.univ := by
  obtain ⟨c, hc, hbound⟩ := exists_unconditional_primitive_packetMass_lower_bound hε
  refine ⟨c, hc, ?_⟩
  intro d hd hns base
  let : Fact (¬IsSquare d) := ⟨hns⟩
  let m : IntegralDiscrForm d :=
    ⟨monicCompanionForm base.1, (discr_monicCompanionForm base.1).trans base.2⟩
  have hm : PrimitiveIntegralForm (integralFormOrbitMk m).out.1 :=
    (primitiveIntegralForm_out_mk_iff m).mpr (primitive_monicCompanionForm base.1)
  exact hbound d hd ⟨integralFormOrbitMk m, hm⟩

end Erdos1148.DukeArithmetic
