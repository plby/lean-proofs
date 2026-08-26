import ErdosProblems.Erdos1148.SharedPrimitivePeriod
import ErdosProblems.Erdos1148.DiscriminantPacket

/-! # The primitive packet mass as class count times common period -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups ENNReal

abbrev PrimitiveIntegralFormOrbits (d : ℤ) :=
  {q : IntegralFormOrbits d // PrimitiveIntegralForm q.out.1}

lemma primitiveIntegralForm_out_mk_iff {d : ℤ} (t : IntegralDiscrForm d) :
    PrimitiveIntegralForm (integralFormOrbitMk t).out.1 ↔ PrimitiveIntegralForm t.1 := by
  have hrel : MulAction.orbitRel SL(2, ℤ) (IntegralDiscrForm d)
      (integralFormOrbitMk t).out t := Quotient.exact (Quotient.out_eq (integralFormOrbitMk t))
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
  have hv : formAction γ t.1 = (integralFormOrbitMk t).out.1 := congrArg Subtype.val hγ
  rw [← hv]
  exact primitiveIntegralForm_formAction_iff γ t.1

noncomputable def primitivePacketMass {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) : ℝ≥0∞ :=
  ∑' q : PrimitiveIntegralFormOrbits d, ENNReal.ofReal (packetOrbit hd hns q.1).period

lemma primitivePacketMass_le_total {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    primitivePacketMass hd hns ≤ discriminantPacket hd hns Set.univ := by
  rw [primitivePacketMass, discriminantPacket_univ]
  exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _

theorem primitivePacketMass_eq_card_mul_period {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (base : PrimitiveIntegralFormOrbits d) :
    primitivePacketMass hd hns =
      (Nat.card (PrimitiveIntegralFormOrbits d) : ℝ≥0∞) *
        ENNReal.ofReal (packetOrbit hd hns base.1).period := by
  classical
  let := finite_integralFormOrbits hd hns
  let := Fintype.ofFinite (PrimitiveIntegralFormOrbits d)
  have heq (q : PrimitiveIntegralFormOrbits d) :
      (packetOrbit hd hns q.1).period = (packetOrbit hd hns base.1).period :=
    ClosedFlowOrbit.primitive_period_eq hd q.2 base.2 q.1.out.2 base.1.out.2
      _ _ (packetOrbit_form hd hns q.1) (packetOrbit_form hd hns base.1)
  simp only [primitivePacketMass, heq, tsum_fintype, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem card_mul_primitive_period_le_packetMass {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (base : PrimitiveIntegralFormOrbits d) :
    (Nat.card (PrimitiveIntegralFormOrbits d) : ℝ≥0∞) *
        ENNReal.ofReal (packetOrbit hd hns base.1).period ≤ discriminantPacket hd hns Set.univ := by
  rw [← primitivePacketMass_eq_card_mul_period hd hns base]
  exact primitivePacketMass_le_total hd hns

end Erdos1148.DukeArithmetic
