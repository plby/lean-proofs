import ErdosProblems.Erdos1148.IdealFormClassSurjective

/-! # A packet-volume lower bound in terms of the quadratic-order class group -/

namespace Erdos1148.DukeArithmetic

open scoped ENNReal

theorem quadraticOrder_classGroup_finite {d : ℤ} [hns : Fact (¬IsSquare d)]
    (hd : 0 < d) {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Finite (ClassGroup (quadraticOrder d)) := by
  let := finite_integralFormOrbits hd hns.out
  exact Finite.of_surjective (primitiveFormOrbitClass (d := d))
    (primitiveFormOrbitClass_surjective ht)

theorem classGroup_card_le_primitiveFormOrbits {d : ℤ} [hns : Fact (¬IsSquare d)]
    (hd : 0 < d) {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Nat.card (ClassGroup (quadraticOrder d)) ≤ Nat.card (PrimitiveIntegralFormOrbits d) := by
  let := finite_integralFormOrbits hd hns.out
  exact Nat.card_le_card_of_surjective _ (primitiveFormOrbitClass_surjective ht)

theorem orderClass_card_mul_period_le_packetMass {d : ℤ} [hns : Fact (¬IsSquare d)]
    (hd : 0 < d) (base : PrimitiveIntegralFormOrbits d) :
    (Nat.card (ClassGroup (quadraticOrder d)) : ℝ≥0∞) *
        ENNReal.ofReal (packetOrbit hd hns.out base.1).period ≤
      discriminantPacket hd hns.out Set.univ := by
  have hcard := classGroup_card_le_primitiveFormOrbits hd base.1.out.2
  have hcard' : (Nat.card (ClassGroup (quadraticOrder d)) : ℝ≥0∞) ≤
      (Nat.card (PrimitiveIntegralFormOrbits d) : ℝ≥0∞) := by exact_mod_cast hcard
  exact (mul_le_mul' hcard' le_rfl).trans
    (card_mul_primitive_period_le_packetMass hd hns.out base)

end Erdos1148.DukeArithmetic
