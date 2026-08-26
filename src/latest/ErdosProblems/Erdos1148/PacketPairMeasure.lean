import ErdosProblems.Erdos1148.PacketCarrier

/-! # Measuring a pair image with the whole discriminant packet -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped ENNReal

lemma packetOrbit_measure_other_carrier {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {p q : IntegralFormOrbits d} (hpq : p ≠ q) :
    (packetOrbit hd hns p).measure (packetOrbit hd hns q).carrier = 0 := by
  apply measure_mono_null _ (packetOrbit hd hns p).measure_compl_carrier
  intro x hx hxp
  exact Set.disjoint_left.mp (packet_carriers_pairwise_disjoint hd hns hpq) hxp hx

theorem packetProduct_apply_of_subset_carriers {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (p q : IntegralFormOrbits d) {E : Set (ModularOrbitSpace × ModularOrbitSpace)}
    (hE : E ⊆ (packetOrbit hd hns p).carrier ×ˢ (packetOrbit hd hns q).carrier) :
    (discriminantPacket hd hns).prod (discriminantPacket hd hns) E =
      (packetOrbit hd hns p).measure.prod (packetOrbit hd hns q).measure E := by
  classical
  let := finite_integralFormOrbits hd hns
  rw [discriminantPacket, Measure.prod_sum, Measure.sum_apply_of_countable]
  apply tsum_eq_single (p, q)
  intro i hi
  apply measure_mono_null hE
  rw [Measure.prod_prod]
  by_cases hp : i.1 = p
  · have hq : i.2 ≠ q := fun hq => hi (Prod.ext hp hq)
    rw [packetOrbit_measure_other_carrier hd hns hq, mul_zero]
  · rw [packetOrbit_measure_other_carrier hd hns hp, zero_mul]

theorem packetProduct_pairImage {d ℓ : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (q : IntegralPairOrbits d ℓ) (η : ℝ) :
    (discriminantPacket hd hns).prod (discriminantPacket hd hns) (packetPairImage hd q η) =
      (packetOrbit hd hns (pairOrbitFirst q)).measure.prod
        (packetOrbit hd hns (pairOrbitSecond q)).measure (packetPairImage hd q η) :=
  packetProduct_apply_of_subset_carriers hd hns _ _ (packetPairImage_subset_carriers hd hns q η)

theorem packetProduct_pairImage_iUnion_le {d ℓ : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (η : ℝ) :
    (discriminantPacket hd hns).prod (discriminantPacket hd hns)
        (⋃ q : IntegralPairOrbits d ℓ, packetPairImage hd q η) ≤
      packetPairImageMass hd hns ℓ η := by
  calc
    _ ≤ ∑' q : IntegralPairOrbits d ℓ,
        (discriminantPacket hd hns).prod (discriminantPacket hd hns) (packetPairImage hd q η) :=
      measure_iUnion_le _
    _ = _ := by simp only [packetProduct_pairImage, packetPairImageMass]

end Erdos1148.DukeArithmetic
