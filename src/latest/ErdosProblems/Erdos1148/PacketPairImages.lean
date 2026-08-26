import ErdosProblems.Erdos1148.PacketComponentMeasure
import ErdosProblems.Erdos1148.PairOrbitComponents
import ErdosProblems.Erdos1148.ClosePairImage
import ErdosProblems.Erdos1148.NearPairArea

/-!
# Close-pair images measured in their packet components

We use exactly the real frames chosen in the arithmetic parameter-area
sum. Passing to the intrinsic closed-orbit measures only decreases the
area. The resulting sum has the same cubic bound; covering the packet's
close-pair set by these images is a separate step.
-/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups ENNReal

noncomputable def packetPairFirstOrbit {d ℓ : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (q : IntegralPairOrbits d ℓ) : ClosedFlowOrbit :=
  let f := chooseIntegralPairFrame hd q.out
  closedOrbitOfIntegralLift hd hns q.out.2.1 f.first f.first_form

noncomputable def packetPairSecondOrbit {d ℓ : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (q : IntegralPairOrbits d ℓ) : ClosedFlowOrbit :=
  let f := chooseIntegralPairFrame hd q.out
  closedOrbitOfIntegralLift hd hns q.out.2.2.1 f.second f.second_form

lemma packetPairFirstOrbit_measure {d ℓ : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (q : IntegralPairOrbits d ℓ) :
    (packetPairFirstOrbit hd hns q).measure = (packetOrbit hd hns (pairOrbitFirst q)).measure := by
  apply ClosedFlowOrbit.measure_eq_packetOrbit hd hns _ (pairFirstForm q.out) _
    (pairOrbitFirst_out q).symm
  exact (chooseIntegralPairFrame hd q.out).first_form

lemma packetPairSecondOrbit_measure {d ℓ : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (q : IntegralPairOrbits d ℓ) :
    (packetPairSecondOrbit hd hns q).measure =
      (packetOrbit hd hns (pairOrbitSecond q)).measure := by
  apply ClosedFlowOrbit.measure_eq_packetOrbit hd hns _ (pairSecondForm q.out) _
    (pairOrbitSecond_out q).symm
  exact (chooseIntegralPairFrame hd q.out).second_form

noncomputable def packetPairImage {d ℓ : ℤ} (hd : 0 < d) (q : IntegralPairOrbits d ℓ)
    (η : ℝ) : Set (ModularOrbitSpace × ModularOrbitSpace) :=
  let f := chooseIntegralPairFrame hd q.out
  finPairFlowCurve f.first f.second '' signedCloseDiagonalFlowTimes (f.first⁻¹ * f.second) η

lemma measurableSet_packetPairImage {d ℓ : ℤ} (hd : 0 < d)
    (q : IntegralPairOrbits d ℓ) (η : ℝ) :
    MeasurableSet (packetPairImage hd q η) :=
  measurableSet_image_of_isClosed_sigmaCompact (continuous_finPairFlowCurve _ _)
    (isClosed_signedCloseDiagonalFlowTimes _ _)

theorem packetPairImage_measure_le {d ℓ : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (q : IntegralPairOrbits d ℓ) (η : ℝ) :
    (packetOrbit hd hns (pairOrbitFirst q)).measure.prod
        (packetOrbit hd hns (pairOrbitSecond q)).measure (packetPairImage hd q η) ≤
      let f := chooseIntegralPairFrame hd q.out
      volume (signedCloseDiagonalFlowTimes (f.first⁻¹ * f.second) η) := by
  rw [← packetPairFirstOrbit_measure hd hns q, ← packetPairSecondOrbit_measure hd hns q]
  let o := packetPairFirstOrbit hd hns q
  let p := packetPairSecondOrbit hd hns q
  let : Fact (0 < o.period) := ⟨o.period_pos⟩
  let : Fact (0 < p.period) := ⟨p.period_pos⟩
  exact closedPair_image_le_parameterArea o.period_mem p.period_mem o.period_group p.period_group
    _ (measurableSet_packetPairImage hd q η)

noncomputable def packetPairImageMass {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (ℓ : ℤ) (η : ℝ) : ℝ≥0∞ :=
  ∑' q : IntegralPairOrbits d ℓ, (packetOrbit hd hns (pairOrbitFirst q)).measure.prod
    (packetOrbit hd hns (pairOrbitSecond q)).measure (packetPairImage hd q η)

lemma packetPairImageMass_le_parameterArea {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (ℓ : ℤ) (η : ℝ) : packetPairImageMass hd hns ℓ η ≤ pairOrbitParameterArea hd ℓ η :=
  ENNReal.tsum_le_tsum (fun q => packetPairImage_measure_le hd hns q η)

theorem exists_sum_packetPairImageMass_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)) (η : ℝ),
      0 < η → η ≤ 1 / 2 →
      (∑ ℓ ∈ noncentralMultiples (2 * d) ⌊4 * (d : ℝ) * η ^ 2⌋ 1,
        packetPairImageMass hd hns ℓ η) ≤ ENNReal.ofReal (K * (d : ℝ) ^ (1 + ε) * η ^ 3) := by
  classical
  obtain ⟨K, hK, hbound⟩ := exists_sum_near_pairOrbitParameterArea_le hε
  refine ⟨K, hK, ?_⟩
  intro d hd hns η hη0 hη
  exact (Finset.sum_le_sum (fun ℓ _ => packetPairImageMass_le_parameterArea hd hns ℓ η)).trans
    (hbound d hd η hη0 hη)

end Erdos1148.DukeArithmetic
