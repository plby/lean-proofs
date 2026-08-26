import ErdosProblems.Erdos1148.ReducedForms
import ErdosProblems.Erdos1148.IntrinsicOrbitMeasure

/-!
# The finite discriminant packet measure

We include all integral forms, since the fixed-ball existence reduction
does not require primitivity. The finite packet is a sum of intrinsic
closed-orbit length measures, and its normalization is a probability
measure whenever an integral form exists.
-/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

noncomputable def packetOrbit {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (q : IntegralFormOrbits d) : ClosedFlowOrbit :=
  Classical.choose (exists_closedFlowOrbit_of_integral_form hd hns q.out.2)

lemma packetOrbit_form {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) (q : IntegralFormOrbits d) :
    Real.sqrt (d : ℝ) • formAction (packetOrbit hd hns q).lift (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) q.out.1 :=
  Classical.choose_spec (exists_closedFlowOrbit_of_integral_form hd hns q.out.2)

noncomputable def discriminantPacket {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    Measure ModularOrbitSpace :=
  Measure.sum (fun q : IntegralFormOrbits d => (packetOrbit hd hns q).measure)

instance discriminantPacket_isFinite {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    IsFiniteMeasure (discriminantPacket hd hns) := by
  let := finite_integralFormOrbits hd hns
  unfold discriminantPacket
  infer_instance

lemma discriminantPacket_univ {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    discriminantPacket hd hns Set.univ =
      ∑' q : IntegralFormOrbits d, ENNReal.ofReal (packetOrbit hd hns q).period := by
  simp [discriminantPacket, Measure.sum_apply, ClosedFlowOrbit.measure_univ]

lemma discriminantPacket_univ_pos {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (base : IntegralDiscrForm d) : 0 < discriminantPacket hd hns Set.univ := by
  let q := integralFormOrbitMk base
  have hpos : 0 < (packetOrbit hd hns q).measure Set.univ := by
    rw [ClosedFlowOrbit.measure_univ]
    exact ENNReal.ofReal_pos.mpr (packetOrbit hd hns q).period_pos
  exact hpos.trans_le (Measure.le_sum (fun q : IntegralFormOrbits d =>
    (packetOrbit hd hns q).measure) q Set.univ)

theorem discriminantPacket_flow_invariant {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) (s : ℝ) :
    Measure.map (modularRightTranslate (diagonalFlow s)) (discriminantPacket hd hns) =
      discriminantPacket hd hns := by
  have hm := (continuous_modularRightTranslate (diagonalFlow s)).measurable
  rw [discriminantPacket, Measure.map_sum hm.aemeasurable]
  congr 1
  funext q
  exact (packetOrbit hd hns q).measure_flow_invariant s

noncomputable def normalizedDiscriminantPacket {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    Measure ModularOrbitSpace :=
  (discriminantPacket hd hns Set.univ)⁻¹ • discriminantPacket hd hns

theorem normalizedDiscriminantPacket_isProbability {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (base : IntegralDiscrForm d) : IsProbabilityMeasure (normalizedDiscriminantPacket hd hns) := by
  let : NeZero (discriminantPacket hd hns) := ⟨by
    intro hzero
    have hpos := discriminantPacket_univ_pos hd hns base
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos⟩
  unfold normalizedDiscriminantPacket
  infer_instance

theorem normalizedDiscriminantPacket_flow_invariant {d : ℤ}
    (hd : 0 < d) (hns : ¬IsSquare d) (s : ℝ) :
    Measure.map (modularRightTranslate (diagonalFlow s)) (normalizedDiscriminantPacket hd hns) =
      normalizedDiscriminantPacket hd hns := by
  rw [normalizedDiscriminantPacket, Measure.map_smul, discriminantPacket_flow_invariant]

end Erdos1148.DukeArithmetic
