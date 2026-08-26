import ErdosProblems.Erdos1148.PacketFullSupport
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Every fixed nonempty open set meets all sufficiently large packets -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

theorem normalizedPacket_eventually_open_pos {U : Set ModularOrbitSpace}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∀ (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ))
      (_base : IntegralDiscrForm (d : ℤ)), 0 < normalizedDiscriminantPacket hd hns U := by
  classical
  by_contra hnot
  push_neg at hnot
  choose d hlarge hd hns base hzero using hnot
  have hdisc : Tendsto d atTop atTop := tendsto_atTop_mono hlarge tendsto_id
  obtain ⟨ν, φ, _, hweak, hsupport⟩ := normalizedPacket_exists_full_support_limit hd hns base hdisc
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU
  have hnull (i : ℕ) : ((normalizedPacketProbability (hd (φ i)) (hns (φ i)) (base (φ i))) :
      Measure ModularOrbitSpace) U = 0 := le_antisymm (hzero (φ i)) zero_le
  simp only [hnull, liminf_const] at hlim
  exact (not_lt_of_ge hlim) (hsupport U hU hne)

end Erdos1148.DukeArithmetic
