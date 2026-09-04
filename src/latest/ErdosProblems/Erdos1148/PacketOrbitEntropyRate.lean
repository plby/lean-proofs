import ErdosProblems.Erdos1148.PacketCriticalPairScale
import ErdosProblems.Erdos1148.GoodOrbitMass
import ErdosProblems.Erdos1148.EntropyRateAlgebra

/-! # Unconditional long-block packet entropy estimates -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter

theorem exists_packet_orbit_entropy_linear_bound {σ : ℝ} (hσpos : 0 < σ) (hσ : σ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ))
      (base : IntegralDiscrForm d) (P : FineModularPartition) (κ m₀ : ℝ),
      0 < κ → 0 < m₀ → 0 ≤ 1 - 2 * σ - κ * Real.log exceptionalStepCoverCost →
      m₀ ≤ 1 - (1 + κ⁻¹) * (normalizedDiscriminantPacket hd hns).real (P.partition.atom none) →
      m₀ * (1 - 2 * σ - κ * Real.log exceptionalStepCoverCost) *
          (packetObservationTime (d : ℝ) : ℝ) -
        (κ * Real.log exceptionalStepCoverCost + |Real.log C| - Real.log m₀) ≤
        P.partition.orbitEntropy (normalizedDiscriminantPacket hd hns) modularTimeOne
          (packetObservationTime (d : ℝ) + 1) := by
  obtain ⟨C, hC, hpair⟩ := exists_unconditional_packet_critical_forward_pair_bound hσpos hσ
  refine ⟨C, hC, ?_⟩
  intro d hd hns base P κ m₀ hκ hm₀ hq hbad
  let μ := normalizedDiscriminantPacket hd hns
  let : IsProbabilityMeasure μ := normalizedDiscriminantPacket_isProbability hd hns base
  let n := packetObservationTime (d : ℝ)
  let m := μ.real (goodOrbitSet P κ n)
  have hmm₀ : m₀ ≤ m := hbad.trans (goodOrbitSet_mass_lower P μ
    (normalizedDiscriminantPacket_flow_invariant hd hns) hκ n)
  have hmpos : 0 < m := hm₀.trans_le hmm₀
  have hmone : m ≤ 1 := measureReal_le_one
  have hbound := hpair d hd hns base (32 * P.radius) (mul_pos (by norm_num) P.radius_pos)
    (by linarith [P.radius_le])
  have hentropy := P.orbitEntropy_lower_of_pair_bound μ κ hbound hmpos
    (sum_goodOrbitWord_mass P μ κ n)
  have hnumeric := collision_entropy_linear_lower hm₀ hmm₀ hmone hC hκ.le
    (Real.log_nonneg exceptionalStepCoverCost_one_le) (Nat.cast_nonneg n) hq
  exact hnumeric.trans hentropy

theorem packet_orbit_entropy_eventually_rate_lower {ι : Type*} {l : Filter ι} {d : ι → ℕ}
    (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hdisc : Tendsto d l atTop)
    (P : FineModularPartition) {σ κ m₀ a : ℝ} (hσpos : 0 < σ) (hσ : σ ≤ 1 / 2)
    (hκ : 0 < κ) (hm₀ : 0 < m₀) (hq : 0 ≤ 1 - 2 * σ - κ * Real.log exceptionalStepCoverCost)
    (hbad : ∀ᶠ i in l, m₀ ≤ 1 - (1 + κ⁻¹) *
      (normalizedDiscriminantPacket (hd i) (hns i)).real (P.partition.atom none))
    (ha : a < m₀ * (1 - 2 * σ - κ * Real.log exceptionalStepCoverCost)) :
    ∀ᶠ i in l, a ≤ P.partition.orbitEntropy
      (normalizedDiscriminantPacket (hd i) (hns i)) modularTimeOne
      (packetObservationTime (d i : ℝ) + 1) / ((packetObservationTime (d i : ℝ) : ℝ) + 1) := by
  obtain ⟨C, _, hlinear⟩ := exists_packet_orbit_entropy_linear_bound hσpos hσ
  have hN := packetObservationTime_tendsto.comp (tendsto_natCast_atTop_atTop.comp hdisc)
  apply eventual_entropy_rate_lower_of_linear_bound hN
    (a := m₀ * (1 - 2 * σ - κ * Real.log exceptionalStepCoverCost))
    (b := κ * Real.log exceptionalStepCoverCost + |Real.log C| - Real.log m₀) _ ha
  filter_upwards [hbad] with i hi
  exact hlinear (d i) (hd i) (hns i) (base i) P κ m₀ hκ hm₀ hq hi

end Erdos1148.DukeArithmetic
