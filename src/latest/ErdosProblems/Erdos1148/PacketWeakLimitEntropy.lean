import ErdosProblems.Erdos1148.PacketOrbitEntropyRate
import ErdosProblems.Erdos1148.OrbitEntropyWeakLimit
import ErdosProblems.Erdos1148.WeakLimitInvariance
import ErdosProblems.Erdos1148.EntropyRateParameters

/-! # Packet probability limits have finite-partition entropy rate at least one -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

theorem normalizedPacket_weak_limit_entropy_lower {ι : Type*} {l : Filter ι} [l.NeBot]
    {d : ι → ℕ} (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hdisc : Tendsto d l atTop)
    {ν : ProbabilityMeasure ModularOrbitSpace}
    (hweak : Tendsto (fun i => normalizedPacketProbability (hd i) (hns i) (base i)) l (𝓝 ν))
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ P : FineModularPartition, (∀ j, (ν : Measure ModularOrbitSpace)
        (frontier (P.partition.atom j)) = 0) ∧
      ∀ k : ℕ, 0 < k → 1 - ε ≤ P.partition.orbitEntropy
        (ν : Measure ModularOrbitSpace) modularTimeOne k / k := by
  obtain ⟨σ, κ, m₀, δ, hσ, hσhalf, hκ, hm₀, hδ, hm₀eq, hq, hrate⟩ :=
    exists_entropy_rate_parameters hε hεone (Real.log_nonneg exceptionalStepCoverCost_one_le)
  obtain ⟨K, hK, hsmall⟩ := normalizedPacket_eventually_tight hd hns base hdisc hδ
  obtain ⟨P, hbadsub, hboundary⟩ := exists_fine_modular_partition (ν : Measure ModularOrbitSpace) hK
  have hbad : ∀ᶠ i in l, m₀ ≤ 1 - (1 + κ⁻¹) *
      (normalizedDiscriminantPacket (hd i) (hns i)).real (P.partition.atom none) := by
    filter_upwards [hsmall] with i hi
    let μ := normalizedDiscriminantPacket (hd i) (hns i)
    letI : IsProbabilityMeasure μ := normalizedDiscriminantPacket_isProbability (hd i) (hns i) (base i)
    have hmass : μ.real (P.partition.atom none) ≤ δ := (measureReal_mono hbadsub).trans hi.le
    have hscaled := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 1 + κ⁻¹)
    rw [hm₀eq]
    linarith
  have hlong := packet_orbit_entropy_eventually_rate_lower hd hns base hdisc P
    hσ hσhalf hκ hm₀ hq hbad hrate
  have hN : Tendsto (fun i => packetObservationTime (d i : ℝ)) l atTop :=
    packetObservationTime_tendsto.comp (tendsto_natCast_atTop_atTop.comp hdisc)
  have hN' : Tendsto (fun i => packetObservationTime (d i : ℝ) + 1) l atTop :=
    tendsto_atTop_mono (fun i => by omega) hN
  have hνinv : Measure.map modularTimeOne (ν : Measure ModularOrbitSpace) = ν :=
    normalizedPacket_weak_limit_flow_invariant hd hns base hweak 1
  have hμinv (i : ι) : Measure.map modularTimeOne
      ((normalizedPacketProbability (hd i) (hns i) (base i) : ProbabilityMeasure ModularOrbitSpace) :
        Measure ModularOrbitSpace) = normalizedPacketProbability (hd i) (hns i) (base i) :=
    normalizedDiscriminantPacket_flow_invariant (hd i) (hns i) 1
  refine ⟨P, hboundary, ?_⟩
  intro k hk
  apply P.partition.orbitEntropy_fixed_block_lower_of_long_blocks hweak continuous_modularTimeOne
    hμinv hνinv hboundary (fun i => packetObservationTime (d i : ℝ) + 1) hN' _ hk
  have hμeq (i : ι) : ((normalizedPacketProbability (hd i) (hns i) (base i) :
      ProbabilityMeasure ModularOrbitSpace) : Measure ModularOrbitSpace) =
      normalizedDiscriminantPacket (hd i) (hns i) := rfl
  simpa only [hμeq, Nat.cast_add, Nat.cast_one] using hlong

end Erdos1148.DukeArithmetic
