import ErdosProblems.Erdos1148.AvoidanceEntropyGap
import ErdosProblems.Erdos1148.PacketEntropyLimit

/-! # Full support of packet probability limits, without Duke's theorem -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

theorem open_measure_pos_of_partition_entropy
    (μ : Measure ModularOrbitSpace) [IsProbabilityMeasure μ]
    (hf : MeasurePreserving modularTimeOne μ μ)
    (hentropy : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ P : FineModularPartition,
      (∀ j, μ (frontier (P.partition.atom j)) = 0) ∧
      ∀ k : ℕ, 0 < k → 1 - ε ≤ P.partition.orbitEntropy μ modularTimeOne k / k)
    {U : Set ModularOrbitSpace} (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U := by
  by_contra hpos
  have hnull : μ U = 0 := le_antisymm (le_of_not_gt hpos) zero_le
  obtain ⟨γ, hγ, hγ1, hgap⟩ := exists_uniform_continuity_partition_entropy_gap μ hf hU hne hnull
  obtain ⟨P, hboundary, hlower⟩ := hentropy (γ / 2) (by positivity) (by linarith only [hγ1])
  obtain ⟨L, hL, hupper⟩ := hgap (Option (Fin P.size)) P.partition hboundary
  have hlow := hlower L hL
  linarith only [hlow, hupper, hγ]

theorem normalizedPacket_weak_limit_open_pos {ι : Type*} {l : Filter ι} [l.NeBot]
    {d : ι → ℕ} (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hdisc : Tendsto d l atTop)
    {ν : ProbabilityMeasure ModularOrbitSpace}
    (hweak : Tendsto (fun i => normalizedPacketProbability (hd i) (hns i) (base i)) l (𝓝 ν))
    {U : Set ModularOrbitSpace} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (ν : Measure ModularOrbitSpace) U := by
  apply open_measure_pos_of_partition_entropy (ν : Measure ModularOrbitSpace)
    ⟨continuous_modularTimeOne.measurable,
      normalizedPacket_weak_limit_flow_invariant hd hns base hweak 1⟩ _ hU hne
  intro ε hε hε1
  exact normalizedPacket_weak_limit_entropy_lower hd hns base hdisc hweak hε hε1

theorem normalizedPacket_exists_full_support_limit {d : ℕ → ℕ}
    (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hdisc : Tendsto d atTop atTop) :
    ∃ (ν : ProbabilityMeasure ModularOrbitSpace) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun i => normalizedPacketProbability (hd (φ i)) (hns (φ i)) (base (φ i)))
        atTop (𝓝 ν) ∧
      ∀ U : Set ModularOrbitSpace, IsOpen U → U.Nonempty →
        0 < (ν : Measure ModularOrbitSpace) U := by
  obtain ⟨ν, φ, hφ, hweak⟩ := normalizedPacket_exists_weakly_convergent_subsequence hd hns base hdisc
  refine ⟨ν, φ, hφ, hweak, ?_⟩
  intro U hU hne
  exact normalizedPacket_weak_limit_open_pos (fun i => hd (φ i)) (fun i => hns (φ i))
    (fun i => base (φ i)) (hdisc.comp hφ.tendsto_atTop) hweak hU hne

end Erdos1148.DukeArithmetic
