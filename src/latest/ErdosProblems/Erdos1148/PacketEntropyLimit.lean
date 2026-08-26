import ErdosProblems.Erdos1148.PacketWeakLimitEntropy

/-! # Every divergent packet sequence has an invariant probability limit of full entropy -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

theorem normalizedPacket_exists_invariant_entropy_limit {d : ℕ → ℕ}
    (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hdisc : Tendsto d atTop atTop) :
    ∃ (ν : ProbabilityMeasure ModularOrbitSpace) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun i => normalizedPacketProbability (hd (φ i)) (hns (φ i)) (base (φ i)))
        atTop (𝓝 ν) ∧
      (∀ t : ℝ, Measure.map (modularRightTranslate (diagonalFlow t))
        (ν : Measure ModularOrbitSpace) = ν) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ P : FineModularPartition,
        (∀ j, (ν : Measure ModularOrbitSpace) (frontier (P.partition.atom j)) = 0) ∧
        ∀ k : ℕ, 0 < k → 1 - ε ≤ P.partition.orbitEntropy
          (ν : Measure ModularOrbitSpace) modularTimeOne k / k := by
  obtain ⟨ν, φ, hφ, hconv, hinv⟩ := normalizedPacket_exists_invariant_weak_limit hd hns base hdisc
  refine ⟨ν, φ, hφ, hconv, hinv, ?_⟩
  intro ε hε hεone
  exact normalizedPacket_weak_limit_entropy_lower (fun i => hd (φ i))
    (fun i => hns (φ i)) (fun i => base (φ i)) (hdisc.comp hφ.tendsto_atTop) hconv hε hεone

end Erdos1148.DukeArithmetic
