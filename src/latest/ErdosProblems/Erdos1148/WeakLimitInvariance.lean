import ErdosProblems.Erdos1148.PacketWeakCompactness

/-! # Flow invariance survives weak limits of packet probability measures -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

theorem probability_weak_limit_invariant {X ι : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T2Space (ProbabilityMeasure X)]
    {l : Filter ι} [l.NeBot] {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hlim : Tendsto μ l (𝓝 ν)) {f : X → X} (hf : Continuous f)
    (hinv : ∀ i, Measure.map f (μ i : Measure X) = μ i) :
    Measure.map f (ν : Measure X) = ν := by
  have heq (i : ι) : (μ i).map hf.measurable.aemeasurable = μ i :=
    Subtype.ext (hinv i)
  have hmap := (ProbabilityMeasure.continuous_map hf).tendsto ν |>.comp hlim
  have hlim' : Tendsto (fun i => (μ i).map hf.measurable.aemeasurable) l (𝓝 ν) := by
    simpa only [heq] using hlim
  have hsame := tendsto_nhds_unique hmap hlim'
  exact congrArg (fun ξ : ProbabilityMeasure X => (ξ : Measure X)) hsame

theorem normalizedPacket_weak_limit_flow_invariant {ι : Type*} {l : Filter ι} [l.NeBot]
    {d : ι → ℤ} (hd : ∀ i, 0 < d i) (hns : ∀ i, ¬IsSquare (d i))
    (base : ∀ i, IntegralDiscrForm (d i)) {ν : ProbabilityMeasure ModularOrbitSpace}
    (hlim : Tendsto (fun i => normalizedPacketProbability (hd i) (hns i) (base i)) l (𝓝 ν))
    (t : ℝ) : Measure.map (modularRightTranslate (diagonalFlow t))
      (ν : Measure ModularOrbitSpace) = ν := by
  exact probability_weak_limit_invariant hlim (continuous_modularRightTranslate _)
    (fun i => normalizedDiscriminantPacket_flow_invariant (hd i) (hns i) t)

theorem normalizedPacket_exists_invariant_weak_limit {d : ℕ → ℕ}
    (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hlim : Tendsto d atTop atTop) :
    ∃ (ν : ProbabilityMeasure ModularOrbitSpace) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun i => normalizedPacketProbability (hd (φ i)) (hns (φ i)) (base (φ i)))
        atTop (𝓝 ν) ∧
      ∀ t : ℝ, Measure.map (modularRightTranslate (diagonalFlow t))
        (ν : Measure ModularOrbitSpace) = ν := by
  obtain ⟨ν, φ, hφ, hconv⟩ :=
    normalizedPacket_exists_weakly_convergent_subsequence hd hns base hlim
  exact ⟨ν, φ, hφ, hconv, normalizedPacket_weak_limit_flow_invariant
    (fun i => hd (φ i)) (fun i => hns (φ i)) (fun i => base (φ i)) hconv⟩

end Erdos1148.DukeArithmetic
