import ErdosProblems.Erdos1148.PacketTightness
import ErdosProblems.Erdos1148.SequentialTightness
import ErdosProblems.Erdos1148.ModularTopology

/-! # Weakly convergent probability subsequences of discriminant packets -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

noncomputable def normalizedPacketProbability {d : ℤ}
    (hd : 0 < d) (hns : ¬IsSquare d) (base : IntegralDiscrForm d) :
    ProbabilityMeasure ModularOrbitSpace :=
  ⟨normalizedDiscriminantPacket hd hns,
    normalizedDiscriminantPacket_isProbability hd hns base⟩

theorem normalizedPacket_has_compact_full_measure {d : ℤ}
    (hd : 0 < d) (hns : ¬IsSquare d) :
    ∃ K : Set ModularOrbitSpace, IsCompact K ∧
      normalizedDiscriminantPacket hd hns Kᶜ = 0 := by
  let H : ℝ := (d : ℝ) ^ (1 / 4 : ℝ)
  have hH : 0 < H := Real.rpow_pos_of_pos (by exact_mod_cast hd) _
  refine ⟨modularCompactCore H, isCompact_modularCompactCore H, ?_⟩
  apply measure_mono_null _ (normalizedDiscriminantPacket_cusp_fourth_root hd hns)
  intro x hx
  by_contra hnot
  exact hx (modularCusp_compl_subset_compactCore hH hnot)

theorem normalizedPacket_sequence_isTight {d : ℕ → ℕ}
    (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hlim : Tendsto d atTop atTop) :
    IsTightMeasureSet (Set.range (fun i => normalizedDiscriminantPacket (hd i) (hns i))) := by
  let μ := fun i => normalizedDiscriminantPacket (hd i) (hns i)
  letI (i : ℕ) : IsProbabilityMeasure (μ i) :=
    normalizedDiscriminantPacket_isProbability (hd i) (hns i) (base i)
  exact isTightMeasureSet_range_of_eventually_tight μ
    (fun i => normalizedPacket_has_compact_full_measure (hd i) (hns i))
    (fun _ hδ => normalizedPacket_eventually_tight hd hns base hlim hδ)

theorem normalizedPacket_sequence_compact_closure {d : ℕ → ℕ}
    (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hlim : Tendsto d atTop atTop) :
    IsCompact (closure (Set.range (fun i =>
      normalizedPacketProbability (hd i) (hns i) (base i)))) := by
  apply isCompact_closure_of_isTightMeasureSet
  have heq : {((ν : ProbabilityMeasure ModularOrbitSpace) : Measure ModularOrbitSpace) |
      ν ∈ Set.range (fun i => normalizedPacketProbability (hd i) (hns i) (base i))} =
      Set.range (fun i => normalizedDiscriminantPacket (hd i) (hns i)) := by
    ext μ
    constructor
    · rintro ⟨ν, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨normalizedPacketProbability (hd i) (hns i) (base i), ⟨i, rfl⟩, rfl⟩
  rw [heq]
  exact normalizedPacket_sequence_isTight hd hns base hlim

theorem normalizedPacket_exists_weakly_convergent_subsequence {d : ℕ → ℕ}
    (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hlim : Tendsto d atTop atTop) :
    ∃ (ν : ProbabilityMeasure ModularOrbitSpace) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun i => normalizedPacketProbability (hd (φ i)) (hns (φ i)) (base (φ i)))
        atTop (𝓝 ν) := by
  have hcompact := normalizedPacket_sequence_compact_closure hd hns base hlim
  obtain ⟨ν, _, φ, hφ, hconv⟩ :=
    hcompact.tendsto_subseq (fun i => subset_closure (Set.mem_range_self i))
  exact ⟨ν, φ, hφ, hconv⟩

end Erdos1148.DukeArithmetic
