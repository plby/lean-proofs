import ErdosProblems.Erdos1148.NearbyGaussParameters

/-! # Compact measurable thickenings of arbitrary coherent pieces -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem LiftForwardClose.exists_compact_superset {η S : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftForwardClose η S E) (hηpos : 0 ≤ η) (hη : η ≤ 1 / 2) (hS : 0 ≤ S) :
    ∃ B : Set SL(2, ℝ), E ⊆ B ∧ IsCompact B ∧ LiftForwardClose (32 * η) S B := by
  by_cases hne : E.Nonempty
  · obtain ⟨g₀, hg₀⟩ := hne
    let B := gaussLiftBox g₀ (-(2 * η * Real.exp (-S))) (-(2 * η)) (1 - η)
      ((4 * η) * Real.exp (-S)) (4 * η) (4 * η)
    refine ⟨B, ?_, isCompact_gaussLiftBox _ _ _ _ _ _ _, ?_⟩
    · intro g hg
      have hflow : ∀ t ∈ Set.Icc 0 S,
          EntryCloseOne η (diagonalFlow (-t) * (g₀⁻¹ * g) * diagonalFlow t) := by
        intro t ht
        have heq : diagonalFlow (-t) * (g₀⁻¹ * g) * diagonalFlow t =
            (g₀ * diagonalFlow t)⁻¹ * (g * diagonalFlow t) := by
          rw [diagonalFlow_neg]
          group
        rw [heq]
        exact hE g₀ hg₀ g hg t ht
      have htube := (entryForwardBowenTube_iff_flow_closeness hS (g₀⁻¹ * g)).mpr hflow
      obtain ⟨p, hp, hr, hx, hh⟩ :=
        exists_boundedGaussParameters_of_forward_tube hη g₀ g htube
      refine ⟨p, ?_, hp⟩
      have hr' := abs_le.mp hr
      have hx' := abs_le.mp hx
      have hh' := abs_le.mp hh
      change p.val.1 ∈ Set.Icc _ _ ∧ p.val.2.1 ∈ Set.Icc _ _ ∧ p.val.2.2 ∈ Set.Icc _ _
      constructor
      · constructor <;> nlinarith [hr'.1, hr'.2]
      constructor
      · constructor <;> linarith [hx'.1, hx'.2]
      · constructor <;> linarith [hh'.1, hh'.2]
    · have hclose := gaussLiftBox_forward_close g₀ (-(2 * η * Real.exp (-S)))
        (-(2 * η)) (1 - η) (show 0 ≤ 4 * η by positivity) hS
      have hscale : 8 * (4 * η) = 32 * η := by ring
      simpa only [hscale] using hclose
  · refine ⟨∅, ?_, isCompact_empty, ?_⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    · intro g hg
      exact False.elim hg

theorem LiftForwardClose.exists_measurable_modular_superset {η S : ℝ} {E : Set SL(2, ℝ)}
    (hE : LiftForwardClose η S E) (hηpos : 0 ≤ η) (hη : η ≤ 1 / 2) (hS : 0 ≤ S) :
    ∃ B : Set ModularOrbitSpace, modularMk '' E ⊆ B ∧ IsCompact B ∧
      MeasurableSet B ∧ B ×ˢ B ⊆ modularForwardBowenPairs (32 * η) S := by
  obtain ⟨B, hEB, hB, hclose⟩ := hE.exists_compact_superset hηpos hη hS
  have hcompact := hB.image continuous_modularMk
  exact ⟨modularMk '' B, Set.image_mono hEB, hcompact, hcompact.measurableSet,
    hclose.modular_image hS⟩

end Erdos1148.DukeArithmetic
