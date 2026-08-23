/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterGrid
import ErdosProblems.Erdos721.HunterLattice

/-!
# Finite phase nets for Hunter centers

For each rational frequency space we use its saturated integral basis and a
nonsingular coordinate minor.  A finite grid in the corresponding coordinate
torus indexes positive-volume target sets.  Hitting every grid target gives,
for every point of the ambient torus, a small Euclidean correction which
annihilates every integral character in the frequency space exactly.
-/

namespace Erdos721.HunterPhaseNet

open Function MeasureTheory Set
open scoped ENNReal MeasureTheory Pointwise Topology

open HunterTorus HunterPhase HunterGrid HunterLattice

lemma latticeBasis_rationalMatrix_linearIndependent {D : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) :
    LinearIndependent ℚ (rationalMatrix (latticeBasis V)).row := by
  change LinearIndependent ℚ
    (fun i j ↦ (latticeBasis V i j : ℚ))
  exact latticeBasis_linearIndependent V

/-- A chosen nonsingular coordinate minor of the saturated lattice basis. -/
noncomputable def latticeMinor {D : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) :
    Fin (latticeRank V) ↪ Fin D :=
  Classical.choose (exists_nonsingular_coordinate_minor
    (latticeBasis V) (latticeBasis_rationalMatrix_linearIndependent V))

lemma latticeMinor_det_ne_zero {D : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) :
    Matrix.det ((fun a b ↦ latticeBasis V a (latticeMinor V b)) :
      Matrix (Fin (latticeRank V)) (Fin (latticeRank V)) ℤ) ≠ 0 :=
  Classical.choose_spec (exists_nonsingular_coordinate_minor
    (latticeBasis V) (latticeBasis_rationalMatrix_linearIndependent V))

/-- Ambient point whose lattice-basis phases are the image of a grid point
under the chosen nonsingular minor. -/
noncomputable def phaseGridCenter {D Q : ℕ}
    (V : Submodule ℚ (Fin D → ℚ))
    (a : Fin (latticeRank V) → Fin Q) : Torus D :=
  coordinateEmbed (latticeMinor V) (gridPoint a)

@[simp] lemma phaseHom_phaseGridCenter {D Q : ℕ}
    (V : Submodule ℚ (Fin D → ℚ))
    (a : Fin (latticeRank V) → Fin Q) :
    phaseHom (latticeBasis V) (phaseGridCenter V a) =
      phaseHom (fun i j ↦ latticeBasis V i (latticeMinor V j))
        (gridPoint a) := by
  exact phaseHom_coordinateEmbed _ _ _

/-- Positive-volume target associated to one point of the finite phase net. -/
noncomputable def phaseNetTarget {D Q : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) (r : ℝ)
    (a : Fin (latticeRank V) → Fin Q) : Set (Torus D) :=
  goodCenterSet (latticeBasis V) (latticeMinor V) r
    (phaseGridCenter V a)

lemma measurableSet_phaseNetTarget {D Q : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) (r : ℝ)
    (a : Fin (latticeRank V) → Fin Q) :
    MeasurableSet (phaseNetTarget V r a) := by
  apply MeasurableSet.preimage
  · exact (goodCenterTarget_compact (latticeBasis V) (latticeMinor V) r
      (phaseGridCenter V a)).measurableSet
  · exact (continuous_phaseHom (latticeBasis V)).measurable

/-- Every phase-net target has the same uniform Haar-volume lower bound. -/
lemma volume_phaseNetTarget {D Q : ℕ}
    (V : Submodule ℚ (Fin D → ℚ)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : 2 * r ≤ 1)
    (a : Fin (latticeRank V) → Fin Q) :
    ENNReal.ofReal (2 * r) ^ latticeRank V ≤
      volume (phaseNetTarget V r a) := by
  exact volume_goodCenterSet (latticeBasis V)
    (latticeBasis_rationalMatrix_linearIndependent V)
    (latticeMinor V) (latticeMinor_det_ne_zero V) hr0 hr
    (phaseGridCenter V a)

/-- Hitting every grid target for `V` gives an exact small correction for an
arbitrary target point. -/
theorem exists_small_correction_of_hits_phaseNet
    {D Q : ℕ} (V : Submodule ℚ (Fin D → ℚ))
    {r : ℝ} (hr0 : 0 ≤ r) (hQ : 2 ≤ Q)
    (hmesh : (Q : ℝ)⁻¹ ≤ r)
    (centers : Set (Torus D))
    (hhit : ∀ a : Fin (latticeRank V) → Fin Q,
      ∃ x ∈ centers, x ∈ phaseNetTarget V r a)
    (xStar : Torus D) :
    ∃ x ∈ centers, ∃ u : EuclideanSpace ℝ (Fin D),
      ‖u‖ ≤ 2 * Real.sqrt (latticeRank V) * r ∧
        ∀ η : Fin D → ℤ, castIntVector η ∈ V →
          integerDot η (x + project u - xStar) = 0 := by
  let A : Matrix (Fin (latticeRank V)) (Fin (latticeRank V)) ℤ :=
    fun i j ↦ latticeBasis V i (latticeMinor V j)
  obtain ⟨z, hz⟩ := phaseHom_surjective_of_det_ne_zero A
    (latticeMinor_det_ne_zero V) (phaseHom (latticeBasis V) xStar)
  obtain ⟨a, ha⟩ := exists_gridPoint_norm_sub_le hQ z
  obtain ⟨x, hxcenters, hxgood⟩ := hhit a
  obtain ⟨u₁, hu₁norm, hu₁phase⟩ :=
    exists_small_phase_correction_of_mem_goodCenterSet
      (latticeBasis V) (latticeMinor V) hr0
      (phaseGridCenter V a) x hxgood
  let dz : Torus (latticeRank V) := z - gridPoint a
  have hdz : dz ∈ centeredBox (latticeRank V) r := by
    intro i hi
    have hai := ha i
    rw [norm_sub_rev] at hai
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖(z - gridPoint a) i‖ ≤ r
    simpa only [Pi.sub_apply] using hai.trans hmesh
  let u₂ : EuclideanSpace ℝ (Fin D) :=
    coordinateLift (latticeMinor V) dz
  have hu₂norm : ‖u₂‖ ≤ Real.sqrt (latticeRank V) * r := by
    exact coordinateLift_norm_le (latticeMinor V) hr0 hdz
  have hphase₂ :
      phaseHom (latticeBasis V) (project u₂) =
        phaseHom (latticeBasis V) xStar -
          phaseHom (latticeBasis V) (phaseGridCenter V a) := by
    rw [show project u₂ = coordinateEmbed (latticeMinor V) dz by
      simp [u₂], phaseHom_coordinateEmbed]
    change phaseHom A dz = _
    rw [map_sub, hz]
    simp only [dz, phaseHom_phaseGridCenter, A]
  refine ⟨x, hxcenters, u₁ + u₂, ?_, ?_⟩
  · calc
      ‖u₁ + u₂‖ ≤ ‖u₁‖ + ‖u₂‖ := norm_add_le _ _
      _ ≤ Real.sqrt (latticeRank V) * r +
          Real.sqrt (latticeRank V) * r := add_le_add hu₁norm hu₂norm
      _ = 2 * Real.sqrt (latticeRank V) * r := by ring
  · intro η hη
    refine integerDot_eq_zero_of_latticeBasis V
      (x + project (u₁ + u₂) - xStar) ?_ hη
    rw [project_add]
    simp only [map_sub, map_add]
    rw [hphase₂]
    have hzero := hu₁phase
    simp only [map_sub, map_add] at hzero
    simpa [sub_eq_add_neg, add_assoc] using hzero

end Erdos721.HunterPhaseNet
