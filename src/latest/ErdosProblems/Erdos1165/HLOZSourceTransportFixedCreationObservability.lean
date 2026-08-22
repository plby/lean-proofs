/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZPrefixedCanonicalSourceProp49Observability
import ErdosProblems.Erdos1165.HLOZSourceEndpointTransportTable
import ErdosProblems.Erdos1165.HLOZSourceTransportCoordinateMass

/-!
# Fixed-creation observability under source reflection

The opposite endpoint row for a column tiling is obtained by reflecting every
increment in the vertical axis.  Reflection acts coordinatewise and therefore
preserves each deterministic increment filtration.  Consequently a canonical
stopped-past event observable at a fixed creation clock remains observable
after taking its literal reflected preimage.

Checker recentering is deliberately absent: deleting the physical first step
changes the clock and is handled by the fixed-prefix stopped construction.
-/

open MeasureTheory Set

namespace Erdos1165.HLOZSourceTransportFixedCreationObservability

noncomputable section

/-- Coordinatewise reflection of a finite increment prefix. -/
def horizontalReflectPrefix {n : ℕ} (v : Fin n → Direction) :
    Fin n → Direction :=
  fun i ↦ horizontalReflectDirection (v i)

theorem measurable_horizontalReflectPrefix (n : ℕ) :
    Measurable (@horizontalReflectPrefix n) :=
  measurable_of_countable _

@[simp] theorem stepPrefix_horizontalReflectSteps (n : ℕ)
    (ω : StepPath) :
    stepPrefix n (horizontalReflectSteps ω) =
      horizontalReflectPrefix (stepPrefix n ω) :=
  rfl

/-- Vertical reflection preserves observability at a deterministic stopping
time.  The proof works inside the finite increment filtration, rather than
using only ambient Borel measurability. -/
theorem isMeasurableAtStopping_const_preimage_horizontalReflectSteps
    {A : Set StepPath} {n : ℕ}
    (hA : IsMeasurableAtStopping (fun _ : StepPath ↦ n) A) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (horizontalReflectSteps ⁻¹' A) := by
  apply HLOZGapFixedPair.isMeasurableAtStopping_const_of_measurableSet
  have hn := hA n
  have heq : A ∩ {ω : StepPath | n = n} = A := by
    ext ω
    simp
  rw [heq, incrementFiltration_apply] at hn
  rw [incrementFiltration_apply]
  obtain ⟨S, hS, hAeq⟩ := hn
  refine ⟨@horizontalReflectPrefix n ⁻¹' S,
    hS.preimage (measurable_horizontalReflectPrefix n), ?_⟩
  rw [← hAeq]
  ext ω
  simp only [Set.mem_preimage]
  rfl

/-- Walk-path form of the reflected fixed-clock observability theorem. -/
theorem isMeasurableAtStopping_const_trajectory_reflection
    {A : Set WalkPath} {n : ℕ}
    (hA : IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (trajectory ⁻¹' A)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (trajectory ⁻¹' (horizontalReflectPath ⁻¹' A)) := by
  have hreflect :=
    isMeasurableAtStopping_const_preimage_horizontalReflectSteps hA
  have heq :
      horizontalReflectSteps ⁻¹' (trajectory ⁻¹' A) =
        trajectory ⁻¹' (horizontalReflectPath ⁻¹' A) := by
    ext ω
    simp only [Set.mem_preimage]
    rw [← horizontalReflectPath_trajectory]
  rw [← heq]
  exact hreflect

/-- The source-table form for an opposite column row. -/
theorem isMeasurableAtStopping_const_sourceTransportPreimage_column
    (t : Tilings.Tiling) (ht : t = .evenColumns ∨ t = .oddColumns)
    {A : Set WalkPath} {n : ℕ}
    (hA : IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (trajectory ⁻¹' A)) :
    IsMeasurableAtStopping (fun _ : StepPath ↦ n)
      (trajectory ⁻¹'
        (HLOZSourceTransportCoordinateMass.sourceTransportPreimage
          t .opposite A)) := by
  rcases ht with rfl | rfl <;>
    simpa only [HLOZSourceTransportCoordinateMass.sourceTransportPreimage,
      HLOZSourceEndpointTransportTable.sourceTransportPath] using
      isMeasurableAtStopping_const_trajectory_reflection hA

end

end Erdos1165.HLOZSourceTransportFixedCreationObservability
