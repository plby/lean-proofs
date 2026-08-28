import Wikipedia.SmoothSixDPoincare.MorseCollapseHomology

/-!
# Surjectivity consequences of the original Morse exact sequence

Vanishing on an actual outer sublevel makes the corresponding native
boundary or collapse map surjective. These are consequences of the proved
exact sequence with its retained original maps, not additional cell-matrix
or degree assumptions.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
theorem coreBoundaryHomology_surjective_of_upper (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} k)] :
    Surjective (d.coreBoundaryHomologyMap k) := by
  intro a
  have ha : a ∈ LinearMap.ker (d.lowerRealizationHomologyMap k) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_lower hf k hk] at ha
  exact ha

open Classical in
theorem morseConnecting_surjective_of_lower (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} k)] :
    Surjective (d.morseConnectingMap hf k) := by
  intro a
  have ha : a ∈ LinearMap.ker (d.coreBoundaryHomologyMap k) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_attachingSphere hf k hk] at ha
  exact ha

open Classical in
/-- The actual whole-sublevel collapse is onto homology when the lower group vanishes. -/
theorem upperCollapse_surjective_of_lower (hf : Continuous f) (k : ℕ)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} (k + 1))] :
    Surjective (singularHomologyMap (d.upperCollapseMap hf) (k + 2)) := by
  intro a
  let C := OnePointCover.sphereHomologyEquiv (N := d.chart.NegativeCoordinates)
    OnePointCover.overlapRadius OnePointCover.overlapRadius_pos k
  obtain ⟨b, hb⟩ := d.morseConnecting_surjective_of_lower hf (k + 1) (by omega) (C a)
  refine ⟨b, C.injective ?_⟩
  exact (d.upperCollapse_homology_equiv_compare hf k b).trans hb

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
