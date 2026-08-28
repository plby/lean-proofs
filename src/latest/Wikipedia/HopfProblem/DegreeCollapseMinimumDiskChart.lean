import Wikipedia.SmoothSixDPoincare.MinimumDiskCoordinates
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# A native partial diffeomorphism parametrizing the minimum disk

The zero negative factor is removed by a genuine continuous linear
equivalence. The positive isometry, scaling, and inverse signed Morse
chart give a partial diffeomorphism on an open Euclidean neighborhood.
Its exact height formula is retained, including on the disk boundary.
-/

noncomputable section

open Set Function Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}

def minimumDiskLinearCoordinates (c : SignedMorseChart (E := E) f p)
    (hmin : IsLocalMin f p) (ρ : ℝ) (hρ : 0 < ρ) :
    Hemisphere.Ambient (Module.finrank ℝ E) ≃L[ℝ]
      (c.NegativeCoordinates × c.PositiveCoordinates) := by
  let _ : Unique c.NegativeCoordinates :=
    { default := 0, uniq := c.negative_eq_zero_of_localMin hmin }
  exact ((c.minimumPositiveIsometry hmin).symm.toContinuousLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ c.PositiveCoordinates ρ hρ.ne').toContinuousLinearEquiv).trans
      (ContinuousLinearEquiv.uniqueProd ℝ c.PositiveCoordinates c.NegativeCoordinates).symm

theorem minimumDiskLinearCoordinates_apply (c : SignedMorseChart (E := E) f p)
    (hmin : IsLocalMin f p) (ρ : ℝ) (hρ : 0 < ρ)
    (v : Hemisphere.Ambient (Module.finrank ℝ E)) :
    minimumDiskLinearCoordinates c hmin ρ hρ v =
      (0, ρ • (c.minimumPositiveIsometry hmin).symm v) := rfl

def minimumDiskChart (c : SignedMorseChart (E := E) f p)
    (hmin : IsLocalMin f p) (ρ : ℝ) (hρ : 0 < ρ) :
    PartialDiffeomorph 𝓘(ℝ, Hemisphere.Ambient (Module.finrank ℝ E)) 𝓘(ℝ, E)
      (Hemisphere.Ambient (Module.finrank ℝ E)) M ∞ :=
  (minimumDiskLinearCoordinates c hmin ρ hρ).toDiffeomorph.toPartialDiffeomorph.trans
    c.splitChart.symm

theorem minimumDiskChart_apply (c : SignedMorseChart (E := E) f p)
    (hmin : IsLocalMin f p) (ρ : ℝ) (hρ : 0 < ρ)
    (v : Hemisphere.Ambient (Module.finrank ℝ E)) :
    minimumDiskChart c hmin ρ hρ v =
      c.splitChart.symm (0, ρ • (c.minimumPositiveIsometry hmin).symm v) := rfl

theorem minimumDiskChart_mem_source (c : SignedMorseChart (E := E) f p)
    (hmin : IsLocalMin f p) (ρ : ℝ) (hρ : 0 < ρ)
    (v : Hemisphere.Ambient (Module.finrank ℝ E)) :
    v ∈ (minimumDiskChart c hmin ρ hρ).source ↔
      (0, ρ • (c.minimumPositiveIsometry hmin).symm v) ∈ c.splitChart.target := by
  change (v ∈ univ ∧ (0, ρ • (c.minimumPositiveIsometry hmin).symm v) ∈
    c.splitChart.target) ↔ _
  simp only [mem_univ, true_and]

theorem minimumDiskChart_target (c : SignedMorseChart (E := E) f p)
    (hmin : IsLocalMin f p) (ρ : ℝ) (hρ : 0 < ρ) :
    (minimumDiskChart c hmin ρ hρ).target = c.splitChart.source := by
  ext y
  change (y ∈ c.splitChart.source ∧ c.splitChart y ∈ univ) ↔ _
  simp only [mem_univ, and_true]

theorem minimumDiskChart_height (c : SignedMorseChart (E := E) f p)
    (hmin : IsLocalMin f p) (ρ : ℝ) (hρ : 0 < ρ)
    (v : Hemisphere.Ambient (Module.finrank ℝ E))
    (hv : v ∈ (minimumDiskChart c hmin ρ hρ).source) :
    f (minimumDiskChart c hmin ρ hρ v) = f p + ρ ^ 2 * ‖v‖ ^ 2 := by
  rw [minimumDiskChart_apply, c.splitChart_inverse_equation
    ((minimumDiskChart_mem_source c hmin ρ hρ v).mp hv)]
  simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero,
    norm_smul, Real.norm_eq_abs, abs_of_pos hρ, LinearIsometryEquiv.norm_map, mul_pow]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
