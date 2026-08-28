import Wikipedia.HopfProblem.DegreeCollapseRadialTraceBoundary

/-!
# Native radial parameter charts for sphere passages in every dimension

Translate the actual puncture and invert the original smooth radial cylinder.
The small Euclidean sphere is exactly the original linking sphere map.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open PassageHomology

def sphereRadialParameterChart (m : ℕ) (τ : ℝ) (u : Hemisphere.Sphere m) :
    PartialDiffeomorph (𝓡 (m + 1)) (𝓘(ℝ, ℝ).prod (𝓡 m))
      (Hemisphere.Ambient (m + 1)) (ℝ × Hemisphere.Sphere m) ∞ := by
  let P := Hemisphere.Ambient (m + 1)
  let _ : Fact (Module.finrank ℝ P = m + 1) := ⟨by simp [P, Hemisphere.Ambient]⟩
  let b := cylinderPuncture τ u
  let T : Diffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) P P ∞ := {
    toEquiv := {
      toFun := fun z => b + z
      invFun := fun z => z - b
      left_inv := fun z => add_sub_cancel_left b z
      right_inv := by intro z; simp }
    contMDiff_toFun := (contDiff_const.add contDiff_id).contMDiff
    contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  exact T.toPartialDiffeomorph.trans (radialCylinderChart P m u).symm

theorem sphereRadialParameterChart_zero_mem_source (m : ℕ) (τ : ℝ)
    (u : Hemisphere.Sphere m) : (0 : Hemisphere.Ambient (m + 1)) ∈
      (sphereRadialParameterChart m τ u).source := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨by simp [Hemisphere.Ambient]⟩
  change (0 : Hemisphere.Ambient (m + 1)) ∈ univ ∧ cylinderPuncture τ u + 0 ∈
    (radialCylinderChart (Hemisphere.Ambient (m + 1)) m u).target
  rw [add_zero, radialCylinderChart_mem_target]
  exact ⟨mem_univ _, norm_pos_iff.mp (by rw [norm_cylinderPuncture]; exact Real.exp_pos τ)⟩

theorem sphereRadialParameterChart_zero (m : ℕ) (τ : ℝ) (u : Hemisphere.Sphere m) :
    sphereRadialParameterChart m τ u 0 = (τ, u) := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨by simp [Hemisphere.Ambient]⟩
  change (radialCylinderChart (Hemisphere.Ambient (m + 1)) m u).symm
    (cylinderPuncture τ u + 0) = (τ, u)
  rw [add_zero]
  have heq : radialCylinderChart (Hemisphere.Ambient (m + 1)) m u (τ, u) =
      cylinderPuncture τ u := rfl
  rw [← heq]
  exact (radialCylinderChart (Hemisphere.Ambient (m + 1)) m u).left_inv
    (radialCylinderChart_mem_source (Hemisphere.Ambient (m + 1)) m u (τ, u))

theorem sphereRadialParameterChart_apply (m : ℕ) (τ : ℝ) (u : Hemisphere.Sphere m)
    (z : Hemisphere.Ambient (m + 1)) (hz : cylinderPuncture τ u + z ≠ 0) :
    sphereRadialParameterChart m τ u z =
      (radialCylinderHomeomorph (Hemisphere.Ambient (m + 1))).symm
        ⟨cylinderPuncture τ u + z, hz⟩ := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨by simp [Hemisphere.Ambient]⟩
  exact radialCylinderChart_symm_eq (Hemisphere.Ambient (m + 1)) m u
    (cylinderPuncture τ u + z) hz

theorem sphereRadialParameterChart_link (m : ℕ) (τ : ℝ) (u : Hemisphere.Sphere m)
    (ε : ℝ) (hε : 0 < ε) (hεu : ε < Real.exp τ) (w : Hemisphere.Sphere m) :
    sphereRadialParameterChart m τ u (ε • w.val) =
      (cylinderLink τ u ε hε hεu w).val := by
  have hz : cylinderPuncture τ u + ε • w.val ≠ 0 :=
    (linkingSphere (cylinderPuncture τ u) ε hε (by rwa [norm_cylinderPuncture]) w).property.1
  exact sphereRadialParameterChart_apply m τ u (ε • w.val) hz

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
