import Wikipedia.HopfProblem.DegreeCollapseLocalTraceBoundary

/-!
# The local normal boundary of the original radial linking sphere

Translate the actual puncture to zero and use the inverse smooth radial
cylinder chart. Its small Euclidean spheres are exactly the linking maps
in the proved cylinder relation. Native transversality constructs their
actual normal boundary data inside any prescribed neighborhood.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open PassageHomology

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2

def radialParameterChart (τ : ℝ) (u : S₂) :
    PartialDiffeomorph (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) P₃ (ℝ × S₂) ∞ := by
  let _ : Fact (Module.finrank ℝ P₃ = 2 + 1) := ⟨by simp⟩
  let b := cylinderPuncture τ u
  let T : Diffeomorph (𝓡 3) (𝓡 3) P₃ P₃ ∞ := {
    toEquiv := {
      toFun := fun z => b + z
      invFun := fun z => z - b
      left_inv := fun z => add_sub_cancel_left b z
      right_inv := by intro z; simp }
    contMDiff_toFun := (contDiff_const.add contDiff_id).contMDiff
    contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  exact T.toPartialDiffeomorph.trans (radialCylinderChart P₃ 2 u).symm

theorem radialParameterChart_zero_mem_source (τ : ℝ) (u : S₂) :
    (0 : P₃) ∈ (radialParameterChart τ u).source := by
  let _ : Fact (Module.finrank ℝ P₃ = 2 + 1) := ⟨by simp⟩
  change (0 : P₃) ∈ univ ∧ cylinderPuncture τ u + 0 ∈ (radialCylinderChart P₃ 2 u).target
  rw [add_zero, radialCylinderChart_mem_target]
  exact ⟨mem_univ _, norm_pos_iff.mp (by rw [norm_cylinderPuncture]; exact Real.exp_pos τ)⟩

theorem radialParameterChart_zero (τ : ℝ) (u : S₂) : radialParameterChart τ u 0 = (τ, u) := by
  let _ : Fact (Module.finrank ℝ P₃ = 2 + 1) := ⟨by simp⟩
  change (radialCylinderChart P₃ 2 u).symm (cylinderPuncture τ u + 0) = (τ, u)
  rw [add_zero]
  have heq : radialCylinderChart P₃ 2 u (τ, u) = cylinderPuncture τ u := rfl
  rw [← heq]
  exact (radialCylinderChart P₃ 2 u).left_inv (radialCylinderChart_mem_source P₃ 2 u (τ, u))

theorem radialParameterChart_apply (τ : ℝ) (u : S₂) (z : P₃)
    (hz : cylinderPuncture τ u + z ≠ 0) :
    radialParameterChart τ u z =
      (radialCylinderHomeomorph P₃).symm ⟨cylinderPuncture τ u + z, hz⟩ := by
  let _ : Fact (Module.finrank ℝ P₃ = 2 + 1) := ⟨by simp⟩
  exact radialCylinderChart_symm_eq P₃ 2 u (cylinderPuncture τ u + z) hz

theorem radialParameterChart_link (τ : ℝ) (u : S₂) (ε : ℝ)
    (hε : 0 < ε) (hεu : ε < Real.exp τ) (w : S₂) :
    radialParameterChart τ u (ε • w.val) = (cylinderLink τ u ε hε hεu w).val := by
  have hz : cylinderPuncture τ u + ε • w.val ≠ 0 :=
    (linkingSphere (cylinderPuncture τ u) ε hε (by rwa [norm_cylinderPuncture]) w).property.1
  exact radialParameterChart_apply τ u (ε • w.val) hz

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M}

theorem exists_radial_trace_boundary_data
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (g : ℝ × S₂ → d.UpperLevel) (τ : ℝ) (u : S₂)
    (v : sphere (0 : d.chart.PositiveCoordinates) 1) {s : Set P₃} (hs : s ∈ 𝓝 (0 : P₃)) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ g (τ, u) →
    d.surgery.beltSphere v = g (τ, u) →
    NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) 𝓘(ℝ, RegularLevel.Model E)
      g d.surgery.beltSphere (τ, u) v →
    ∃ L : P₃ ≃L[ℝ] d.chart.NegativeCoordinates,
      Nonempty (LocalDegree.BoundaryData
        (fun z : P₃ => d.beltNormal (g (radialParameterChart τ u z))) L s) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro hg hcross htrans
  exact exists_native_trace_boundary_data d hf 2
    (by simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hdim])
    g (τ, u) v (radialParameterChart τ u) (radialParameterChart_zero_mem_source τ u)
    (radialParameterChart_zero τ u) hs hg hcross htrans

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
