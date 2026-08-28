import Wikipedia.HopfProblem.DegreeCollapseRadialLinkMeridian
import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundarySigns

/-!
# Retain the actual normal derivative in the passage link comparison

The local meridian map has exactly the homology action of the normalized
invertible derivative, not merely an unspecified unit coefficient. This
allows two geometrically constructed traces to be compared by their
relative normal determinant.
-/

noncomputable section

open Set Function Filter Metric ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open PassageHomology SingularMayerVietoris

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M}

theorem exists_radial_link_meridian_with_derivative
    (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    (H : C(ℝ × S₂, d.UpperLevel)) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (x₀ : S₂) (v : sphere (0 : d.chart.PositiveCoordinates) 1)
    (hpoint : d.surgery.beltSphere v = H (τ, x₀))
    (hcross : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : S₂,
      H (t, x) ∈ range d.surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (L : P₃ ≃L[ℝ] d.chart.NegativeCoordinates)
    (hL : HasFDerivAt (fun z : P₃ => d.beltNormal (H (radialParameterChart τ x₀ z)))
      L.toContinuousLinearMap 0) :
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ H (τ, x₀) →
    ∃ (ε : ℝ) (hε : 0 < ε) (hεx : ε < Real.exp τ),
      ∃ (w : sphere (0 : d.chart.PositiveCoordinates) 1)
        (β : C(S₂, sphere (0 : d.chart.NegativeCoordinates) 1)),
        singularHomologyMap β 2 =
          singularHomologyMap (LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 ∧
        ((puncturedPassageTrace H (range d.surgery.beltSphere) hτ x₀ hcross).comp
          (cylinderLink τ x₀ ε hε hεx)).Homotopic
            ((nativeBeltTubeMeridian d w (1 / 2) (by norm_num) (by norm_num)).comp β) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro hg
  let Ψ := radialParameterChart τ x₀
  have hΨ0 : (0 : P₃) ∈ Ψ.source := radialParameterChart_zero_mem_source τ x₀
  have hΨ : ContMDiffAt (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ Ψ 0 :=
    Ψ.contMDiffOn_toFun.contMDiffAt (Ψ.open_source.mem_nhds hΨ0)
  have hΨc : ContinuousAt Ψ 0 := hΨ.continuousAt
  have htime : (fun z : P₃ => (Ψ z).1) ⁻¹' Ioo (0 : ℝ) 1 ∈ 𝓝 (0 : P₃) := by
    apply hΨc.fst.preimage_mem_nhds
    apply isOpen_Ioo.mem_nhds
    simpa only [Ψ, radialParameterChart_zero] using hτ
  let t := Ψ.source ∩ (ball (0 : P₃) (Real.exp τ) ∩
    (fun z : P₃ => (Ψ z).1) ⁻¹' Ioo (0 : ℝ) 1)
  have ht : t ∈ 𝓝 (0 : P₃) :=
    inter_mem (Ψ.open_source.mem_nhds hΨ0) (inter_mem (ball_mem_nhds _ (Real.exp_pos τ)) htime)
  have hc : ContinuousOn (fun z : P₃ => H (Ψ z)) t :=
    H.continuous.comp_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono inter_subset_left)
  have hcenter : H (Ψ 0) = d.surgery.beltSphere v := by
    rw [show Ψ 0 = (τ, x₀) from radialParameterChart_zero τ x₀]
    exact hpoint.symm
  obtain ⟨s, hs, hst, hcs, hdomain, hsmall⟩ :=
    exists_small_native_belt_neighborhood d (fun z : P₃ => H (Ψ z)) v ht hc hcenter
  have hgΨ : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ H (Ψ 0) := by
    rw [show Ψ 0 = (τ, x₀) from radialParameterChart_zero τ x₀]
    exact hg
  have hnormal := d.contMDiffOn_beltNormal hf |>.contMDiffAt
    (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  have hnormal' : ContMDiffAt 𝓘(ℝ, RegularLevel.Model E)
      𝓘(ℝ, d.chart.NegativeCoordinates) ∞ d.beltNormal (H (Ψ 0)) := by
    rw [hcenter]
    exact hnormal
  have hF : ContDiffAt ℝ ∞ (fun z : P₃ => d.beltNormal (H (Ψ z))) 0 :=
    (ContMDiffAt.comp (g := d.beltNormal) (f := fun z : P₃ => H (Ψ z))
      0 hnormal' (hgΨ.comp 0 hΨ)).contDiffAt
  have hF0 : d.beltNormal (H (Ψ 0)) = 0 := by rw [hcenter, d.beltNormal_belt]
  obtain ⟨b⟩ := LocalDegree.nonempty_boundaryData_of_contDiffAt L hL hF0 hs hF
  have hball (u : S₂) : b.radius • u.val ∈ s := by
    apply b.ball_subset
    rw [mem_closedBall_zero_iff, LocalDegree.norm_radius_smul b.radius b.radius_pos u]
  have hεx : b.radius < Real.exp τ := by
    have hh := (hst (hball x₀)).2.1
    rwa [mem_ball_zero_iff, LocalDegree.norm_radius_smul b.radius b.radius_pos x₀] at hh
  obtain ⟨J, hJ, w, hmeridian⟩ := normal_boundary_homotopic_native_meridian d
    (fun z : P₃ => H (Ψ z)) b hcs hdomain hsmall (1 / 2) (by norm_num) (by norm_num)
  have hlink : (puncturedPassageTrace H (range d.surgery.beltSphere) hτ x₀ hcross).comp
      (cylinderLink τ x₀ b.radius b.radius_pos hεx) = J := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    have htimeu : (cylinderLink τ x₀ b.radius b.radius_pos hεx u).val.1 ∈ Icc (0 : ℝ) 1 := by
      rw [← radialParameterChart_link τ x₀ b.radius b.radius_pos hεx u]
      exact ⟨(hst (hball u)).2.2.1.le, (hst (hball u)).2.2.2.le⟩
    rw [ContinuousMap.comp_apply, puncturedPassageTrace_on_interval H
      (range d.surgery.beltSphere) hτ x₀ hcross _ htimeu, hJ]
    rw [show Ψ (b.radius • u.val) = _ from
      radialParameterChart_link τ x₀ b.radius b.radius_pos hεx u]
  refine ⟨b.radius, b.radius_pos, hεx, w, b.normalizedMap,
    b.normalized_homology_compare 2, ?_⟩
  rw [hlink]
  exact hmeridian

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
