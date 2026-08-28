import Wikipedia.HopfProblem.DegreeCollapsePatchNormalDerivative
import Wikipedia.SmoothSixDPoincare.CornerNormalDerivative

/-!
# Nonzero corner derivative relative to a selected embedded branch

The first branch only needs to agree with the clean zero section near the
selected source point. Transversality and the opposite native corner axis
give the nonzero normal derivative needed to construct the joining strip.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D B E M A Z Z' N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup Z'] [NormedSpace ℝ Z']
  [TopologicalSpace N] [ChartedSpace A N]
  [TopologicalSpace P] [ChartedSpace Z P]
  (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞)

theorem patch_corner_normalDerivative_ne_zero {F : N → M} {G : P → M} {K : Set N}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ F '' K ↔ q.2 = 0)
    (c : PartialDiffeomorph 𝓘(ℝ, Z') 𝓘(ℝ, Z) Z' P ∞) (hc : (0 : Z') ∈ c.source)
    {x : N} (hK : K ∈ 𝓝 x) (hx : F x ∈ Φ.target) (hxy : G (c 0) = F x)
    (ht : Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c 0))))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B)
    {k : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W)
    (hW : IsOpen W) (h0W : (0 : ℝ × ℝ) ∈ W) {v : Z'} (hv : v ≠ 0)
    (haxis : ∀ t, (0, t) ∈ W → k (0, t) = G (c (t • v))) :
    fderiv ℝ (normalCoordinate Φ ∘ k) (0, 0) (0, 1) ≠ 0 ∧
      ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), fderiv ℝ (normalCoordinate Φ ∘ k) q (0, 1) ≠ 0 := by
  let H := normalCoordinate Φ ∘ k
  let a := (normalCoordinate Φ ∘ G) ∘ c
  have hk0 : k (0 : ℝ × ℝ) = F x := by
    have h := haxis 0 h0W
    rw [zero_smul] at h
    exact h.trans hxy
  have hkΦ : k (0 : ℝ × ℝ) ∈ Φ.target := hk0.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hkΦ)
  have hH : ContDiffAt ℝ ∞ H 0 :=
    (hnormal.comp 0 (hk.contMDiffAt (hW.mem_nhds h0W))).contDiffAt
  have hy : G (c 0) ∈ Φ.target := hxy.symm ▸ hx
  have hnormalG := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have ha : ContDiffAt ℝ ∞ a 0 :=
    ((hnormalG.comp (c 0) hG.contMDiffAt).comp 0
      (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc))).contDiffAt
  have haxisW : ∀ᶠ t : ℝ in 𝓝 0, (0, t) ∈ W :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hW.mem_nhds h0W)
  have heq : (fun t : ℝ => H (0, t)) =ᶠ[𝓝 0] (fun t => a (t • v)) := by
    filter_upwards [haxisW] with t htW
    exact congrArg (normalCoordinate Φ) (haxis t htW)
  have hderiv := vertical_derivative_of_axis_germ v
    (hH.differentiableAt (by simp)) (ha.differentiableAt (by simp)) heq
  have hbij : Bijective (fderiv ℝ a 0) :=
    bijective_normalDerivative_patch_parametrization Φ hF hG hclean c hc hK hx hxy ht hdim
  have hn : fderiv ℝ H (0, 0) (0, 1) ≠ 0 := by
    rw [hderiv]
    intro hz
    exact hv (hbij.1 (hz.trans (map_zero (fderiv ℝ a 0)).symm))
  exact ⟨hn, eventually_vertical_derivative_ne_zero hH hn⟩

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
