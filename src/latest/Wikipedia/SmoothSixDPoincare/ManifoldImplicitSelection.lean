import Wikipedia.SmoothSixDPoincare.SmoothImplicitSelection
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Smoothness of a native manifold-valued parameter's scalar implicit solution

The parameter is the original boundaryless manifold. The proof passes to
its actual chart, applies the scalar implicit-selection theorem, and returns
to the native smooth structure. The already given continuous scalar function
is retained exactly, including when smoothness is relative to a set.
-/

noncomputable section

open Set Manifold Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem contMDiffWithinAt_scalarImplicitSelection {f : M × ℝ → ℝ} {τ : M → ℝ}
    {S : Set M} {x : M} {d : ℝ}
    (hf : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f (x, τ x))
    (hd : HasDerivAt (fun t => f (x, t)) d (τ x)) (hd₀ : d ≠ 0)
    (hτ : ContinuousWithinAt τ S x)
    (heq : ∀ᶠ y in 𝓝[S] x, f (y, τ y) = f (x, τ x)) :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ τ S x := by
  let e := chartAt E x
  have hx : x ∈ e.source := mem_chart_source E x
  have hxe : e.symm (e x) = x := e.left_inv hx
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm (e x) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x)).contMDiffAt
      (e.open_target.mem_nhds (e.map_source hx))
  let g : E → ℝ := τ ∘ e.symm
  let F : E × ℝ → ℝ := fun p => f (e.symm p.1, p.2)
  have hgx : g (e x) = τ x := congrArg τ hxe
  have hparam : ContMDiffAt 𝓘(ℝ, E × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : E × ℝ => (e.symm p.1, p.2)) (e x, τ x) :=
    (hi.comp (e x, τ x) contDiffAt_fst.contMDiffAt).prodMk contDiffAt_snd.contMDiffAt
  have hF : ContDiffAt ℝ ∞ F (e x, g (e x)) := by
    rw [hgx]
    have hf' : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f
        (e.symm (e x), τ x) := by rwa [hxe]
    exact (hf'.comp (e x, τ x) hparam).contDiffAt
  have hd' : HasDerivAt (fun t => F (e x, t)) d (g (e x)) := by
    simpa only [F, hgx, hxe] using hd
  have himap : Tendsto e.symm (𝓝[e.symm ⁻¹' S] e x) (𝓝[S] x) := by
    have h := hi.continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (show MapsTo e.symm (e.symm ⁻¹' S) S from fun _ hy => hy)
    rwa [hxe] at h
  have hg : ContinuousWithinAt g (e.symm ⁻¹' S) (e x) := by
    have h := Filter.Tendsto.comp hτ himap
    rwa [← hgx] at h
  have heq' : ∀ᶠ y in 𝓝[e.symm ⁻¹' S] e x, F (y, g y) = F (e x, g (e x)) := by
    filter_upwards [himap.eventually heq] with y hy
    simpa only [F, g, Function.comp_apply, hxe] using hy
  have hpre := contDiffWithinAt_scalarImplicitSelection hF hd' hd₀ hg heq'
  rw [contMDiffWithinAt_iff_source]
  change ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g
    (e.symm ⁻¹' S ∩ Set.range (id : E → E)) (e x)
  rw [range_id, inter_univ]
  exact hpre.contMDiffWithinAt

end Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus
