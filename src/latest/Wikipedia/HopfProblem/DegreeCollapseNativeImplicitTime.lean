import Wikipedia.HopfProblem.DegreeCollapseImplicitScalarTime
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# Smooth implicit time germs in the original manifold atlas

The scalar implicit-function theorem is applied in an actual source chart
and transported back. The time derivative and the level value belong to
the original family; no changed manifold structure is introduced.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- An actual transverse time derivative gives a smooth native root germ. -/
theorem exists_native_smooth_time_germ {H : M × ℝ → ℝ} {p : M} {t c v : ℝ}
    (hH : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H (p, t))
    (hlevel : H (p, t) = c) (htime : HasDerivAt (fun s : ℝ => H (p, s)) v t)
    (hv : v ≠ 0) :
    ∃ θ : M → ℝ, θ p = t ∧ ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ p ∧
      ∀ᶠ q in 𝓝 p, H (q, θ q) = c := by
  let e := NoExoticSixSphere.modelChartPartialDiffeomorph (I := 𝓘(ℝ, E)) p
  have hp : p ∈ e.source := mem_extChartAt_source p
  have hz : e p ∈ e.target := e.map_source' hp
  have he : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e p :=
    (e.contMDiffOn p hp).contMDiffAt (e.open_source.mem_nhds hp)
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm (e p) :=
    (e.symm.contMDiffOn (e p) hz).contMDiffAt (e.open_target.mem_nhds hz)
  let B (q : E × ℝ) : M × ℝ := (e.symm q.1, q.2)
  let F : E × ℝ → ℝ := H ∘ B
  have hleft : e.symm (e p) = p := e.left_inv' hp
  have hB : ContMDiffAt 𝓘(ℝ, E × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞ B (e p, t) := by
    have hfst : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞
        (Prod.fst : E × ℝ → E) (e p, t) := contDiffAt_fst.contMDiffAt
    have hfirst := hi.comp (e p, t) hfst
    exact hfirst.prodMk contDiffAt_snd.contMDiffAt
  have hB0 : B (e p, t) = (p, t) := Prod.ext hleft rfl
  have hH' : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H (B (e p, t)) := by
    rw [hB0]
    exact hH
  have hF : ContDiffAt ℝ ∞ F (e p, t) := (hH'.comp (e p, t) hB).contDiffAt
  have hFtime : (fun s : ℝ => F (e p, s)) = fun s => H (p, s) := by
    funext s
    change H (e.symm (e p), s) = H (p, s)
    rw [hleft]
  have hFt : HasDerivAt (fun s : ℝ => F (e p, s)) v t := by rw [hFtime]; exact htime
  have hFc : F (e p, t) = c := by
    change H (B (e p, t)) = c
    rw [hB0]
    exact hlevel
  obtain ⟨θ, hθ, hsmooth, hroot⟩ := SmoothODE.exists_smooth_scalar_time_germ hF hFc hFt hv
  refine ⟨θ ∘ e, hθ, hsmooth.contMDiffAt.comp p he, ?_⟩
  filter_upwards [e.open_source.mem_nhds hp, he.continuousAt hroot] with q hq hrootq
  have hqleft : e.symm (e q) = q := e.left_inv' hq
  change H (e.symm (e q), θ (e q)) = c at hrootq
  change H (q, θ (e q)) = c
  rwa [hqleft] at hrootq

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
