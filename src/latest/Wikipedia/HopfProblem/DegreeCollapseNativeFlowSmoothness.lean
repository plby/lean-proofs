import Wikipedia.HopfProblem.DegreeCollapseLocalFieldFlowSmoothness
import Wikipedia.HopfProblem.DegreeCollapseSmoothIntegralCurve
import Mathlib.Dynamics.Flow

/-!
# Joint smoothness of the original native flow at time zero

The original flow is written in a genuine chart. Joint continuity keeps
nearby trajectories in that chart; the native chain rule supplies its
ordinary coordinate ODE. The proved local-field smoothness theorem applies,
and composition with the original inverse chart restores the native atlas.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

open MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- A complete native flow of a smooth field is jointly smooth at its initial time slice. -/
theorem contMDiffAt_native_flow_zero
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (p : M) :
    ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : M × ℝ => F q.2 q.1) (p, 0) := by
  let e := NoExoticSixSphere.modelChartPartialDiffeomorph (I := 𝓘(ℝ, E)) p
  have hp : p ∈ e.source := mem_extChartAt_source p
  have hz : e p ∈ e.target := e.map_source' hp
  have he : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e p :=
    (e.contMDiffOn p hp).contMDiffAt (e.open_source.mem_nhds hp)
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm (e p) :=
    (e.symm.contMDiffOn (e p) hz).contMDiffAt (e.open_target.mem_nhds hz)
  let C (q : E × ℝ) : M := F q.2 (e.symm q.1)
  let H (q : E × ℝ) : E := e (C q)
  have hC0 : C (e p, 0) = p := by
    change F 0 (e.symm (e p)) = p
    rw [F.map_zero_apply]
    exact e.left_inv' hp
  have hFC : Continuous (fun q : ℝ × M => F q.1 q.2) :=
    F.continuous continuous_fst continuous_snd
  have hic : ContinuousAt (fun q : E × ℝ => e.symm q.1) (e p, 0) :=
    hi.continuousAt.comp_of_eq
      (show ContinuousAt (Prod.fst : E × ℝ → E) (e p, 0) from continuousAt_fst) rfl
  have hC : ContinuousAt C (e p, 0) :=
    hFC.continuousAt.comp (continuousAt_snd.prodMk hic)
  have hHC : ContinuousAt H (e p, 0) := by
    have heC : ContinuousAt e (C (e p, 0)) := by rw [hC0]; exact he.continuousAt
    exact heC.comp hC
  have htarget : ∀ᶠ q : E × ℝ in 𝓝 (e p, 0), q.1 ∈ e.target :=
    continuousAt_fst (e.open_target.mem_nhds hz)
  have hstay : ∀ᶠ q : E × ℝ in 𝓝 (e p, 0), C q ∈ e.source := by
    apply hC
    rw [hC0]
    exact e.open_source.mem_nhds hp
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp (htarget.and hstay)
  have hrect (z : E) (hz' : z ∈ ball (e p) δ) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      z ∈ e.target ∧ C (z, t) ∈ e.source := by
    apply hδsub (y := (z, t))
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hz', by simpa only [dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht⟩
  have hinit (z : E) (hz' : z ∈ ball (e p) δ) : H (z, 0) = z := by
    change e (F 0 (e.symm z)) = z
    rw [F.map_zero_apply]
    exact e.right_inv' (hrect z hz' 0 ⟨neg_lt_zero.mpr hδ, hδ⟩).1
  have hODE (z : E) (hz' : z ∈ ball (e p) δ) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      HasDerivAt (fun s => H (z, s)) (coordinateField (V := V) e (H (z, t))) t :=
    hasDerivAt_coordinate_integralCurve e (hcurve (e.symm z)) (hrect z hz' t ht).2
  have hH : ContDiffAt ℝ ∞ H (e p, 0) := contDiffAt_local_field_flow
    (contDiffOn_coordinateField hV e) e.open_target hz isOpen_ball (mem_ball_self hδ)
    hδ hHC hinit hODE
  let A (q : M × ℝ) : E × ℝ := (e q.1, q.2)
  have hA : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) ∞ A (p, 0) := by
    apply (contMDiffAt_prod_module_iff A).mpr
    have hefst : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (e ∘ (Prod.fst : M × ℝ → M)) (p, 0) := he.comp (p, 0) contMDiffAt_fst
    exact ⟨hefst, contMDiffAt_snd⟩
  have hHA : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (H ∘ A) (p, 0) :=
    hH.contMDiffAt.comp (p, 0) hA
  have hHA0 : (H ∘ A) (p, 0) = e p := congrArg e hC0
  have hi' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm ((H ∘ A) (p, 0)) := by
    rw [hHA0]
    exact hi
  apply (hi'.comp (p, 0) hHA).congr_of_eventuallyEq
  have hstart : ∀ᶠ q : M × ℝ in 𝓝 (p, 0), q.1 ∈ e.source :=
    continuousAt_fst (e.open_source.mem_nhds hp)
  have hfinish : ∀ᶠ q : M × ℝ in 𝓝 (p, 0), F q.2 q.1 ∈ e.source := by
    have hc : Continuous (fun q : M × ℝ => F q.2 q.1) :=
      F.continuous continuous_snd continuous_fst
    apply hc.continuousAt
    simpa only [F.map_zero_apply] using e.open_source.mem_nhds hp
  filter_upwards [hstart, hfinish] with q hq hFq
  have heq : e.symm (e q.1) = q.1 := e.left_inv' hq
  change F q.2 q.1 = e.symm (e (F q.2 (e.symm (e q.1))))
  rw [heq]
  exact (e.left_inv' hFq).symm

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
