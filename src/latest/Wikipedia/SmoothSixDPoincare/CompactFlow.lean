import Wikipedia.SmoothSixDPoincare.CompactIntegralCurves
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Connected.Clopen

/-!
# The continuous global flow of a vector field on a compact manifold

The maps are chosen global solutions of the native manifold ODE. Uniqueness
proves the action law and identifies them with the constructed continuous
local flows. Compactness and connectedness of the time axis extend the
local continuity to a genuine jointly continuous global flow.
-/

noncomputable section

open Set Metric Manifold Filter Topology Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  [T2Space M] [CompactSpace M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
    (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))

def flow (t : ℝ) (x : M) : M := (exists_globalIntegralCurve hv x).choose t

@[simp] theorem flow_zero (x : M) : flow hv 0 x = x :=
  (exists_globalIntegralCurve hv x).choose_spec.1

theorem isMIntegralCurve_flow (x : M) : IsMIntegralCurve (fun t => flow hv t x) v :=
  (exists_globalIntegralCurve hv x).choose_spec.2

theorem flow_add (s t : ℝ) (x : M) : flow hv (s + t) x = flow hv s (flow hv t x) := by
  have h₁ := (isMIntegralCurve_flow hv x).comp_add t
  have h₂ := isMIntegralCurve_flow hv (flow hv t x)
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv h₁ h₂
    (t₀ := 0) (by simp only [comp_apply, zero_add, flow_zero])
  exact congrFun heq s

/-- Uniqueness identifies the chosen global trajectories with any matching local flow. -/
theorem flow_eq_local {U : Set M} {ε : ℝ} (hε : 0 < ε) {F : M × ℝ → M}
    (hF : ∀ x ∈ U, F (x, 0) = x ∧
      IsMIntegralCurveOn (fun t => F (x, t)) v (Ioo (-ε) ε))
    {x : M} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    flow hv t x = F (x, t) :=
  isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨neg_lt_zero.mpr hε, hε⟩ hv
    ((isMIntegralCurve_flow hv x).isMIntegralCurveOn _) (hF x hx).2
    ((flow_zero hv x).trans (hF x hx).1.symm) ht

/-- The chosen global trajectories are jointly continuous near time zero and each base point. -/
theorem exists_continuousOn_flow (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ ε > (0 : ℝ),
      ContinuousOn (uncurry (flow hv)) (Ioo (-ε) ε ×ˢ U) := by
  obtain ⟨U, hU, hp, ε, hε, F, hFc, hF⟩ := exists_manifoldLocalFlow p (hv p)
  refine ⟨U, hU, hp, ε, hε, ?_⟩
  have hc : ContinuousOn (fun q : ℝ × M => F (q.2, q.1)) (Ioo (-ε) ε ×ˢ U) :=
    hFc.comp continuous_swap.continuousOn (fun _ hq => ⟨hq.2, hq.1⟩)
  exact hc.congr (fun q hq => flow_eq_local hv hε hF hq.2 hq.1)

/-- For a uniform short time interval, every time map is continuous on the whole manifold. -/
theorem exists_smalltime_continuous :
    ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (-ε) ε, Continuous (flow hv t) := by
  classical
  choose U hU hp ε hε hF using exists_continuousOn_flow hv
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hp x⟩)
  have hN : (⋂ p ∈ s, Ioo (-(ε p)) (ε p)) ∈ 𝓝 (0 : ℝ) :=
    (biInter_finset_mem s).mpr fun p _ => Ioo_mem_nhds (neg_lt_zero.mpr (hε p)) (hε p)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have htall : t ∈ ⋂ p ∈ s, Ioo (-(ε p)) (ε p) := hδsub
    (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht)
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨p, hps, hxp⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have htp := mem_iInter₂.mp htall p hps
  exact ((hF p).continuousAt (prod_mem_nhds (Ioo_mem_nhds htp.1 htp.2)
    ((hU p).mem_nhds hxp))).comp (continuousAt_const.prodMk continuousAt_id)

/-- The flow action law extends continuity of the time maps from small times to every real time. -/
theorem continuous_flow_time (t : ℝ) : Continuous (flow hv t) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_smalltime_continuous hv
  let S : Set ℝ := {s | Continuous (flow hv s)}
  have hstep {s u : ℝ} (hs : s ∈ S) (hu : dist u s < ε) : u ∈ S := by
    have hus : u - s ∈ Ioo (-ε) ε := by
      exact abs_lt.mp (by simpa only [Real.dist_eq] using hu)
    have hc := (hsmall (u - s) hus).comp hs
    have heq : (fun x => flow hv (u - s) (flow hv s x)) = flow hv u := by
      funext x
      rw [← flow_add, sub_add_cancel]
    change Continuous (flow hv u)
    rw [← heq]
    exact hc
  have hS : IsOpen S := isOpen_iff_mem_nhds.mpr fun s hs =>
    mem_of_superset (ball_mem_nhds s hε) (fun u hu => hstep hs hu)
  have hSc : IsOpen Sᶜ := isOpen_iff_mem_nhds.mpr fun s hs =>
    mem_of_superset (ball_mem_nhds s hε) (fun u hu h => hs (hstep h (by
      change dist u s < ε at hu
      rwa [dist_comm])))
  have hzero : (0 : ℝ) ∈ S := by
    change Continuous (flow hv 0)
    have heq : flow hv 0 = id := funext (flow_zero hv)
    rw [heq]
    exact continuous_id
  have hSuniv : S = univ :=
    (show IsClopen S from ⟨isOpen_compl_iff.mp hSc, hS⟩).eq_univ ⟨0, hzero⟩
  change t ∈ S
  rw [hSuniv]
  exact mem_univ t

/-- The ODE flow is jointly continuous in time and initial point. -/
theorem continuous_flow : Continuous (uncurry (flow hv)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨U, hU, hp, ε, hε, hF⟩ := exists_continuousOn_flow hv (flow hv q.1 q.2)
  have hzero := hF.continuousAt (prod_mem_nhds
    (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε) (hU.mem_nhds hp))
  have hmap : ContinuousAt (fun r : ℝ × M => (r.1 - q.1, flow hv q.1 r.2)) q :=
    (continuousAt_fst.sub continuousAt_const).prodMk
      ((continuous_flow_time hv q.1).continuousAt.comp continuousAt_snd)
  have hzero' : ContinuousAt (uncurry (flow hv))
      ((fun r : ℝ × M => (r.1 - q.1, flow hv q.1 r.2)) q) := by
    simpa only [sub_self] using hzero
  have hcomp := hzero'.comp
    (f := fun r : ℝ × M => (r.1 - q.1, flow hv q.1 r.2)) hmap
  have heq : (fun r : ℝ × M => flow hv (r.1 - q.1) (flow hv q.1 r.2)) =
      uncurry (flow hv) := by
    funext r
    rw [← flow_add, sub_add_cancel]
    rfl
  exact heq ▸ hcomp

/-- A native continuous flow whose trajectories solve the original manifold vector field. -/
def compactFlow : Flow ℝ M where
  toFun := flow hv
  cont' := continuous_flow hv
  map_add' := flow_add hv
  map_zero' := flow_zero hv

theorem isMIntegralCurve_compactFlow (x : M) :
    IsMIntegralCurve (fun t => compactFlow hv t x) v := isMIntegralCurve_flow hv x

end Wikipedia.SmoothSixDPoincare.FlowConstruction
