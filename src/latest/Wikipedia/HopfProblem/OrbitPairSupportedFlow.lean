import Wikipedia.HopfProblem.OrbitPairSupportedIntegralCurves
import Wikipedia.SmoothSixDPoincare.SmoothManifoldLocalFlow
import Mathlib.Dynamics.Flow
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Connected.Clopen

/-!
# Jointly smooth native flows of compactly supported vector fields

The manifold itself need not be compact. The compact support gives a
uniform short-time smoothness interval; outside the support the flow is
the identity on a neighborhood. The action law extends smoothness to
every time. Every time map is a native diffeomorphism with inverse given
by the negative time, and the complement of the support is fixed exactly.
-/

noncomputable section

open Set Metric Manifold Filter Topology Function
open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SupportedFlow

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

structure Field where
  vector : (x : M) → TangentSpace 𝓘(ℝ, E) x
  support : Set M
  compact_support : IsCompact support
  smooth : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
    (fun x => (⟨x, vector x⟩ : TangentBundle 𝓘(ℝ, E) M))
  zero_outside : ∀ x ∉ support, vector x = 0

namespace Field

variable (v : Field (E := E) (M := M))

theorem smooth_one : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
    (fun x => (⟨x, v.vector x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
  v.smooth.of_le (by simp)

def flow (t : ℝ) (x : M) : M :=
  (exists_globalIntegralCurve v.compact_support v.smooth_one v.zero_outside x).choose t

theorem flow_zero (x : M) : v.flow 0 x = x :=
  (exists_globalIntegralCurve v.compact_support v.smooth_one v.zero_outside x).choose_spec.1

theorem integralCurve (x : M) : IsMIntegralCurve (fun t => v.flow t x) v.vector :=
  (exists_globalIntegralCurve v.compact_support v.smooth_one v.zero_outside x).choose_spec.2

theorem flow_add (s t : ℝ) (x : M) : v.flow (s + t) x = v.flow s (v.flow t x) := by
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless v.smooth_one
    ((v.integralCurve x).comp_add t) (v.integralCurve (v.flow t x))
    (t₀ := 0) (by simp only [comp_apply, zero_add, v.flow_zero])
  exact congrFun heq s

theorem flow_stationary (t : ℝ) {x : M} (hx : x ∉ v.support) : v.flow t x = x := by
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless v.smooth_one
    (v.integralCurve x) (isMIntegralCurve_const (v.zero_outside x hx))
    (t₀ := 0) (v.flow_zero x)
  exact congrFun heq t

theorem flow_eq_local {U : Set M} {ε : ℝ} (hε : 0 < ε) {F : M × ℝ → M}
    (hF : ∀ x ∈ U, F (x, 0) = x ∧
      IsMIntegralCurveOn (fun t => F (x, t)) v.vector (Ioo (-ε) ε))
    {x : M} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    v.flow t x = F (x, t) :=
  isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨neg_lt_zero.mpr hε, hε⟩ v.smooth_one
    ((v.integralCurve x).isMIntegralCurveOn _) (hF x hx).2
    ((v.flow_zero x).trans (hF x hx).1.symm) ht

theorem smooth_near_zero (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ ε > (0 : ℝ),
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (uncurry v.flow) (Ioo (-ε) ε ×ˢ U) := by
  obtain ⟨U, hU, hp, ε, hε, F, hFs, hF⟩ :=
    Wikipedia.SmoothSixDPoincare.FlowConstruction.exists_smooth_manifoldLocalFlow v.smooth p
  refine ⟨U, hU, hp, ε, hε, ?_⟩
  have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => F (q.2, q.1)) (Ioo (-ε) ε ×ˢ U) :=
    hFs.comp (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn
      (fun _ hq => ⟨hq.2, hq.1⟩)
  exact hs.congr (fun q hq => v.flow_eq_local hε hF hq.2 hq.1)

theorem smooth_small_times :
    ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (-ε) ε, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (v.flow t) := by
  classical
  choose U hU hp ε hε hF using v.smooth_near_zero
  obtain ⟨s, hs⟩ := v.compact_support.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hp x⟩)
  have hN : (⋂ p ∈ s, Ioo (-(ε p)) (ε p)) ∈ 𝓝 (0 : ℝ) :=
    (biInter_finset_mem s).mpr fun p _ => Ioo_mem_nhds (neg_lt_zero.mpr (hε p)) (hε p)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨δ, hδ, ?_⟩
  intro t ht x
  by_cases hx : x ∈ v.support
  · have htall : t ∈ ⋂ p ∈ s, Ioo (-(ε p)) (ε p) := hδsub
      (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht)
    obtain ⟨p, hps, hxp⟩ := mem_iUnion₂.mp (hs hx)
    have htp := mem_iInter₂.mp htall p hps
    exact ((hF p).contMDiffAt (prod_mem_nhds (Ioo_mem_nhds htp.1 htp.2)
      ((hU p).mem_nhds hxp))).comp x (contMDiffAt_const.prodMk contMDiffAt_id)
  · apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [v.compact_support.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact v.flow_stationary t hy

theorem smooth_time (t : ℝ) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (v.flow t) := by
  obtain ⟨ε, hε, hsmall⟩ := v.smooth_small_times
  let S : Set ℝ := {s | ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (v.flow s)}
  have hstep {s u : ℝ} (hs : s ∈ S) (hu : dist u s < ε) : u ∈ S := by
    have hus : u - s ∈ Ioo (-ε) ε :=
      abs_lt.mp (by simpa only [Real.dist_eq] using hu)
    have hc := (hsmall (u - s) hus).comp hs
    have heq : (fun x => v.flow (u - s) (v.flow s x)) = v.flow u := by
      funext x
      rw [← v.flow_add, sub_add_cancel]
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (v.flow u)
    rw [← heq]
    exact hc
  have hS : IsOpen S := isOpen_iff_mem_nhds.mpr fun s hs =>
    mem_of_superset (ball_mem_nhds s hε) (fun u hu => hstep hs hu)
  have hSc : IsOpen Sᶜ := isOpen_iff_mem_nhds.mpr fun s hs =>
    mem_of_superset (ball_mem_nhds s hε) (fun u hu h => hs (hstep h (by
      change dist u s < ε at hu
      rwa [dist_comm])))
  have hzero : (0 : ℝ) ∈ S := by
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (v.flow 0)
    rw [show v.flow 0 = id from funext v.flow_zero]
    exact contMDiff_id
  have hSuniv : S = univ :=
    (show IsClopen S from ⟨isOpen_compl_iff.mp hSc, hS⟩).eq_univ ⟨0, hzero⟩
  change t ∈ S
  rw [hSuniv]
  exact mem_univ t

theorem smooth_flow :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (uncurry v.flow) := by
  intro q
  obtain ⟨U, hU, hp, ε, hε, hF⟩ := v.smooth_near_zero (v.flow q.1 q.2)
  have hzero := hF.contMDiffAt (prod_mem_nhds
    (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε) (hU.mem_nhds hp))
  have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun r : ℝ × M => (r.1 - q.1, v.flow q.1 r.2)) q :=
    (contMDiffAt_fst.sub contMDiffAt_const).prodMk
      ((v.smooth_time q.1).contMDiffAt.comp q contMDiffAt_snd)
  have hzero' : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (uncurry v.flow) ((fun r : ℝ × M => (r.1 - q.1, v.flow q.1 r.2)) q) := by
    simpa only [sub_self] using hzero
  have hcomp := hzero'.comp q hmap
  have heq : (fun r : ℝ × M => v.flow (r.1 - q.1) (v.flow q.1 r.2)) = uncurry v.flow := by
    funext r
    rw [← v.flow_add, sub_add_cancel]
    rfl
  exact heq ▸ hcomp

def toFlow : Flow ℝ M where
  toFun := v.flow
  cont' := v.smooth_flow.continuous
  map_add' := v.flow_add
  map_zero' := v.flow_zero

def diffeomorph (t : ℝ) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞ where
  toEquiv := (v.toFlow.toHomeomorph t).toEquiv
  contMDiff_toFun := v.smooth_time t
  contMDiff_invFun := v.smooth_time (-t)

theorem diffeomorph_apply (t : ℝ) (x : M) : v.diffeomorph t x = v.flow t x := rfl

theorem diffeomorph_symm_apply (t : ℝ) (x : M) : (v.diffeomorph t).symm x = v.flow (-t) x := rfl

end Field

end Wikipedia.HopfProblem.OrbitPair.SupportedFlow
