import Wikipedia.SmoothSixDPoincare.SmoothManifoldLocalFlow
import Wikipedia.SmoothSixDPoincare.CompactFlow
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Joint smoothness of the existing compact-manifold flow

Uniqueness identifies the already chosen global trajectories with the
smooth native local flows. Compactness gives a uniform short-time interval;
the original action law and connectedness of the time axis extend smoothness
to every time. No new flow or new trajectory is substituted.
-/

noncomputable section

open Set Metric Manifold Filter Topology Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
    (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
  (hv₁ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
    (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))

include hv

theorem exists_contMDiffOn_flow (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ ε > (0 : ℝ),
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (uncurry (flow hv₁)) (Ioo (-ε) ε ×ˢ U) := by
  obtain ⟨U, hU, hp, ε, hε, F, hFsmooth, hF⟩ := exists_smooth_manifoldLocalFlow hv p
  refine ⟨U, hU, hp, ε, hε, ?_⟩
  have hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => F (q.2, q.1)) (Ioo (-ε) ε ×ˢ U) :=
    hFsmooth.comp (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn
      (fun _ hq => ⟨hq.2, hq.1⟩)
  exact hsmooth.congr (fun q hq => flow_eq_local hv₁ hε hF hq.2 hq.1)

theorem exists_smalltime_contMDiff_flow :
    ∃ ε > (0 : ℝ), ∀ t ∈ Ioo (-ε) ε, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (flow hv₁ t) := by
  classical
  choose U hU hp ε hε hF using exists_contMDiffOn_flow hv hv₁
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hp x⟩)
  have hN : (⋂ p ∈ s, Ioo (-(ε p)) (ε p)) ∈ 𝓝 (0 : ℝ) :=
    (biInter_finset_mem s).mpr fun p _ => Ioo_mem_nhds (neg_lt_zero.mpr (hε p)) (hε p)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨δ, hδ, ?_⟩
  intro t ht x
  have htall : t ∈ ⋂ p ∈ s, Ioo (-(ε p)) (ε p) := hδsub
    (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht)
  obtain ⟨p, hps, hxp⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have htp := mem_iInter₂.mp htall p hps
  exact ((hF p).contMDiffAt (prod_mem_nhds (Ioo_mem_nhds htp.1 htp.2)
    ((hU p).mem_nhds hxp))).comp x (contMDiffAt_const.prodMk contMDiffAt_id)

theorem contMDiff_flow_time (t : ℝ) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (flow hv₁ t) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_smalltime_contMDiff_flow hv hv₁
  let S : Set ℝ := {s | ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (flow hv₁ s)}
  have hstep {s u : ℝ} (hs : s ∈ S) (hu : dist u s < ε) : u ∈ S := by
    have hus : u - s ∈ Ioo (-ε) ε := by
      exact abs_lt.mp (by simpa only [Real.dist_eq] using hu)
    have hc := (hsmall (u - s) hus).comp hs
    have heq : (fun x => flow hv₁ (u - s) (flow hv₁ s x)) = flow hv₁ u := by
      funext x
      rw [← flow_add, sub_add_cancel]
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (flow hv₁ u)
    rw [← heq]
    exact hc
  have hS : IsOpen S := isOpen_iff_mem_nhds.mpr fun s hs =>
    mem_of_superset (ball_mem_nhds s hε) (fun u hu => hstep hs hu)
  have hSc : IsOpen Sᶜ := isOpen_iff_mem_nhds.mpr fun s hs =>
    mem_of_superset (ball_mem_nhds s hε) (fun u hu h => hs (hstep h (by
      change dist u s < ε at hu
      rwa [dist_comm])))
  have hzero : (0 : ℝ) ∈ S := by
    change ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (flow hv₁ 0)
    have heq : flow hv₁ 0 = id := funext (flow_zero hv₁)
    rw [heq]
    exact contMDiff_id
  have hSuniv : S = univ :=
    (show IsClopen S from ⟨isOpen_compl_iff.mp hSc, hS⟩).eq_univ ⟨0, hzero⟩
  change t ∈ S
  rw [hSuniv]
  exact mem_univ t

theorem contMDiff_flow :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (uncurry (flow hv₁)) := by
  intro q
  obtain ⟨U, hU, hp, ε, hε, hF⟩ := exists_contMDiffOn_flow hv hv₁ (flow hv₁ q.1 q.2)
  have hzero := hF.contMDiffAt (prod_mem_nhds
    (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε) (hU.mem_nhds hp))
  have hmap : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun r : ℝ × M => (r.1 - q.1, flow hv₁ q.1 r.2)) q :=
    (contMDiffAt_fst.sub contMDiffAt_const).prodMk
      ((contMDiff_flow_time hv hv₁ q.1).contMDiffAt.comp q contMDiffAt_snd)
  have hzero' : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (uncurry (flow hv₁))
      ((fun r : ℝ × M => (r.1 - q.1, flow hv₁ q.1 r.2)) q) := by
    simpa only [sub_self] using hzero
  have hcomp := hzero'.comp q hmap
  have heq : (fun r : ℝ × M => flow hv₁ (r.1 - q.1) (flow hv₁ q.1 r.2)) =
      uncurry (flow hv₁) := by
    funext r
    rw [← flow_add, sub_add_cancel]
    rfl
  exact heq ▸ hcomp

theorem contMDiff_compactFlow :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × M => compactFlow hv₁ q.1 q.2) :=
  contMDiff_flow hv hv₁

def compactFlowDiffeomorph (t : ℝ) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞ where
  toEquiv := ((compactFlow hv₁).toHomeomorph t).toEquiv
  contMDiff_toFun := contMDiff_flow_time hv hv₁ t
  contMDiff_invFun := contMDiff_flow_time hv hv₁ (-t)

theorem compactFlowDiffeomorph_apply (t : ℝ) (x : M) :
    compactFlowDiffeomorph hv hv₁ t x = compactFlow hv₁ t x := rfl

theorem compactFlowDiffeomorph_symm_apply (t : ℝ) (x : M) :
    (compactFlowDiffeomorph hv hv₁ t).symm x = compactFlow hv₁ (-t) x := rfl

theorem compactFlowDiffeomorph_toHomeomorph (t : ℝ) :
    (compactFlowDiffeomorph hv hv₁ t).toHomeomorph = (compactFlow hv₁).toHomeomorph t := rfl

omit hv in
theorem flow_eq_of_isMIntegralCurves (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) v) (t : ℝ) (x : M) :
    F t x = flow hv₁ t x := by
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hv₁
    (hcurve x) (isMIntegralCurve_flow hv₁ x) (t₀ := 0)
    ((F.map_zero_apply x).trans (flow_zero hv₁ x).symm)
  exact congrFun heq t

theorem contMDiff_of_isMIntegralCurves (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) v) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × M => F q.1 q.2) := by
  have hV₁ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)) := hv.of_le (by simp)
  have heq : (fun q : ℝ × M => F q.1 q.2) = uncurry (flow hV₁) :=
    funext (fun q => flow_eq_of_isMIntegralCurves hV₁ F hcurve q.1 q.2)
  rw [heq]
  exact contMDiff_flow hv hV₁

theorem contMDiff_time_of_isMIntegralCurves (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) v) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t) :=
  (contMDiff_of_isMIntegralCurves hv F hcurve).comp (contMDiff_const.prodMk contMDiff_id)

end Wikipedia.SmoothSixDPoincare.FlowConstruction
