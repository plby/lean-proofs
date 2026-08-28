import Wikipedia.HopfProblem.DegreeCollapseSmoothLocalODE
import Wikipedia.SmoothSixDPoincare.StarConvexSmoothExtension

/-!
# Joint smoothness for local coordinate fields

The ordinary field only needs to be smooth on its actual open coordinate
domain. A germ-preserving global extension and joint continuity shrink
the given local solution family into the agreement region. The proved
Picard endpoint identification then gives joint smoothness at time zero.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A local smooth coordinate field gives joint smoothness of the actual local solution family. -/
theorem contDiffAt_local_field_flow {v : E → E} {O P : Set E}
    (hv : ContDiffOn ℝ ∞ v O) (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    (hP : IsOpen P) (hxP : x ∈ P) {ε : ℝ} (hε : 0 < ε)
    {H : E × ℝ → E} (hc : ContinuousAt H (x, 0))
    (hinit : ∀ p ∈ P, H (p, 0) = p)
    (hH : ∀ p ∈ P, ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun s : ℝ => H (p, s)) (v (H (p, t))) t) :
    ContDiffAt ℝ ∞ H (x, 0) := by
  obtain ⟨w, hwM, heq⟩ := exists_smooth_extension_near_point hv.contMDiffOn hO hxO
  have hw : ContDiff ℝ ∞ w := contMDiff_iff_contDiff.mp hwM
  have hevent : ∀ᶠ q in 𝓝 (x, (0 : ℝ)), w (H q) = v (H q) := by
    have heq' : w =ᶠ[𝓝 (H (x, 0))] v := by rwa [hinit x hxP]
    exact hc heq'
  have hdom : P ×ˢ Ioo (-ε) ε ∈ 𝓝 (x, (0 : ℝ)) :=
    prod_mem_nhds (hP.mem_nhds hxP) (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε)
  have hdom' : ∀ᶠ q in 𝓝 (x, (0 : ℝ)), q ∈ P ×ˢ Ioo (-ε) ε := hdom
  obtain ⟨δ, hδ, hsub⟩ := Metric.eventually_nhds_iff.mp (hdom'.and hevent)
  have hrect (p : E) (hp : p ∈ ball x δ) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      (p, t) ∈ P ×ˢ Ioo (-ε) ε ∧ w (H (p, t)) = v (H (p, t)) := by
    apply hsub
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨hp, by simpa only [dist_zero_right, Real.norm_eq_abs] using abs_lt.mpr ht⟩
  let W : C(E, E) := ⟨w, hw.continuous⟩
  apply contDiffAt_ordinary_localFlow W hw isOpen_ball (mem_ball_self hδ) hδ
  · intro p hp
    exact hinit p (hrect p hp 0 ⟨neg_lt_zero.mpr hδ, hδ⟩).1.1
  · intro p hp t ht
    have hh := hrect p hp t ht
    have hd := hH p hh.1.1 t hh.1.2
    change HasDerivAt (fun s => H (p, s)) (w (H (p, t))) t
    rw [hh.2]
    exact hd

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
