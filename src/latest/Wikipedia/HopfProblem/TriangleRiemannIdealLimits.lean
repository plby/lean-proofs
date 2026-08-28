import Wikipedia.HopfProblem.TriangleRiemannIdealComparison
import Wikipedia.HopfProblem.RiemannBoundaryHalfStrip

/-!
# The full forward limit at the triangle's ideal vertex

Every approach to infinity inside the actual triangle has imaginary part
tending to infinity: its real coordinate stays in a fixed bounded interval.
The exact exponential/logarithmic inverse then places every such approach
in the analytic ideal germ. The limit is not restricted to selected rays.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology OnePoint

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannBoundary

/-- The actual exponential cusp parameter of the half-Ford triangle. -/
def triangleCuspExp : ℂ → ℂ := halfStripExp stripLeft triangleCuspScale

@[simp] theorem norm_triangleCuspExp (z : ℂ) :
    ‖triangleCuspExp z‖ = Real.exp (-z.im / triangleCuspScale) :=
  norm_halfStripExp _ _ _

theorem triangleCuspExp_im_pos {z : ℂ} (hz : z ∈ triangleInterior) :
    0 < (triangleCuspExp z).im := by
  apply halfStripExp_im_pos stripLeft triangleCuspScale_pos
  exact ⟨hz.1, by simpa only [triangleCuspScale_endpoint] using hz.2.1⟩

/-- The logarithmic coordinate recovers every point of the triangle,
not merely points on a selected vertical ray. -/
theorem triangleCuspLog_triangleCuspExp {z : ℂ} (hz : z ∈ triangleInterior) :
    triangleCuspLog (triangleCuspExp z) = z := by
  apply logHalfStrip_halfStripExp stripLeft triangleCuspScale_pos
  exact ⟨hz.1, by simpa only [triangleCuspScale_endpoint] using hz.2.1⟩

theorem triangleCuspExp_triangleCuspLog {q : ℂ} (hq : q ≠ 0) :
    triangleCuspExp (triangleCuspLog q) = q :=
  halfStripExp_logHalfStrip stripLeft triangleCuspScale_pos.ne' hq

/-- The full horizontal cusp period is the original triangle width. -/
theorem triangleCuspExp_add_width (z : ℂ) :
    triangleCuspExp (z + (width : ℂ)) = triangleCuspExp z := by
  have hp : 2 * triangleCuspScale * Real.pi = width := by
    unfold triangleCuspScale
    field_simp [Real.pi_ne_zero]
  simpa only [hp, triangleCuspExp] using
    halfStripExp_add_period stripLeft triangleCuspScale_pos.ne' z

/-- All ambient compact-set-escaping approaches within the triangle. -/
def triangleInfinityFilter : Filter ℂ := cocompact ℂ ⊓ 𝓟 triangleInterior

theorem triangleInfinity_eventually_mem :
    ∀ᶠ z in triangleInfinityFilter, z ∈ triangleInterior :=
  (show ∀ᶠ z in 𝓟 triangleInterior, z ∈ triangleInterior by simp).filter_mono inf_le_right

/-- The whole-end filter is nontrivial. A single interior vertical ray
is used only to witness nontriviality, not to restrict the forward limit. -/
theorem triangleInfinityFilter_neBot : NeBot triangleInfinityFilter := by
  let z : ℝ → ℂ := fun y => -1 + y * I
  have hmem : ∀ᶠ y : ℝ in atTop, z y ∈ triangleInterior := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    apply triangle_high_halfStrip_mem
    · simpa [z] using stripLeft_lt_neg_one
    · rw [triangleCuspScale_endpoint]
      norm_num [z]
    · simpa [z] using hy
  have hn : Tendsto (fun y : ℝ => ‖z y‖) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro y
    simpa [z] using im_le_norm (z y)
  have hz : Tendsto z atTop (cocompact ℂ) := by
    simpa only [Metric.cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hn
  have ht : Tendsto z atTop triangleInfinityFilter :=
    tendsto_inf.mpr ⟨hz, tendsto_principal.mpr hmem⟩
  exact ht.neBot

/-- The fixed real-coordinate bound controls the norm by the height. -/
theorem triangle_norm_add_stripLeft_le_im {z : ℂ} (hz : z ∈ triangleInterior) :
    ‖z‖ + stripLeft ≤ z.im := by
  have hre : z.re < 0 := hz.2.1.trans (by norm_num)
  have hnorm := norm_le_abs_re_add_abs_im z
  rw [abs_of_neg hre, abs_of_pos hz.2.2.1] at hnorm
  linarith [hz.1]

/-- Escape from compact sets inside the triangle forces the full
imaginary coordinate to tend to positive infinity. -/
theorem tendsto_im_triangleInfinity :
    Tendsto (fun z : ℂ => z.im) triangleInfinityFilter atTop := by
  have hn : Tendsto (fun z : ℂ => ‖z‖) triangleInfinityFilter atTop :=
    tendsto_norm_cocompact_atTop.mono_left inf_le_left
  have hshift : Tendsto (fun z : ℂ => ‖z‖ + stripLeft) triangleInfinityFilter atTop :=
    tendsto_atTop_add_const_right _ stripLeft hn
  apply tendsto_atTop_mono' triangleInfinityFilter _ hshift
  filter_upwards [triangleInfinity_eventually_mem] with z hz
  exact triangle_norm_add_stripLeft_le_im hz

/-- The actual exponential cusp parameter tends to zero along every
compact-set-escaping approach inside the triangle. -/
theorem tendsto_triangleCuspExp_triangleInfinity :
    Tendsto triangleCuspExp triangleInfinityFilter (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_triangleCuspExp]
  apply Real.tendsto_exp_atBot.comp
  have ht := tendsto_neg_atTop_atBot.comp
    (tendsto_im_triangleInfinity.atTop_div_const triangleCuspScale_pos)
  simpa only [Function.comp_def, neg_div] using ht

/-- The exact pointwise cusp formula whenever the actual exponential
parameter lies in the chosen analytic germ's disk. -/
theorem triangleMap_eq_ideal_cusp_of_param_mem {z : ℂ} (hz : z ∈ triangleInterior)
    (hq : triangleCuspExp z ∈ ball (0 : ℂ) triangleIdealGerm.radius) :
    triangleMap z = triangleIdealGerm.function (triangleCuspExp z) := by
  have he := triangleIdealGerm.agrees ⟨hq, triangleCuspExp_im_pos hz⟩
  simpa only [Function.comp_def, triangleCuspLog_triangleCuspExp hz] using he.symm

/-- The actual cusp model holds eventually on the whole triangle end. -/
theorem triangleMap_eventually_eq_ideal_cusp :
    triangleMap =ᶠ[triangleInfinityFilter]
      (fun z => triangleIdealGerm.function (triangleCuspExp z)) := by
  have hsmall := tendsto_triangleCuspExp_triangleInfinity.eventually
    (ball_mem_nhds (0 : ℂ) triangleIdealGerm.radius_pos)
  filter_upwards [triangleInfinity_eventually_mem, hsmall] with z hz hq
  exact triangleMap_eq_ideal_cusp_of_param_mem hz hq

/-- **Full ideal forward limit.** No selected logarithmic ray or
additional cusp asymptotic is a hypothesis. -/
theorem triangleIdeal_forward_limit :
    Tendsto triangleMap triangleInfinityFilter (𝓝 (triangleIdealGerm.function 0)) := by
  have hc := (triangleIdealGerm.analytic 0
    (mem_ball_self triangleIdealGerm.radius_pos)).continuousAt
  exact (hc.tendsto.comp tendsto_triangleCuspExp_triangleInfinity).congr'
    triangleMap_eventually_eq_ideal_cusp.symm

/-- Arbitrary-net form of the full forward ideal limit. -/
theorem triangleIdeal_forward_limit_of_cocompact
    {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto z l (cocompact ℂ)) (hmem : ∀ᶠ i in l, z i ∈ triangleInterior) :
    Tendsto (fun i => triangleMap (z i)) l (𝓝 (triangleIdealGerm.function 0)) :=
  triangleIdeal_forward_limit.comp (tendsto_inf.mpr ⟨hz, tendsto_principal.mpr hmem⟩)

/-- The compact-set-escaping triangle filter is exactly the pullback
of the actual one-point-domain neighborhoods at infinity. -/
theorem comap_coe_triangle_onePoint_nhds_infty :
    comap ((↑) : ℂ → OnePoint ℂ)
      (𝓝[onePointDomain triangleInterior] (∞ : OnePoint ℂ)) = triangleInfinityFilter := by
  have hp : ((↑) : ℂ → OnePoint ℂ) ⁻¹' onePointDomain triangleInterior = triangleInterior :=
    Set.ext fun _ => coe_mem_onePointDomain
  rw [nhdsWithin, comap_inf, OnePoint.comap_coe_nhds_infty, coclosedCompact_eq_cocompact,
    comap_principal, hp]
  rfl

/-- The full ideal forward limit in precisely the source topology used
for the closed triangle in `OnePoint ℂ`. The representative's arbitrary
value at infinity is irrelevant to this within-domain limit. -/
theorem triangleIdeal_forward_limit_onePoint :
    Tendsto triangleOnePointRepresentative
      (𝓝[onePointDomain triangleInterior] (∞ : OnePoint ℂ))
      (𝓝 (triangleIdealGerm.function 0)) := by
  have hRange : range ((↑) : ℂ → OnePoint ℂ) ∈
      𝓝[onePointDomain triangleInterior] (∞ : OnePoint ℂ) := by
    apply mem_of_superset self_mem_nhdsWithin
    rintro _ ⟨z, _, rfl⟩
    exact mem_range_self z
  apply (tendsto_comap'_iff (i := ((↑) : ℂ → OnePoint ℂ)) hRange).mp
  simpa only [Function.comp_def, triangleOnePointRepresentative_coe,
    comap_coe_triangle_onePoint_nhds_infty] using triangleIdeal_forward_limit

/-- Infinity is an actual frontier point of the original triangle in
the one-point compactification. -/
theorem triangle_infty_mem_frontier_onePointDomain :
    (∞ : OnePoint ℂ) ∈ frontier (onePointDomain triangleInterior) := by
  let : NeBot triangleInfinityFilter := triangleInfinityFilter_neBot
  have hz : Tendsto (fun z : ℂ => z) triangleInfinityFilter (cocompact ℂ) :=
    tendsto_id.mono_left inf_le_left
  exact infty_mem_frontier_onePointDomain_of_cocompact hz triangleInfinity_eventually_mem

end Wikipedia.HopfProblem.RiemannMapping
