module
public import ErdosProblems.Erdos515.External.Ray.Manifold.Defs
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Cases
import ErdosProblems.Erdos515.External.Ray.Analytic.Holomorphic
import ErdosProblems.Erdos515.External.Ray.Manifold.Analytic
import ErdosProblems.Erdos515.External.Ray.Manifold.Manifold
import ErdosProblems.Erdos515.External.Ray.Manifold.Nontrivial
import ErdosProblems.Erdos515.External.Ray.Manifold.OneDimension
import ErdosProblems.Erdos515.External.Ray.Misc.Connected
import ErdosProblems.Erdos515.External.Ray.Misc.Topology
import ErdosProblems.Erdos515.External.Ray.Misc.TotallyDisconnected

/-!
## The open mapping theorem on 1D complex manifolds

`AnalyticAt.eventually_constant_or_nhds_le_map_nhds` shows that `ℂ → ℂ` analytic
functions are either locally constant or locally open (mapping open neighborhoods to
open neighborhoods).  We slightly generalize this result, to

1. Parameterized analytic maps `f : ℂ → ℂ → ℂ`, where the analogue of openness for `f`
   is openness of `(c,z) ↦ (c, f c z)`.
2. MAnalytic maps `S → T` where `S, T` are 1D analytic manifolds
3. (1) and (2) together: parameterized analytic maps `f : ℂ → S → T`, where
   `S, T` are 1D analytic manifolds.

The parameterized versions follow straightforwardly from effective versions of the
unparameterized version, and specificaly our underlying workhorse is
`DiffContOnCl.ball_subset_image_closedBall`.  The manifold versions are straightforward
extentions of the flat versions lifted to charts.
-/

open Classical
open Complex
open Filter (Tendsto)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball mem_ball mem_closedBall mem_ball_self
  mem_closedBall_self mem_sphere sphere)
open OneDimension
open Set
open scoped ContDiff Real Topology Manifold
noncomputable section

variable {X : Type} [TopologicalSpace X]
variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]
variable {U : Type} [TopologicalSpace U] [ChartedSpace ℂ U]

/-- Nontriviality at a point from nontriviality on a sphere -/
theorem nontrivial_local_of_global {f : ℂ → ℂ} {z : ℂ} {e r : ℝ}
    (fa : AnalyticOnNhd ℂ f (closedBall z r))
    (rp : 0 < r) (ep : 0 < e) (ef : ∀ w, w ∈ sphere z r → e ≤ ‖f w - f z‖) :
    NontrivialMAnalyticAt f z := by
  replace fa : ∃ t, r < t ∧ AnalyticOnNhd ℂ f (ball z t) :=
    exists_ball_superset fa (isOpen_analyticAt ℂ f)
  obtain ⟨t, rt, fa⟩ := fa
  have fh : ∀ x ∈ ball z t, ContMDiffAt I I ω f x := fun _ m ↦ (fa _ m).mAnalyticAt I I
  have zs : z ∈ ball z t := mem_ball_self (by linarith)
  use fh _ zs
  contrapose ef
  simp only [Filter.not_frequently, not_not] at ef
  simp only [not_forall, not_le]
  have zrs : z + r ∈ sphere z r := by
    simp only [mem_sphere, Complex.dist_eq, add_sub_cancel_left, Complex.norm_real, abs_of_pos rp,
      Real.norm_eq_abs]
  use z + r, zrs
  have lc := ContMDiffOn.const_of_locally_const (fun _ m ↦ (fh _ m).contMDiffWithinAt) zs
      isOpen_ball (convex_ball z t).isPreconnected ef (z + r) (Metric.sphere_subset_ball rt zrs)
  simp only [lc, sub_self, norm_zero, ep]

/-- The effective parameterized open mapping theorem for analytic `f : ℂ → ℂ → ℂ`.
    We lose more effectiveness than is optimal, since our goal is ineffective versions. -/
theorem AnalyticOnNhd.ball_subset_image_closedBall_param {f : ℂ → ℂ → ℂ} {c z : ℂ} {e r : ℝ}
    {u : Set ℂ} (fa : AnalyticOnNhd ℂ (uncurry f) (u ×ˢ closedBall z r)) (rp : 0 < r) (ep : 0 < e)
    (un : u ∈ 𝓝 c) (ef : ∀ d, d ∈ u → ∀ w, w ∈ sphere z r → e ≤ ‖f d w - f d z‖) :
    (fun p : ℂ × ℂ ↦ (p.1, f p.1 p.2)) '' u ×ˢ closedBall z r ∈ 𝓝 (c, f c z) := by
  have fn : ∀ d, d ∈ u → ∃ᶠ w in 𝓝 z, f d w ≠ f d z := by
    refine fun d m ↦ (nontrivial_local_of_global (fa.along_snd.mono ?_) rp ep (ef d m)).nonconst
    simp only [mem_prod_eq, ofPred_mem_eq, (iff_true _).mpr m, true_and, subset_refl]
  have op : ∀ d, d ∈ u → ball (f d z) (e / 2) ⊆ f d '' closedBall z r := by
    intro d du; refine DiffContOnCl.ball_subset_image_closedBall ?_ rp (ef d du) (fn d du)
    have e : f d = uncurry f ∘ fun w ↦ (d, w) := rfl
    rw [e]; apply DifferentiableOn.diffContOnCl; apply AnalyticOnNhd.differentiableOn
    refine fa.comp (analyticOnNhd_const.prod analyticOnNhd_id) ?_
    intro w wr; simp only [closure_ball _ rp.ne'] at wr
    simp only [mem_prod_eq, wr, true_and, du]
  rcases Metric.continuousAt_iff.mp
      (fa (c, z) (mk_mem_prod (mem_of_mem_nhds un) (mem_closedBall_self rp.le))).continuousAt
      (e / 4) (by linarith) with
    ⟨s, sp, sh⟩
  rw [mem_nhds_prod_iff]
  refine ⟨u ∩ ball c s, Filter.inter_mem un (Metric.ball_mem_nhds c (by linarith)), ?_⟩
  use ball (f c z) (e / 4), Metric.ball_mem_nhds _ (by linarith)
  intro ⟨d, w⟩ m
  simp only [mem_inter_iff, mem_prod_eq, mem_image, @mem_ball _ _ c] at m op ⊢
  have wm : w ∈ ball (f d z) (e / 2) := by
    simp only [mem_ball] at m ⊢
    specialize @sh ⟨d, z⟩; simp only [Prod.dist_eq, dist_self, Function.uncurry] at sh
    specialize sh (max_lt m.1.2 sp); rw [dist_comm] at sh
    calc dist w (f d z)
      _ ≤ dist w (f c z) + dist (f c z) (f d z) := by bound
      _ < e / 4 + dist (f c z) (f d z) := by linarith [m.2]
      _ ≤ e / 4 + e / 4 := by linarith [sh]
      _ = e / 2 := by ring
  specialize op d m.1.1 wm
  rcases (mem_image _ _ _).mp op with ⟨y, yr, yw⟩
  use⟨d, y⟩
  simp only [yw, and_true, yr, m.1.1]

/-- A trivial lemma used repeatedly below -/
theorem norm_sub_self_lt {z : ℂ} {r : ℝ} (rp : 0 < r) : ‖z - z‖ < r := by
  simp [sub_self, norm_zero, rp]

/-- The parameterized open mapping theorem for analytic `f : ℂ → ℂ → ℂ`:
    `(c,z) ↦ (c, f c z)` sends neighborhoods to neighborhoods if `f` is nontrivial. -/
public theorem NontrivialMAnalyticAt.nhds_le_map_nhds_param' {f : ℂ → ℂ → ℂ} {c z : ℂ}
    (n : NontrivialMAnalyticAt (f c) z) (fa : AnalyticAt ℂ (uncurry f) (c, z)) :
    𝓝 (c, f c z) ≤ Filter.map (fun p : ℂ × ℂ ↦ (p.1, f p.1 p.2)) (𝓝 (c, z)) := by
  -- Reduce to a neighborhood of (c,z) on which f is analytic
  rw [Filter.le_map_iff]
  intro s' sn
  generalize hs : s' ∩ {p | AnalyticAt ℂ (uncurry f) p} = s
  have ss : s ⊆ s' := by rw [← hs]; apply inter_subset_left
  replace sn : s ∈ 𝓝 (c, z) := by rw [← hs]; exact Filter.inter_mem sn fa.eventually_analyticAt
  replace fa : AnalyticOnNhd ℂ (uncurry f) s := by rw [← hs]; apply inter_subset_right
  refine Filter.mem_of_superset ?_ (image_mono ss)
  clear ss hs s'
  rcases Metric.mem_nhds_iff.mp sn with ⟨e, ep, es⟩
  -- Find a radius within s where f c is nontrivial
  have er : ∃ r, 0 < r ∧ closedBall (c, z) r ⊆ s ∧ f c z ∉ f c '' sphere z r := by
    have h := n.eventually_ne; contrapose h
    simp only [not_exists, not_not, not_and, not_exists] at h
    simp only [Classical.not_imp, not_not, Filter.eventually_iff, Metric.mem_nhds_iff, not_exists,
      not_subset, mem_ofPred, not_and]
    intro r rp; specialize h (min (e/2) (r/2)) ?_ ?_
    · bound
    · exact _root_.trans (Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _)
        (half_lt_self ep))) es
    · rcases (mem_image _ _ _).mp h with ⟨w, ws, wz⟩
      use w; refine ⟨?_, ?_, wz⟩
      · exact Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self rp))
          (Metric.sphere_subset_closedBall ws)
      · contrapose ws
        simp only [ws, Metric.mem_sphere, dist_self]
        exact ne_of_lt (by bound)
  rcases er with ⟨r, rp, rs, fr⟩
  -- Get a lower bound of f c '' sphere z r, then extend to a neighborhood of c
  have fc : ContinuousOn (fun w ↦ ‖f c w - f c z‖) (sphere z r) := by
    apply ContinuousOn.norm; refine ContinuousOn.sub ?_ continuousOn_const
    apply fa.along_snd.continuousOn.mono; intro x xs; apply rs
    simp only [← closedBall_prod_same, mem_prod_eq]
    use Metric.mem_closedBall_self rp.le, Metric.sphere_subset_closedBall xs
  rcases (isCompact_sphere _ _).exists_isMinOn (NormedSpace.sphere_nonempty.mpr rp.le) fc with
    ⟨x, xs, xm⟩
  generalize he : ‖f c x - f c z‖ = e
  have ep : 0 < e := by
    contrapose fr
    simp only [norm_pos_iff, sub_ne_zero, not_not, mem_image, ← he] at fr ⊢
    use x, xs, fr
  rcases Metric.uniformContinuousOn_iff.mp
      ((isCompact_closedBall _ _).uniformContinuousOn_of_continuous (fa.continuousOn.mono rs))
      (e / 4) (by linarith) with
    ⟨t, tp, ft⟩
  have ef : ∀ d, d ∈ ball c (min t r) → ∀ w, w ∈ sphere z r → e / 2 ≤ ‖f d w - f d z‖ := by
    intro d dt w wr
    simp only [Complex.dist_eq, Prod.forall, mem_closedBall, Prod.dist_eq, max_le_iff, max_lt_iff,
      Function.uncurry, and_imp] at ft
    simp only [mem_ball, Complex.dist_eq, lt_min_iff] at dt
    have a1 : ‖f d w - f c w‖ ≤ e / 4 :=
      (ft d w dt.2.le (le_of_eq (mem_sphere_iff_norm.mp wr)) c w (norm_sub_self_lt rp).le (le_of_eq (mem_sphere_iff_norm.mp wr)) dt.1
        (norm_sub_self_lt tp)).le
    have a2 : ‖f c z - f d z‖ ≤ e / 4 := by
      refine (ft c z (norm_sub_self_lt rp).le (norm_sub_self_lt rp).le d z
          dt.2.le (norm_sub_self_lt rp).le ?_ (norm_sub_self_lt tp)).le
      rw [← neg_sub, norm_neg]; exact dt.1
    calc ‖f d w - f d z‖
      _ = ‖f c w - f c z + (f d w - f c w) + (f c z - f d z)‖ := by ring_nf
      _ ≥ ‖f c w - f c z + (f d w - f c w)‖ - ‖f c z - f d z‖ := by bound
      _ ≥ ‖f c w - f c z‖ - ‖f d w - f c w‖ - ‖f c z - f d z‖ := by bound
      _ ≥ e - e / 4 - e / 4 := by rw [← he] at a1 a2 ⊢; exact sub_le_sub (sub_le_sub (xm wr) a1) a2
      _ = e / 2 := by ring
  -- Apply the partially effective parameterized open mapping theorem
  have ss : ball c (min t r) ×ˢ closedBall z r ⊆ s := by
    refine _root_.trans ?_ rs; rw [← closedBall_prod_same]; apply prod_mono_left
    exact _root_.trans (Metric.ball_subset_ball (min_le_right _ _)) Metric.ball_subset_closedBall
  exact Filter.mem_of_superset ((fa.mono ss).ball_subset_image_closedBall_param rp (half_pos ep)
    (Metric.ball_mem_nhds _ (by bound)) ef) (image_mono ss)

/-- If `f : S → T` is nontrivial, it is nontrivial when written in charts -/
theorem NontrivialMAnalyticAt.inCharts {f : S → T} {z : S} (n : NontrivialMAnalyticAt f z) :
    NontrivialMAnalyticAt (fun w ↦ extChartAt I (f z) (f ((extChartAt I z).symm w)))
      (extChartAt I z z) := by
  use (mAnalyticAt_iff_of_boundaryless.mp n.mAnalyticAt).2.mAnalyticAt I I
  have c := n.nonconst; contrapose c
  simp only [Filter.not_frequently, not_not, ← map_extChartAt_nhds_of_boundaryless z,
    Filter.eventually_map] at c ⊢
  apply c.mp
  apply ((isOpen_extChartAt_source z).eventually_mem (mem_extChartAt_source (I := I) z)).mp
  apply (n.mAnalyticAt.continuousAt.eventually_mem (extChartAt_source_mem_nhds (I := I) (f z))).mp
  refine .of_forall fun w fm m fn ↦ ?_
  rw [PartialEquiv.left_inv _ m, PartialEquiv.left_inv _ (mem_extChartAt_source z)] at fn
  exact ((PartialEquiv.injOn _).eq_iff fm (mem_extChartAt_source _)).mp fn

/-- The local open mapping theorem, manifold version: if `f : S → T` is nontrivial,
    `f` sends neighborhoods to neighborhoods.  This is a manifold version of
    `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`. -/
public theorem NontrivialMAnalyticAt.nhds_eq_map_nhds [IsManifold I ω T] {f : S → T} {z : S}
    (n : NontrivialMAnalyticAt f z) : 𝓝 (f z) = Filter.map f (𝓝 z) := by
  refine le_antisymm ?_ n.mAnalyticAt.continuousAt
  generalize hg : (fun x ↦ extChartAt I (f z) (f ((extChartAt I z).symm x))) = g
  have ga : AnalyticAt ℂ g (extChartAt I z z) := by
    rw [← hg]; exact (mAnalyticAt_iff_of_boundaryless.mp n.mAnalyticAt).2
  cases' ga.eventually_constant_or_nhds_le_map_nhds with h h
  · contrapose h; clear h; simp only [Filter.not_eventually]
    apply n.inCharts.nonconst.mp; simp only [← hg, Ne, imp_self, Filter.eventually_true]
  · -- The open mapping theorem for g = c ∘ f ∘ c⁻¹ (with charts c) is
    --   𝓝 (g (c z)) ≤ map g (𝓝 (c z))
    -- We have
    --   map c⁻¹ (𝓝 (g (c z))) ≤ map c⁻¹ (map g (𝓝 (c z))  -- Monotonicity of map
    --   𝓝 (c⁻¹ (g (c z))) ≤ map (c' ∘ g ∘ c) (𝓝 z)        -- Charts map 𝓝 to 𝓝
    --   𝓝 (f z) ≤ map f (𝓝 z)                             -- Congruence
    simp only [← map_extChartAt_nhds_of_boundaryless z, Filter.map_map] at h
    replace h := @Filter.map_mono _ _ (extChartAt I (f z)).symm _ _ h
    simp only [← hg] at h; rw [PartialEquiv.left_inv _ (mem_extChartAt_source z)] at h
    simp only [extChartAt_symm_map_nhds' I (f z), Filter.map_map, Function.comp_def] at h
    have e : (fun w ↦ (extChartAt I (f z)).symm
        (extChartAt I (f z) (f ((extChartAt I z).symm (extChartAt I z w))))) =ᶠ[𝓝 z] f := by
      apply ((isOpen_extChartAt_source z).eventually_mem (mem_extChartAt_source (I := I) z)).mp
      apply (n.mAnalyticAt.continuousAt.eventually_mem
        (extChartAt_source_mem_nhds (I := I) (f z))).mp
      refine .of_forall fun w fm m ↦ ?_
      simp only [PartialEquiv.left_inv _ m, PartialEquiv.left_inv _ fm]
    rw [Filter.map_congr e] at h; exact h

/-- Special case of `Filter.prod_map_map_eq` where the first map is `id` -/
theorem Filter.prod_map_id_map_eq {A B C : Type} {f : Filter A} {g : Filter B} {m : B → C} :
    f ×ˢ (Filter.map m g) = Filter.map (fun p : A × B ↦ (p.1, m p.2)) (f ×ˢ g) :=
  Filter.prod_map_map_eq (f₁ := f) (f₂ := g) (m₁ := id) (m₂ := m)

/-- The local open mapping theorem, parameterized manifold version: if `f : ℂ → S → T` is
    nontrivial, then `(c,z) ↦ (c, f c z)` sends neighborhoods to neighborhoods. -/
public theorem NontrivialMAnalyticAt.nhds_eq_map_nhds_param [IsManifold I ω T] {f : ℂ → S → T}
    {c : ℂ} {z : S} (n : NontrivialMAnalyticAt (f c) z)
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) :
    𝓝 (c, f c z) = Filter.map (fun p : ℂ × S ↦ (p.1, f p.1 p.2)) (𝓝 (c, z)) := by
  refine le_antisymm ?_ (continuousAt_fst.prodMk fa.continuousAt)
  generalize hg : (fun e x ↦ extChartAt I (f c z) (f e ((extChartAt I z).symm x))) = g
  have ga : AnalyticAt ℂ (uncurry g) (c, extChartAt I z z) := by
    rw [← hg]; exact (mAnalyticAt_iff_of_boundaryless.mp fa).2
  have gn : NontrivialMAnalyticAt (g c) (extChartAt I z z) := by rw [← hg]; exact n.inCharts
  have h := gn.nhds_le_map_nhds_param' ga
  -- We follow the 𝓝 ≤ 𝓝 argument of nontrivial_mAnalytic_at.nhds_le_map_nhds
  -- above, but a bit more complicated due to the parameterization.
  simp only [nhds_prod_eq, ← map_extChartAt_nhds_of_boundaryless z, Filter.map_map,
    Filter.prod_map_id_map_eq] at h
  replace h := @Filter.map_mono _ _ (fun p : ℂ × ℂ ↦ (p.1, (extChartAt I (f c z)).symm p.2)) _ _ h
  simp only [← hg] at h; rw [PartialEquiv.left_inv _ (mem_extChartAt_source z)] at h
  have pe := Filter.prod_map_id_map_eq (f := 𝓝 c) (g := 𝓝 (extChartAt I (f c z) (f c z)))
    (m := fun x ↦ (extChartAt I (f c z)).symm x)
  rw [extChartAt_symm_map_nhds', ←nhds_prod_eq] at pe
  refine _root_.trans (le_of_eq pe) (_root_.trans h (le_of_eq ?_)); clear h pe
  rw [←nhds_prod_eq, Filter.map_map]; apply Filter.map_congr
  apply ((isOpen_extChartAt_source (c, z)).eventually_mem
    (mem_extChartAt_source (I := II) (c, z))).mp
  apply (fa.continuousAt.eventually_mem (extChartAt_source_mem_nhds (I := I) (f c z))).mp
  refine .of_forall fun ⟨e, w⟩ fm m ↦ ?_
  simp only [uncurry, extChartAt_prod, PartialEquiv.prod_source, mem_prod_eq] at fm m
  simp only [Function.comp, PartialEquiv.left_inv _ m.2, PartialEquiv.left_inv _ fm]
