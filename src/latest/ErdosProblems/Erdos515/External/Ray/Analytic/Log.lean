module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.Algebra.GroupWithZero
import ErdosProblems.Erdos515.External.Ray.Analytic.Analytic
import ErdosProblems.Erdos515.External.Ray.Misc.Continuation

/-!
## Logs of nonzero analytic functions

If `f : ℂ → ℂ` is analytic and nonzero in `ball 0 r`, we can take its logarithm.
-/

open Classical
open Complex (exp log)
open Metric (ball closedBall isOpen_ball)
open Set
open scoped Real Topology
noncomputable section

variable {f : ℂ → ℂ} {c z : ℂ} {r : ℝ}

/-- `exp` is locally injective -/
lemma exp_eq_exp_of_lt {z w : ℂ} (e : exp z = exp w) (lt : ‖z - w‖ < 2 * π) : z = w := by
  simp only [Complex.exp_eq_exp_iff_exists_int] at e
  obtain ⟨n, e⟩ := e
  simp only [e, add_eq_left, mul_eq_zero, Int.cast_eq_zero, OfNat.ofNat_ne_zero,
    Complex.ofReal_eq_zero, Real.pi_ne_zero, or_self, Complex.I_ne_zero, or_false]
  rw [add_comm w, ← sub_eq_iff_eq_add] at e
  simp only [e, Complex.norm_mul, Complex.norm_intCast, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
    ← lt_div_iff₀ Real.two_pi_pos, div_self Real.two_pi_pos.ne'] at lt
  simpa only [← Int.cast_abs, ← Int.cast_one (R := ℝ), Int.cast_lt, Int.abs_lt_one_iff] using lt

/-- Logarithms of nonzero analytic functions exist -/
public theorem AnalyticOnNhd.exists_log (fa : AnalyticOnNhd ℂ f (ball c r))
    (f0 : ∀ z ∈ ball c r, f z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball c r) ∧ g c = Complex.log (f c) ∧
      ∀ z ∈ ball c r, f z = exp (g z) := by
  by_cases r0 : r ≤ 0
  · simp [Metric.ball_eq_empty.mpr r0]
    exact ⟨fun z ↦ Complex.log (f z), rfl⟩
  simp only [not_le] at r0
  set p : (ℂ → ℂ) → ℂ → Prop := fun g z ↦ AnalyticAt ℂ g z ∧ f z = exp (g z)
  have slit : ∀ w ∈ ball c r, ∀ᶠ z in 𝓝 w, f z / f w ∈ Complex.slitPlane := by
    intro w wm
    refine ((fa _ wm).continuousAt.div_const _).eventually_mem ?_
    simp only [div_self (f0 _ wm)]
    exact Complex.isOpen_slitPlane.mem_nhds (by simp)
  have loc : ∀ w ∈ ball c r, ∃ g, g w = Complex.log (f w) ∧ ∀ᶠ z in 𝓝 w, p g z := by
    intro w wm
    set g : ℂ → ℂ := fun z ↦ Complex.log (f z / f w) + Complex.log (f w)
    refine ⟨g, ?_, ?_⟩
    · simp only [g, div_self (f0 _ wm), Complex.log_one, zero_add]
    · filter_upwards [isOpen_ball.eventually_mem wm, slit w wm] with z zm s
      refine ⟨?_, ?_⟩
      · exact ((fa _ zm).div_const.clog s).add analyticAt_const
      · have zw : f z / f w ≠ 0 := by simp [f0 _ zm, f0 _ wm]
        simp only [g, Complex.exp_add, Complex.exp_log zw, Complex.exp_log (f0 _ wm),
          div_mul_cancel₀ _ (f0 _ wm)]
  have near : ∀ {w g h} (pg : p g w) (ph : p h w) (e : g w = h w),
      ∀ᶠ z in 𝓝 w, ‖g z - h z‖ < 2 * π := by
    intro w g h pg ph e
    refine ContinuousAt.eventually_lt (f := fun z ↦ ‖g z - h z‖) ?_ continuousAt_const ?_
    · exact (pg.1.continuousAt.sub ph.1.continuousAt).norm
    · simp [e, Real.pi_pos]
  have unique : ∀ {g h : ℂ → ℂ} {t : Set ℂ}, IsOpen t → IsPreconnected t → (∀ x ∈ t, p g x) →
      (∀ x ∈ t, p h x) → (∃ x ∈ t, g x = h x) → EqOn g h t := by
    intro g h t ot ct pg ph ⟨w,wt,e⟩
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) ?_ ?_ ct wt ?_
    · exact fun z m ↦ (pg _ m).1
    · exact fun z m ↦ (ph _ m).1
    · filter_upwards [ot.eventually_mem wt, near (pg _ wt) (ph _ wt) e] with z zm near
      exact exp_eq_exp_of_lt ((pg _ zm).2.symm.trans (ph _ zm).2) near
  obtain ⟨fs, fsc, fsp⟩ := loc c (by simp [r0])
  have i : Continuation p c r fs := {
    pos := r0
    congr := by
      intro g h x pg e
      exact ⟨pg.1.congr e, pg.2.trans (by rw [e.self_of_nhds])⟩
    start := fsp
    point := by
      intro g t w t0 tr pg wt
      obtain ⟨h,_,ph⟩ := loc w (Metric.closedBall_subset_ball tr wt)
      obtain ⟨e,e0,ph⟩ := Metric.eventually_nhds_iff_ball.mp ph
      have all : ∀ᶠ z in 𝓝 w, z ∈ ball w e := isOpen_ball.eventually_mem (by simp [e0])
      have freq : ∃ᶠ z in 𝓝 w, z ∈ ball c t := by
        simp only [← mem_closure_iff_frequently, closure_ball _ t0.ne', wt]
      have ne : (ball w e ∩ ball c t).Nonempty := (all.and_frequently freq).exists
      obtain ⟨d,dm⟩ := ne
      set h' : ℂ → ℂ := fun z ↦ h z + (g d - h d)
      have ph' : ∀ y ∈ ball w e, p h' y := by
        intro y yw
        refine ⟨(ph y yw).1.add analyticAt_const, ?_⟩
        simp only [h', Complex.exp_add, Complex.exp_sub, ← (ph _ yw).2, ← (ph _ dm.1).2, mul_one,
          ← (pg.self_of_nhdsSet _ dm.2).2, div_self (f0 _ (Metric.ball_subset_ball tr.le dm.2))]
      have gh' : EqOn g h' (ball w e ∩ ball c t) := by
        apply unique (isOpen_ball.inter isOpen_ball)
          ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
        · exact fun x ⟨_,m⟩ ↦ pg.self_of_nhdsSet _ m
        · exact fun x ⟨m,_⟩ ↦ ph' _ m
        · exact ⟨d, dm, by simp only [add_sub_cancel, h']⟩
      refine ⟨h', ?_, ?_⟩
      · filter_upwards [all] with z m
        exact ph' _ m
      · exact (all.and_frequently freq).mp (.of_forall fun y m ↦ ⟨m.2, (gh' m).symm⟩)
    unique := unique }
  obtain ⟨g,e,pg⟩ := i.grow
  simp only [isOpen_ball.nhdsSet_eq, Filter.eventually_principal] at pg
  exact ⟨g, fun _ m ↦ (pg _ m).1, by simp only [e, fsc], fun _ m ↦ (pg _ m).2⟩

/-- `n`th roots of nonzero analytic functions exist -/
public theorem AnalyticOnNhd.exists_root (fa : AnalyticOnNhd ℂ f (ball c r))
    (f0 : ∀ z ∈ ball c r, f z ≠ 0) {n : ℕ} (n0 : n ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball c r) ∧ g c = exp (Complex.log (f c) / n) ∧
      ∀ z ∈ ball c r, f z = g z ^ n := by
  obtain ⟨g, ga, e, fg⟩ := fa.exists_log f0
  refine ⟨fun z ↦ exp (g z / n), ?_, ?_, ?_⟩
  · intro z m
    exact (ga _ m).div_const.cexp
  · simp only [e]
  · intro z m
    rw [fg z m, ← Complex.exp_nat_mul, mul_div_cancel₀ _ (by simpa)]
