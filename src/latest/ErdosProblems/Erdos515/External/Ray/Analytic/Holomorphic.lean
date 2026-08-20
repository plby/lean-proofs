module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import ErdosProblems.Erdos515.External.Ray.Analytic.Analytic
import ErdosProblems.Erdos515.External.Ray.Hartogs.Osgood
import ErdosProblems.Erdos515.External.Ray.Misc.Bounds
import ErdosProblems.Erdos515.External.Ray.Misc.Multilinear
import ErdosProblems.Erdos515.External.Ray.Misc.Topology

/-!
## Basics about complex analytic functions
-/

open Complex (exp I log)
open Filter (atTop)
open Metric (ball closedBall sphere isOpen_ball)
open Set (univ)
open scoped Real NNReal ENNReal Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- `f : ℂ × ℂ → E` is differentiable iff it is analytic -/
public theorem differentiable_iff_analytic2 {E : Type} {f : ℂ × ℂ → E} {s : Set (ℂ × ℂ)}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (o : IsOpen s) :
    DifferentiableOn ℂ f s ↔ AnalyticOnNhd ℂ f s := by
  constructor
  · intro d; apply osgood o d.continuousOn
    · intro z0 z1 zs
      rcases Metric.isOpen_iff.mp o (z0, z1) zs with ⟨r, rp, rs⟩
      have d0 : DifferentiableOn ℂ (fun z0 ↦ f (z0, z1)) (ball z0 r) := by
        apply DifferentiableOn.comp d
        exact DifferentiableOn.prodMk differentiableOn_id (differentiableOn_const _)
        intro z0 z0s; apply rs; simp at z0s ⊢; assumption
      exact (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr d0 z0 (Metric.mem_ball_self rp)
    · intro z0 z1 zs
      rcases Metric.isOpen_iff.mp o (z0, z1) zs with ⟨r, rp, rs⟩
      have d1 : DifferentiableOn ℂ (fun z1 ↦ f (z0, z1)) (ball z1 r) := by
        apply DifferentiableOn.comp d
        exact DifferentiableOn.prodMk (differentiableOn_const _) differentiableOn_id
        intro z1 z1s; apply rs; simp at z1s ⊢; assumption
      exact (Complex.analyticOnNhd_iff_differentiableOn isOpen_ball).mpr d1 z1 (Metric.mem_ball_self rp)
  · exact fun a ↦ a.differentiableOn

/-- `f : ℂ × ℂ → E` is `ContDiffAt` iff it is analytic -/
public theorem contDiffAt_iff_analytic_at2 {E : Type} {f : ℂ × ℂ → E} {x : ℂ × ℂ} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {n : WithTop ℕ∞} (n1 : 1 ≤ n) :
    ContDiffAt ℂ n f x ↔ AnalyticAt ℂ f x := by
  constructor
  · intro d
    rcases d.contDiffOn (m := 1) (by simpa) (by simp) with ⟨u, un, d⟩
    rcases mem_nhds_iff.mp un with ⟨v, uv, vo, vx⟩
    refine (differentiable_iff_analytic2 vo).mp ?_ _ vx
    exact (d.mono uv).differentiableOn (by decide)
  · intro a; exact a.contDiffAt.of_le le_top

/-- If `f` is analytic in an open ball, it has a power series over that ball -/
public lemma analyticOnNhd_ball_iff_hasFPowerSeriesOnBall {f : ℂ → E} {c : ℂ} {r : ℝ≥0∞}
    (r0 : 0 < r) :
    AnalyticOnNhd ℂ f (Metric.eball c r) ↔
      ∃ p : FormalMultilinearSeries ℂ ℂ E, HasFPowerSeriesOnBall f p c r := by
  constructor
  · intro a
    obtain ⟨p,s,hs⟩ := a c (by simp only [Metric.mem_eball, edist_self, r0])
    have grow : ∀ t : ℝ≥0, 0 < t → t < r → HasFPowerSeriesOnBall f p c t := by
      intro t t0 tr
      have d : DifferentiableOn ℂ f (closedBall c t) := by
        apply (a.mono ?_).differentiableOn
        intro x m
        simp only [Metric.mem_closedBall, dist_le_coe, Metric.mem_eball,
          ← ENNReal.coe_le_coe, ← edist_nndist] at m ⊢
        order
      have ht := d.hasFPowerSeriesOnBall t0
      exact hs.hasFPowerSeriesAt.eq_formalMultilinearSeries ht.hasFPowerSeriesAt ▸ ht
    refine ⟨p, ?_, r0, ?_⟩
    · exact ENNReal.le_of_forall_pos_nnreal_lt fun t t0 tr ↦ (grow t t0 tr).r_le
    · intro y yr
      simp only [Metric.mem_eball, edist_zero_right] at yr
      obtain ⟨t,yt,tr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp yr
      have t0 : 0 < t := by
        simp only [enorm_eq_nnnorm, ENNReal.coe_lt_coe] at yt
        exact pos_of_gt yt
      refine (grow t t0 tr).hasSum ?_
      simp only [Metric.eball_coe, Metric.mem_ball, dist_zero_right]
      simpa only [← ofReal_norm, ENNReal.ofReal_lt_coe_iff, norm_nonneg] using yt
  · intro ⟨p,a⟩
    exact a.analyticOnNhd
