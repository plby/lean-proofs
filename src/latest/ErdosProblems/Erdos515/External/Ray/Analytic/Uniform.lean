module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Lattice
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.CauchyIntegral
import ErdosProblems.Erdos515.External.Ray.Misc.Bounds

/-!
## Convergent sequences of analytic functions

We show that uniformly convergence sequences of analytic functions have analytic limits.
-/

open Complex (I)
open Filter (atTop)
open MeasureTheory.MeasureSpace (volume)
open Metric (ball closedBall sphere)
open scoped Real NNReal Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOn_small_cball {f : ℂ → E} {z : ℂ} {r : ℝ≥0} (h : AnalyticOnNhd ℂ f (ball z r))
    (s : ℝ≥0) (sr : s < r) : AnalyticOnNhd ℂ f (closedBall z s) := by
  intro x hx
  rw [closedBall] at hx; simp at hx
  have hb : x ∈ ball z r := by
    rw [ball]; simp only [dist_lt_coe, Set.mem_ofPred_eq]; exact lt_of_le_of_lt hx sr
  exact h x hb

theorem cauchy_bound {f : ℂ → E} {c : ℂ} {r : ℝ≥0} {d : ℝ≥0} {w : ℂ} {n : ℕ} (rp : r > 0)
    (h : ∀ w ∈ closedBall c r, ‖f w‖ ≤ d) :
    ‖cauchyPowerSeries f c r n fun _ ↦ w‖ ≤ ‖w‖ ^ n * r⁻¹ ^ n * d := by
  set wr := ‖w‖ ^ n * r⁻¹ ^ n * d
  rw [cauchyPowerSeries_apply f c r n w, norm_smul]
  generalize hg : (fun z ↦ (w / (z - c)) ^ n • (z - c)⁻¹ • f z) = g
  have gs : ∀ z ∈ sphere c r, ‖g z‖ ≤ wr * r⁻¹ := by
    intro z; simp only [mem_sphere_iff_norm]; intro zr
    simp only [← hg, zr, div_pow, norm_smul, norm_div, norm_pow, norm_inv]
    have zb : z ∈ closedBall c r := by
      simp only [Metric.mem_closedBall, Complex.dist_eq, zr, le_refl]
    have zs := h z zb
    calc ‖w‖ ^ n / ↑r ^ n * (r⁻¹ * ‖f z‖)
      _ = ‖w‖ ^ n * (r⁻¹ ^ n : ℝ≥0) * (r⁻¹ * ‖f z‖) := by
        rw [div_eq_mul_inv, ← inv_pow, NNReal.coe_pow, NNReal.coe_inv]
      _ ≤ ‖w‖ ^ n * r⁻¹ ^ n * (r⁻¹ * d) := by bound
      _ = ‖w‖ ^ n * r⁻¹ ^ n * d * r⁻¹ := by ring
      _ = wr * r⁻¹ := rfl
  have cn := circleIntegral.norm_integral_le_of_norm_le_const (NNReal.coe_nonneg r) gs
  simp only [mul_inv_rev, Complex.inv_I, norm_neg, norm_mul, Complex.norm_I, norm_inv,
    Complex.norm_real, Complex.norm_two, one_mul, div_pow, Real.norm_eq_abs] at hg cn ⊢
  have p3 : ‖π‖ = π := abs_of_nonneg (by bound)
  calc ‖π‖⁻¹ * 2⁻¹ * ‖circleIntegral g c ↑r‖
    _ ≤ ‖π‖⁻¹ * 2⁻¹ * (2 * π * r * (wr * r⁻¹)) := by bound
    _ = π * ‖π‖⁻¹ * (r * r⁻¹) * wr := by ring
    _ = π * π⁻¹ * (r * r⁻¹) * wr := by rw [p3]
    _ = 1 * (r * r⁻¹) * wr := by rw [mul_inv_cancel₀ Real.pi_ne_zero]
    _ = wr := by field_simp; norm_cast; field_simp; simp

theorem circleIntegral_sub {f g : ℂ → E} {c : ℂ} {r : ℝ} (fi : CircleIntegrable f c r)
    (gi : CircleIntegrable g c r) :
    circleIntegral f c r - circleIntegral g c r = circleIntegral (f - g) c r := by
  rw [circleIntegral]
  generalize hf : (fun θ : ℝ ↦ deriv (circleMap c r) θ • f (circleMap c r θ)) = fc
  rw [circleIntegral]
  generalize hg : (fun θ : ℝ ↦ deriv (circleMap c r) θ • g (circleMap c r θ)) = gc
  rw [circleIntegral]
  generalize hfg : (fun θ : ℝ ↦ deriv (circleMap c r) θ • (f - g) (circleMap c r θ)) = fgc
  have hs : fc - gc = fgc := by
    rw [← hf, ← hg, ← hfg]; funext
    simp only [deriv_circleMap, Pi.sub_apply, smul_sub]
  rw [← hs]; clear hfg hs fgc; symm
  have fci := CircleIntegrable.out fi; rw [hf] at fci
  have gci := CircleIntegrable.out gi; rw [hg] at gci
  exact intervalIntegral.integral_sub fci gci

theorem circleMap_nz {c : ℂ} {r : ℝ≥0} {θ : ℝ} (rp : r > 0) : circleMap c r θ - c ≠ 0 := by
  simp only [circleMap_sub_center, Ne, circleMap_eq_center_iff, NNReal.coe_eq_zero]
  intro h; rw [h] at rp; simp only [gt_iff_lt, not_lt_zero] at rp

theorem cauchy_is_circleIntegrable {f : ℂ → E} {c : ℂ} {r : ℝ≥0} (n : ℕ) (w : ℂ) (rp : r > 0)
    (h : ContinuousOn f (closedBall c r)) :
    CircleIntegrable (fun z ↦ (w ^ n / (z - c) ^ n) • ((z - c)⁻¹ • f z)) c r := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.smul ?_ ?_
  · refine continuousOn_const.div ?_ ?_
    · apply Continuous.continuousOn
      fun_prop
    · simp [rp.ne']
  · refine ContinuousOn.smul ?_ ?_
    · apply Continuous.continuousOn
      refine Continuous.inv₀ (by continuity) fun x ↦ circleMap_nz rp
    · refine ContinuousOn.comp h (Continuous.continuousOn (by continuity)) ?_
      intro θ _; exact circleMap_mem_closedBall c (NNReal.coe_nonneg r) θ

theorem cauchy_sub {f g : ℂ → E} {c : ℂ} {r : ℝ≥0} (n : ℕ) (w : ℂ) (rp : r > 0)
    (cf : ContinuousOn f (closedBall c r)) (cg : ContinuousOn g (closedBall c r)) :
    ((cauchyPowerSeries f c r n fun _ ↦ w) - cauchyPowerSeries g c r n fun _ ↦ w) =
      cauchyPowerSeries (f - g) c r n fun _ ↦ w := by
  rw [cauchyPowerSeries_apply f c r n w]
  rw [cauchyPowerSeries_apply g c r n w]
  rw [cauchyPowerSeries_apply (f - g) c r n w]
  set s : ℂ := (2 * π * I)⁻¹
  simp only [div_pow, Pi.sub_apply, smul_sub]
  have fi := cauchy_is_circleIntegrable n w rp cf
  have gi := cauchy_is_circleIntegrable n w rp cg
  have cia := circleIntegral_sub fi gi
  rw [← smul_sub, cia]
  clear cia fi gi cf cg rp
  have flip :
    ((fun z ↦ (w ^ n / (z - c) ^ n) • ((z - c)⁻¹ • f z)) - fun z ↦
        (w ^ n / (z - c) ^ n) • ((z - c)⁻¹ • g z)) =
      fun z ↦ (w ^ n / (z - c) ^ n) • ((z - c)⁻¹ • f z) -
        (w ^ n / (z - c) ^ n) • ((z - c)⁻¹ • g z) :=
    rfl
  simp only [flip]

theorem cauchy_dist {f g : ℂ → E} {c : ℂ} {r : ℝ≥0} {d : ℝ≥0} (n : ℕ) (w : ℂ) (rp : r > 0)
    (cf : ContinuousOn f (closedBall c r)) (cg : ContinuousOn g (closedBall c r))
    (h : ∀ z, z ∈ closedBall c r → ‖f z - g z‖ ≤ d) :
    dist (cauchyPowerSeries f c r n fun _ ↦ w) (cauchyPowerSeries g c r n fun _ ↦ w) ≤
      ‖w‖ ^ n * r⁻¹ ^ n * d := by
  rw [dist_eq_norm, cauchy_sub n w rp cf cg]
  refine cauchy_bound rp ?_; intro z zr; simp at h zr; refine h z zr

variable [CompleteSpace E]

theorem cauchy_on_cball_radius {f : ℂ → E} {z : ℂ} {r : ℝ≥0} (rp : r > 0)
    (h : AnalyticOnNhd ℂ f (closedBall z r)) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f z r) z r := by
  have hd : DifferentiableOn ℂ f (closedBall z r) := by
    intro x H; exact AnalyticAt.differentiableWithinAt (h x H)
  set p : FormalMultilinearSeries ℂ ℂ E := cauchyPowerSeries f z r
  exact DifferentiableOn.hasFPowerSeriesOnBall hd rp

theorem analyticOn_cball_radius {f : ℂ → E} {z : ℂ} {r : ℝ≥0} (rp : r > 0)
    (h : AnalyticOnNhd ℂ f (closedBall z r)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ E, HasFPowerSeriesOnBall f p z r :=
  ⟨cauchyPowerSeries f z r, cauchy_on_cball_radius rp h⟩

theorem analyticOn_ball_radius {f : ℂ → E} {z : ℂ} {r : ℝ≥0} (rp : r > 0)
    (h : AnalyticOnNhd ℂ f (ball z r)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ E, HasFPowerSeriesOnBall f p z r := by
  have h0 := analyticOn_small_cball h (r / 2) (NNReal.half_lt_self <| rp.ne')
  rcases analyticOn_cball_radius (half_pos rp) h0 with ⟨p, ph⟩
  set R := FormalMultilinearSeries.radius p
  refine
    ⟨p, {
        r_le := ?_
        r_pos := ENNReal.coe_pos.mpr rp
        hasSum := ?_ }⟩
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro t tp tr
    have ht := analyticOn_small_cball h t (ENNReal.coe_lt_coe.mp tr)
    rcases analyticOn_cball_radius tp ht with ⟨p', hp'⟩
    have pp : p = p' := HasFPowerSeriesAt.eq_formalMultilinearSeries ⟨↑(r / 2), ph⟩ ⟨t, hp'⟩
    rw [← pp] at hp'
    refine hp'.r_le
  · intro y yr
    rw [Metric.mem_eball] at yr
    rcases exists_between yr with ⟨t, t0, t1⟩
    have t1' : t.toNNReal < r := by
      rw [← WithTop.coe_lt_coe]; exact lt_of_le_of_lt ENNReal.coe_toNNReal_le_self t1
    have ht := analyticOn_small_cball h t.toNNReal t1'
    have tp : 0 < ENNReal.toNNReal t :=
      ENNReal.toNNReal_pos (ne_of_gt <| pos_of_gt t0) (ne_top_of_lt t1)
    rcases analyticOn_cball_radius tp ht with ⟨p', hp'⟩
    have pp : p = p' :=
      HasFPowerSeriesAt.eq_formalMultilinearSeries ⟨↑(r / 2), ph⟩ ⟨t.toNNReal, hp'⟩
    rw [← pp] at hp'
    refine hp'.hasSum ?_
    rw [Metric.mem_eball]
    calc edist y 0
      _ < t := t0
      _ = ↑t.toNNReal := (ENNReal.coe_toNNReal <| ne_top_of_lt t1).symm

/-- Uniform limits of analytic functions are analytic -/
public theorem uniform_analytic_lim {I : Type} [Lattice I] [Nonempty I] {f : I → ℂ → E} {g : ℂ → E}
    {s : Set ℂ} (o : IsOpen s) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (u : TendstoUniformlyOn f g atTop s) : AnalyticOnNhd ℂ g s := by
  intro c hc
  rcases Metric.nhds_basis_closedBall.mem_iff.mp (o.mem_nhds hc) with ⟨r, rp, cb⟩
  lift r to ℝ≥0 using rp.le
  simp only [NNReal.coe_pos] at rp
  have hb : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c r) := fun n ↦ (h n).mono cb
  set pr := fun n ↦ cauchyPowerSeries (f n) c r
  have hpf : ∀ n, HasFPowerSeriesOnBall (f n) (pr n) c r := by
    intro n
    have cs := cauchy_on_cball_radius rp (hb n)
    have pn : pr n = cauchyPowerSeries (f n) c r := rfl
    rw [← pn] at cs; exact cs
  have cfs : ∀ n, ContinuousOn (f n) s := fun n ↦ AnalyticOnNhd.continuousOn (h n)
  have cf : ∀ n, ContinuousOn (f n) (closedBall c r) := fun n ↦ ContinuousOn.mono (cfs n) cb
  have cg : ContinuousOn g (closedBall c r) :=
    ContinuousOn.mono (TendstoUniformlyOn.continuousOn u (.of_forall cfs)) cb
  clear h hb hc o cfs
  set p := cauchyPowerSeries g c r
  refine
    HasFPowerSeriesOnBall.analyticAt
      { r_le := le_radius_cauchyPowerSeries g c r
        r_pos := ENNReal.coe_pos.mpr rp
        hasSum := ?_ }
  intro y yb
  have yr := yb; simp at yr
  set a := ‖y‖ / r
  have a0 : a ≥ 0 := by bound
  have a1 : a < 1 := (div_lt_one (NNReal.coe_pos.mpr rp)).mpr yr
  have a1p : 1 - a > 0 := by bound
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop]
  intro e ep
  generalize d4 : (1 - a) * (e / 4) = d
  have dp : d > 0 := by rw [← d4]; bound
  rcases Filter.eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp u d dp) with ⟨n, hn'⟩
  set hn := hn' n; simp at hn; clear hn' u
  have dfg : dist (f n (c + y)) (g (c + y)) ≤ d := by
    apply le_of_lt; rw [dist_comm]
    refine hn (c + y) ?_
    apply cb
    simp; exact yr.le
  set hs := (hpf n).hasSum yb
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop] at hs
  rcases hs d dp with ⟨N, NM⟩; clear hs
  exists N; intro M NlM
  have dpf := (NM M NlM).le; clear NM NlM N yb
  have dppr : dist (M.sum fun k : ℕ ↦ p k fun _ ↦ y)
      (M.sum fun k : ℕ ↦ pr n k fun _ ↦ y) ≤ e / 4 := by
    trans M.sum fun k : ℕ ↦ dist (p k fun _ ↦ y) (pr n k fun _ ↦ y)
    apply dist_sum_sum_le M (fun k : ℕ ↦ p k fun _ ↦ y) fun k : ℕ ↦ pr n k fun _ ↦ y
    trans M.sum fun k ↦ a ^ k * d
    · apply Finset.sum_le_sum; intro k _
      have hak : a ^ k = ‖y‖ ^ k * r⁻¹ ^ k := by
        calc (‖y‖ / r) ^ k
          _ = (‖y‖ * r⁻¹) ^ k := by rw [div_eq_mul_inv, NNReal.coe_inv]
          _ = ‖y‖ ^ k * r⁻¹ ^ k := mul_pow _ _ _
      rw [hak]
      generalize hd' : d.toNNReal = d'
      have dd : (d' : ℝ) = d := by rw [← hd']; exact Real.coe_toNNReal d dp.le
      have hcb : ∀ z, z ∈ closedBall c r → ‖g z - f n z‖ ≤ d' := by
        intro z zb
        simp only [dist_eq_norm] at hn
        exact le_trans (hn z (cb zb)).le (le_of_eq dd.symm)
      exact _root_.trans (cauchy_dist k y rp cg (cf n) hcb)
        (mul_le_mul_of_nonneg_left (le_of_eq dd) (by bound))
    · have pgb : (M.sum fun k ↦ a ^ k) ≤ (1 - a)⁻¹ := partial_geometric_bound M a0 a1
      calc
        (M.sum fun k ↦ a ^ k * d) = (M.sum fun k ↦ a ^ k) * d := by rw [← Finset.sum_mul]
        _ ≤ (1 - a)⁻¹ * d := by bound
        _ = (1 - a)⁻¹ * ((1 - a) * (e / 4)) := by rw [← d4]
        _ = (1 - a) * (1 - a)⁻¹ * (e / 4) := by ring
        _ = 1 * (e / 4) := by rw [mul_inv_cancel₀ a1p.ne']
        _ = e / 4 := by ring
  generalize hMp : M.sum (fun k : ℕ ↦ p k fun _ ↦ y) = Mp; rw [hMp] at dppr
  generalize hMpr : M.sum (fun k ↦ pr n k fun _ ↦ y) = Mpr; rw [hMpr] at dpf dppr
  calc dist Mp (g (c + y))
    _ ≤ dist Mp (f n (c + y)) + dist (f n (c + y)) (g (c + y)) := dist_triangle _ _ _
    _ ≤ dist Mp Mpr + dist Mpr (f n (c + y)) + d := by bound
    _ ≤ e / 4 + d + d := by bound
    _ = e / 4 + 2 * (1 - a) * (e / 4) := by rw [← d4]; ring
    _ ≤ e / 4 + 2 * (1 - 0) * (e / 4) := by bound
    _ = 3 / 4 * e := by ring
    _ < 1 * e := (mul_lt_mul_of_pos_right (by norm_num) ep)
    _ = e := by simp
