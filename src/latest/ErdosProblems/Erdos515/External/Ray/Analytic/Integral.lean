module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import ErdosProblems.Erdos515.External.Ray.Analytic.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.CauchyIntegral
import ErdosProblems.Erdos515.External.Ray.Analytic.Analytic
import ErdosProblems.Erdos515.External.Ray.Misc.Bound
import ErdosProblems.Erdos515.External.Ray.Misc.Multilinear

/-!
## Integrals of analytic functions are analytic

We consider a function `f : X → ℂ → E` which is continuous on a complex `s : Set X` and analytic
for `z ∈ closedBall c r`. Interchanging the order of integration shows that the integral is
analytic.
-/

open Classical
open Function (uncurry)
open MeasureTheory
open Metric (ball closedBall)
open Set
open scoped NNReal Real
noncomputable section

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [FirstCountableTopology X] [T2Space X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {f : X → ℂ → E} {μ : Measure X} {s : Set X} {c : ℂ} {r : ℝ≥0}
variable {x : X} {z : ℂ} {p : X × ℂ} {n : ℕ} {t : ℝ}

/-- Our various assumptions -/
structure Holo [CompleteSpace E] [OpensMeasurableSpace X] [FirstCountableTopology X] [T2Space X]
    (f : X → ℂ → E) (μ : Measure X) (s : Set X) (c : ℂ) (r : ℝ≥0) : Prop where
  r0 : 0 < r
  sc : IsCompact s
  μs : μ s ≠ ⊤
  fc : ContinuousOn (uncurry f) (s ×ˢ closedBall c r)
  fd : ∀ x ∈ s, ∀ z ∈ ball c r, DifferentiableAt ℂ (f x) z

namespace Holo

attribute [bound_forward] Holo.r0
attribute [aesop (rule_sets := [finiteness]) safe forward] Holo.μs

lemma sm (i : Holo f μ s c r) : MeasurableSet s :=
  i.sc.measurableSet

/-- Our power series is the `cauchyPowerSeries`, integrated over `s` -/
def series (_ : Holo f μ s c r) : FormalMultilinearSeries ℂ ℂ E :=
  fun n ↦ ∫ x in s, cauchyPowerSeries (f x) c r n ∂μ

-- `f` is uniformly bounded
lemma pc (i : Holo f μ s c r) : IsCompact (s ×ˢ closedBall c r) :=
  i.sc.prod (isCompact_closedBall _ _)
lemma bounded (i : Holo f μ s c r) : ∃ C, ∀ x ∈ s ×ˢ closedBall c r, ‖uncurry f x‖ ≤ C :=
  i.pc.exists_bound_of_continuousOn i.fc
def C (i : Holo f μ s c r) : ℝ := choose i.bounded
def le_C (i : Holo f μ s c r) (m : p ∈ s ×ˢ closedBall c r) : ‖uncurry f p‖ ≤ i.C :=
  choose_spec i.bounded _ m
def le_C' (i : Holo f μ s c r) (xs : x ∈ s) (zm : z ∈ closedBall c r) : ‖f x z‖ ≤ i.C :=
  i.le_C (p := (x, z)) ⟨xs, zm⟩
@[bound] def comp_le_C (i : Holo f μ s c r) (xs : x ∈ s) : ‖f x (circleMap c r t)‖ ≤ i.C :=
  i.le_C' xs (by simp [circleMap])

/-- The inner cauchy series is bounded -/
@[bound] lemma norm_cauchyPowerSeries_le (i : Holo f μ s c r) (xm : x ∈ s) :
    ‖cauchyPowerSeries (f x) c r n‖ ≤ i.C * r⁻¹ ^ n := by
  have le : ‖∫ t in 0..2 * π, ‖f x (circleMap c r t)‖‖ ≤ i.C * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x m ↦ ?_
    simp only [norm_norm]
    apply i.le_C' xm
    simp only [Metric.mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
      NNReal.abs_eq, le_refl]
  simp only [Real.norm_eq_abs, sub_zero, abs_of_pos Real.two_pi_pos, mul_comm i.C] at le
  rw [abs_of_nonneg (intervalIntegral.integral_nonneg (by bound) (by bound))] at le
  refine le_trans (_root_.norm_cauchyPowerSeries_le _ _ _ _) ?_
  rw [abs_of_pos (by bound), NNReal.coe_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by bound)
  rwa [inv_mul_le_iff₀ (by bound)]

/-- Our series is bounded -/
@[bound] lemma norm_series_le (i : Holo f μ s c r) : ‖i.series n‖ ≤ i.C * r⁻¹ ^ n * μ.real s :=
  norm_setIntegral_le_of_norm_le_const (by finiteness) (C := i.C * r⁻¹ ^ n)
    (fun _ m ↦ i.norm_cauchyPowerSeries_le m)

/-- Our series has nice radius of convergence -/
lemma le_radius_series (i : Holo f μ s c r) : r ≤ i.series.radius := by
  refine FormalMultilinearSeries.le_radius_of_bound _ (C := i.C * μ.real s) fun n ↦ ?_
  calc ‖i.series n‖ * r ^ n
    _ ≤ i.C * r⁻¹ ^ n * μ.real s * r ^ n := by bound
    _ = i.C * μ.real s * (r / r) ^ n := by simp only [NNReal.coe_inv, inv_pow]; ring
    _ = i.C * μ.real s := by rw [div_self (ne_of_gt (by bound)), one_pow, mul_one]

lemma diffContOnCl (i : Holo f μ s c r) (xs : x ∈ s) : DiffContOnCl ℂ (f x) (ball c r) where
  differentiableOn := fun z zm ↦ (i.fd x xs z zm).differentiableWithinAt
  continuousOn := by
    rw [closure_ball]
    · exact i.fc.uncurry_left x xs
    · exact ne_of_gt (by bound)

/-- The inner Cauchy integral is continuous in `x` -/
lemma continuousOn_cauchy_integral (i : Holo f μ s c r) :
    ContinuousOn (fun x ↦ ∮ (z : ℂ) in C(c, ↑r), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f x z) s := by
  simp only [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  set g : X → ℝ → E := fun x t ↦ deriv (circleMap c r) t • (circleMap c r t - c)⁻¹ ^ n •
      (circleMap c r t - c)⁻¹ • f x (circleMap c r t)
  have ic : ContinuousOn (fun p : X × ℝ ↦ g p.1 p.2) (s ×ˢ univ) := by
    simp only [g, deriv_circleMap, circleMap_sub_center, circleMap_zero_inv, smul_smul]
    apply ContinuousOn.smul
    · fun_prop
    · have e : (fun p : X × ℝ ↦ f p.1 (circleMap c r p.2)) =
        uncurry f ∘ fun p : X × ℝ ↦ (p.1, circleMap c r p.2) := rfl
      rw [e]
      refine i.fc.comp (by fun_prop) ?_
      intro p ⟨ps, _⟩
      simp [circleMap, ps]
  apply MeasureTheory.continuousOn_of_dominated (bound := fun _ ↦ r * ((r ^ n)⁻¹ * (r⁻¹ * i.C)))
  · intro x xs
    apply Continuous.aestronglyMeasurable
    rw [← continuousOn_univ]
    exact ContinuousOn.uncurry_left (f := g) x xs ic
  · intro x xs
    refine ae_of_all _ fun t ↦ ?_
    simp only [deriv_circleMap, circleMap_sub_center, inv_pow, norm_smul, Complex.norm_mul,
      norm_circleMap_zero, NNReal.abs_eq, Complex.norm_I, mul_one, norm_inv, norm_pow,
      NNReal.coe_inv, NNReal.coe_pow]
    bound
  · exact integrableOn_const (by simpa using not_eq_of_beq_eq_false rfl)
  · refine ae_of_all _ fun t ↦ ?_
    exact ContinuousOn.uncurry_right (f := g) t (mem_univ _) ic

/-- Applying our Cauchy power series is continuous in `x` -/
lemma continuousOn_cauchyPowerSeries_apply (i : Holo f μ s c r) {y : ℂ} :
    ContinuousOn (fun x ↦ (cauchyPowerSeries (f x) c r n) fun _ ↦ y) s := by
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_smul (y ^ n)]
  exact continuousOn_const.smul i.continuousOn_cauchy_integral

/-- The inner power series is integral w.r.t. `x` -/
lemma integrableOn_cauchyPowerSeries (i : Holo f μ s c r) :
    IntegrableOn (fun x ↦ cauchyPowerSeries (f x) c r n) s μ := by
  apply IntegrableOn.of_bound (by finiteness) (C := i.C * r⁻¹ ^ n)
  · refine ContinuousOn.aestronglyMeasurable_of_isCompact ?_ i.sc i.sm
    exact ContinuousMultilinearMap.continuous_mkPiRing.comp_continuousOn
      (continuousOn_const.smul i.continuousOn_cauchy_integral)
  · exact ae_restrict_of_forall_mem i.sm fun x xs ↦ i.norm_cauchyPowerSeries_le xs

@[bound] lemma norm_cauchyPowerSeries_apply_le (i : Holo f μ s c r) (xs : x ∈ s) {y : ℂ} :
    ‖(cauchyPowerSeries (f x) c r n) fun _ ↦ y‖ ≤ i.C * r⁻¹ ^ n * ‖y‖ ^ n := by
  refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  bound

/-- The inner power series is integrable, when applied -/
lemma integrableOn_cauchyPowerSeries_apply (i : Holo f μ s c r) {y : ℂ} :
    IntegrableOn (fun x ↦ cauchyPowerSeries (f x) c r n fun _ ↦ y) s μ := by
  apply IntegrableOn.of_bound (by finiteness) (C := i.C * r⁻¹ ^ n * ‖y‖ ^ n)
  · refine ContinuousOn.aestronglyMeasurable_of_isCompact ?_ i.sc i.sm
    simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, smul_smul (y ^ n)]
    exact continuousOn_const.smul i.continuousOn_cauchy_integral
  · exact ae_restrict_of_forall_mem i.sm fun x xs ↦ by bound

lemma summable_cauchyPowerSeries_apply (i : Holo f μ s c r) {y : ℂ} (yr : ‖y‖ < r) :
    Summable fun n ↦ ∫ x in s, ‖(cauchyPowerSeries (f x) c r n) fun _ ↦ y‖ ∂μ := by
  apply Summable.of_norm_bounded (g := fun n ↦ i.C * r⁻¹ ^ n * ‖y‖ ^ n * μ.real s)
  · simp only [← mul_assoc, mul_comm _ (μ.real s)]
    simp only [mul_assoc _ _ (‖y‖ ^ _), ← mul_pow, NNReal.coe_inv, ← div_eq_inv_mul]
    exact (summable_geometric_of_lt_one (by bound) (by bound)).mul_left _
  · intro n
    refine norm_setIntegral_le_of_norm_le_const (by finiteness) fun x xs ↦ ?_
    simp only [norm_norm]
    bound

/-- Integrals of analytic functions are analytic -/
theorem hasFPowerSeriesOnBall_integral (i : Holo f μ s c r) :
    HasFPowerSeriesOnBall (fun z ↦ ∫ x in s, f x z ∂μ) i.series c r where
  r_le := i.le_radius_series
  r_pos := by bound
  hasSum := by
    intro y ym
    have hp : ∀ x ∈ s, HasFPowerSeriesOnBall (f x) (cauchyPowerSeries (f x) c r) c r :=
      fun _ xs ↦ (i.diffContOnCl xs).hasFPowerSeriesOnBall i.r0
    have hs := fun x xs ↦ (hp x xs).hasSum ym
    set a : X → ℕ → E := fun x n ↦ cauchyPowerSeries (f x) c r n fun _ ↦ y
    have e : EqOn (fun x ↦ f x (c + y)) (fun x ↦ ∑' n, a x n) s :=
      fun x xs ↦ (hs x xs).tsum_eq.symm
    rw [setIntegral_congr_fun i.sm e]
    simp only [series, ContinuousMultilinearMap.integral_apply i.integrableOn_cauchyPowerSeries]
    apply MeasureTheory.hasSum_integral_of_summable_integral_norm
    · exact fun _ ↦ i.integrableOn_cauchyPowerSeries_apply
    · simp only [Metric.eball_coe, Metric.mem_ball, dist_zero_right] at ym
      exact i.summable_cauchyPowerSeries_apply ym

end Holo

/-!
### Standalone theorem statements
-/

/-- Well-behaved integrals of analytic functions are analytic, ball version -/
theorem AnalyticOnNhd.integral_ball {r : ℝ} (fc : ContinuousOn (uncurry f) (s ×ˢ closedBall c r))
    (fd : ∀ x ∈ s, ∀ z ∈ ball c r, DifferentiableAt ℂ (f x) z) (r0 : 0 < r) (sc : IsCompact s)
    (μs : μ s ≠ ⊤ := by finiteness) : AnalyticOnNhd ℂ (fun z ↦ ∫ x in s, f x z ∂μ) (ball c r) := by
  set r' : ℝ≥0 := ⟨r, r0.le⟩
  set i : Holo f μ s c r' := ⟨r0, sc, μs, fc, fd⟩
  have e : ball c r = Metric.eball c r' := by rw [Metric.eball_coe]; rfl
  rw [e]
  exact i.hasFPowerSeriesOnBall_integral.analyticOnNhd

/-- Well-behaved integrals of analytic functions are analytic, general set version -/
public theorem AnalyticOnNhd.integral {t : Set ℂ} (fc : ContinuousOn (uncurry f) (s ×ˢ t))
    (fa : ∀ x ∈ s, AnalyticOnNhd ℂ (f x) t) (sc : IsCompact s) (μs : μ s ≠ ⊤ := by finiteness)
    (ot : IsOpen t) : AnalyticOnNhd ℂ (fun z ↦ ∫ x in s, f x z ∂μ) t := by
  intro c ct
  obtain ⟨r,r0,rt⟩ := Metric.isOpen_iff.mp ot c ct
  have ia := AnalyticOnNhd.integral_ball (f := f) (c := c) (r := r / 2) ?_ ?_ (by bound) sc
  · exact ia _ (by simp [r0])
  · exact fc.mono (prod_mono_right (subset_trans (Metric.closedBall_subset_ball (by bound)) rt))
  · intro x xs z m
    refine (fa x xs z (rt ?_)).differentiableAt
    simp only [Metric.mem_ball] at m ⊢
    linarith
