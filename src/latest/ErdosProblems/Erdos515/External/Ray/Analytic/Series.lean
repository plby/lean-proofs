module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Stream.Init
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import ErdosProblems.Erdos515.External.Ray.Analytic.Analytic
import ErdosProblems.Erdos515.External.Ray.Analytic.Uniform
import ErdosProblems.Erdos515.External.Ray.Misc.Bounds
import ErdosProblems.Erdos515.External.Ray.Misc.Finset

/-!
## Infinite series of analytic functions

Uniformly convergent series of analytic functions have analytic limits.
-/

open Complex
open Filter (atTop)
open Metric (ball closedBall sphere)
open scoped Real NNReal ENNReal Topology symmDiff
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type} [NormedAddCommGroup G]

/-- Summability restricted to sets -/
@[expose] public def SummableOn (f : ℕ → ℂ → E) (s : Set ℂ) :=
  ∀ z, z ∈ s → Summable fun n ↦ f n z

/-- `n ↦ f n z` has a convergent sum for each `z ∈ s` -/
@[expose] public def HasSumOn (f : ℕ → ℂ → E) (g : ℂ → E) (s : Set ℂ) :=
  ∀ z, z ∈ s → HasSum (fun n ↦ f n z) (g z)

/-- The parameterized limit of an infinite sum, if it exists -/
@[expose] public noncomputable def tsumOn (f : ℕ → ℂ → E) := fun z ↦ tsum fun n ↦ f n z

/-- Uniform convergence of sums on a set -/
@[expose] public def HasUniformSum (f : ℕ → ℂ → E) (g : ℂ → E) (s : Set ℂ) :=
  TendstoUniformlyOn (fun (N : Finset ℕ) z ↦ N.sum fun n ↦ f n z) g atTop s

/-- Uniform vanishing means late sums are uniformly small -/
def UniformVanishing (f : ℕ → ℂ → E) (s : Set ℂ) :=
  ∀ e : ℝ, e > 0 → ∃ n : ℕ, ∀ (N : Finset ℕ) (z), Late N n → z ∈ s → (N.sum fun n ↦ ‖f n z‖) < e

/-- Uniformly vanishing series results in uniform Cauchy sequences of finite sums -/
theorem uniformVanishing_to_uniform_cauchy_series {f : ℕ → ℂ → G} {s : Set ℂ}
    (h : UniformVanishing f s) :
    UniformCauchySeqOn (fun (N : Finset ℕ) z ↦ N.sum fun n ↦ f n z) atTop s := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro e ep
  rcases h e ep with ⟨m, hm⟩
  use Finset.range m
  intro A HA B HB z zs
  calc dist (A.sum fun n ↦ f n z) (B.sum fun n ↦ f n z)
    _ ≤ (A ∆ B).sum fun n ↦ ‖f n z‖ := symmDiff_bound _ _ _
    _ < e := hm (A ∆ B) z (symmDiff_late HA HB) zs

/-- Geometric bounds with c ≤ 0 are degenerate -/
theorem CNonpos.degenerate {f : ℕ → ℂ → G} {s : Set ℂ} {c a : ℝ} (c0 : c ≤ 0) (a0 : 0 ≤ a)
    (hf : ∀ n z, z ∈ s → ‖f n z‖ ≤ c * a ^ n) : ∀ n z, z ∈ s → f n z = 0 := by
  intro n z zs; specialize hf n z zs
  have ca : c * a ^ n ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨c0, by bound⟩)
  exact norm_eq_zero.mp (le_antisymm (le_trans hf ca) (norm_nonneg _))

/-- Adding one more term to a sum adds it, `Stream'.get` version to keep terms type-correct
    at low transparency -/
theorem sum_cons_get {a t : G} {q : Stream' G} (h : HasSum q.get t) :
    HasSum (Stream'.cons a q).get (a + t) := by
  rw [HasSum] at h ⊢
  have ha := Filter.Tendsto.comp (Continuous.tendsto (continuous_const_add a) t) h
  have s : ((fun z ↦ a + z) ∘ fun N : Finset ℕ ↦ N.sum q.get) =
      (fun N : Finset ℕ ↦ N.sum (Stream'.cons a q).get) ∘ push := by
    apply funext; intro N
    simp only [Function.comp_apply]
    exact push_sum_get
  rw [s] at ha
  exact tendsto_comp_push.mp ha

/-- Adding one more term to a sum adds it -/
theorem sum_cons {a g : G} {f : ℕ → G} (h : HasSum f g) :
    HasSum (Stream'.cons a f) (a + g) :=
  sum_cons_get (q := f) h

/-- Adding one more term to a sum adds it (`tprod` version) -/
lemma sum_cons' {a : G} {f : ℕ → G} (h : Summable f) :
    tsum (Stream'.cons a f) = a + tsum f := by
  rcases h with ⟨g, h⟩; rw [HasSum.tsum_eq h]; exact HasSum.tsum_eq (sum_cons h)

/-- Dropping the first term subtracts it -/
public lemma sum_drop {f : ℕ → G} {g : G} (h : HasSum f g) :
    HasSum (fun n ↦ f (n + 1)) (g - f 0) := by
  rw [hasSum_nat_add_iff (f := f) 1]
  simpa using h

/-- Dropping the first term subtracts it (`tsum` version) -/
public lemma tsum_drop {f : ℕ → G} (h : Summable f) :
    ∑' n, f n = f 0 + ∑' n, f (n + 1) := by
  rw [(sum_drop h.hasSum).tsum_eq, add_sub_cancel]

variable [CompleteSpace E] [CompleteSpace G]

/-- Uniformly vanishing series are summable -/
theorem uniformVanishing_to_summable {f : ℕ → ℂ → G} {s : Set ℂ} {z : ℂ} (zs : z ∈ s)
    (h : UniformVanishing f s) : Summable fun n ↦ f n z := by
  rw [summable_iff_vanishing_norm]; intro e ep
  rcases h e ep with ⟨m, hm⟩
  use Finset.range m; intro A d
  calc ‖A.sum (fun n ↦ f n z)‖
    _ ≤ A.sum (fun n ↦ ‖f n z‖) := by bound
    _ < e := hm _ _ (late_iff_disjoint_range.mpr d) zs

/-- If a series is uniformly vanishing, it tends to its limit uniformly -/
theorem uniformVanishing_to_tendsto_uniformly_on {f : ℕ → ℂ → G} {s : Set ℂ}
    (h : UniformVanishing f s) : HasUniformSum f (tsumOn f) s := by
  rw [HasUniformSum, Metric.tendstoUniformlyOn_iff]
  intro e ep
  rcases h (e / 4) (by linarith) with ⟨m, hm⟩
  rw [Filter.eventually_atTop]
  use Finset.range m
  intro N Nm z zs
  rw [tsumOn]
  generalize G : tsum (fun n ↦ f n z) = g
  have S : Summable (fun n ↦ f n z) := uniformVanishing_to_summable zs h
  have GS : HasSum (fun n ↦ f n z) g := by rw [← G]; exact Summable.hasSum S
  clear S
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop] at GS
  rcases GS (e / 4) (by linarith) with ⟨M, HM⟩; clear GS G h
  set A := N ∪ M \ N
  have AM : M ⊆ A := subset_union_sdiff _ _
  simp only [gt_iff_lt] at HM
  specialize HM A AM
  rw [dist_comm] at HM
  calc dist g (N.sum fun n ↦ f n z)
    _ ≤ dist g (A.sum fun n ↦ f n z) + dist (A.sum fun n ↦ f n z) (N.sum fun n ↦ f n z) := by bound
    _ ≤ e / 4 + dist (A.sum fun n ↦ f n z) (N.sum fun n ↦ f n z) := by linarith
    _ = e / 4 + dist ((N.sum fun n ↦ f n z) + (M \ N).sum fun n ↦ f n z)
        (N.sum fun n ↦ f n z) := by rw [Finset.sum_union Finset.disjoint_sdiff]
    _ = e / 4 + ‖((N.sum fun n ↦ f n z) + (M \ N).sum fun n ↦ f n z) -
        N.sum fun n ↦ f n z‖ := by rw [dist_eq_norm]
    _ = e / 4 + ‖(M \ N).sum fun n ↦ f n z‖ := by rw [add_sub_cancel_left]
    _ ≤ e / 4 + (M \ N).sum fun n ↦ ‖f n z‖ := by
      linarith [finset_norm_sum_le (M \ N) fun n ↦ f n z]
    _ ≤ e / 4 + e / 4 := by linarith [hm (M \ N) z (sdiff_late M Nm) zs]
    _ = e / 2 := by ring
    _ < e := by linarith

/-- Uniformly exponentially converging series converge uniformly -/
theorem fast_series_converge_uniformly_on {f : ℕ → ℂ → G} {s : Set ℂ} {c a : ℝ} (a0 : 0 ≤ a)
    (a1 : a < 1) (hf : ∀ n z, z ∈ s → ‖f n z‖ ≤ c * a ^ n) : HasUniformSum f (tsumOn f) s := by
  by_cases c0 : c ≤ 0
  · have fz := CNonpos.degenerate c0 a0 hf
    rw [HasUniformSum, Metric.tendstoUniformlyOn_iff]
    intro e ep; refine .of_forall ?_; intro n z zs
    rw [tsumOn]
    simp_rw [fz _ z zs]
    simp only [tsum_zero, Finset.sum_const_zero, dist_zero_left, norm_zero]
    assumption
  · simp only [not_le] at c0
    apply uniformVanishing_to_tendsto_uniformly_on
    intro e ep
    set t := (1 - ↑a) / ↑c * (e / 2)
    have tp : t > 0 := by bound
    rcases exists_pow_lt_of_lt_one tp a1 with ⟨n, nt⟩
    use n; intro N z NL zs
    have a1p : 1 - (a : ℝ) > 0 := by linarith
    calc (N.sum fun n ↦ ‖f n z‖)
      _ ≤ N.sum fun n ↦ c * a ^ n := Finset.sum_le_sum fun n _ ↦ hf n z zs
      _ = c * N.sum fun n ↦ a ^ n := (Finset.mul_sum _ _ _).symm
      _ ≤ c * (a ^ n * (1 - a)⁻¹) := by bound [late_geometric_bound NL a0 a1]
      _ = a ^ n * (c * (1 - a)⁻¹) := by ring
      _ ≤ t * (c * (1 - a)⁻¹) := by bound
      _ = (1 - a) / c * (e / 2) * (c * (1 - a)⁻¹) := rfl
      _ = (1 - a) * (1 - a)⁻¹ * (c / c) * (e / 2) := by ring
      _ = 1 * 1 * (e / 2) := by rw [mul_inv_cancel₀ a1p.ne', div_self c0.ne']
      _ = e / 2 := by ring
      _ < e := by linarith

/-- Exponentially converging series converge -/
theorem fast_series_converge_at {f : ℕ → G} {c a : ℝ} (a0 : 0 ≤ a) (a1 : a < 1)
    (hf : ∀ n, ‖f n‖ ≤ c * a ^ n) : Summable f := by
  set s : Set ℂ := {0}
  set g : ℕ → ℂ → G := fun n _ ↦ f n
  have hg : ∀ n z, z ∈ s → ‖g n z‖ ≤ c * a ^ n := fun n z _ ↦ hf n
  have u := fast_series_converge_uniformly_on a0 a1 hg
  rw [HasUniformSum] at u
  rw [tendstoUniformlyOn_singleton_iff_tendsto] at u
  apply HasSum.summable; assumption

/-- Analytic series that converge exponentially converge to analytic functions -/
public theorem fast_series_converge {f : ℕ → ℂ → E} {s : Set ℂ} {c a : ℝ} (o : IsOpen s)
    (a0 : 0 ≤ a) (a1 : a < 1) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (hf : ∀ n z, z ∈ s → ‖f n z‖ ≤ c * a ^ n) :
    ∃ g : ℂ → E, AnalyticOnNhd ℂ g s ∧ HasSumOn f g s := by
  use tsumOn f; constructor
  · exact uniform_analytic_lim o (fun N ↦ N.analyticOnNhd_fun_sum fun _ _ ↦ h _)
      (fast_series_converge_uniformly_on a0 a1 hf)
  · exact fun z zs ↦ Summable.hasSum (fast_series_converge_at a0 a1 fun n ↦ hf n z zs)

/-- Analytic series that converge exponentially converge to analytic functions, tsum version -/
public theorem fast_series_converge_tsum_at {f : ℕ → ℂ → E} {s : Set ℂ} {c a : ℝ} (o : IsOpen s)
    (a0 : 0 ≤ a) (a1 : a < 1) (h : ∀ n, AnalyticOnNhd ℂ (f n) s)
    (hf : ∀ n z, z ∈ s → ‖f n z‖ ≤ c * a ^ n) :
    AnalyticOnNhd ℂ (fun z ↦ ∑' n, f n z) s := by
  obtain ⟨g, ga, gs⟩ := fast_series_converge o a0 a1 h hf
  rwa [analyticOnNhd_congr (g := g) o]
  intro z m
  simp only [(gs z m).tsum_eq]
