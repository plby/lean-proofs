/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 516.
https://www.erdosproblems.com/forum/thread/516

Informal authors:
- W. H. J. Fuchs

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos516.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/516.lean
-/
/-
This file formalizes the affirmative resolution of Erdős Problem 516.

Informal author:
- W. H. J. Fuchs

Formal author:
- OpenAI Codex

Reference:
W. H. J. Fuchs, "Proof of a conjecture of G. Pólya concerning gap series",
Illinois J. Math. 7 (1963), 661--667.
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.CompareExp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic
import ErdosProblems.Erdos516.Check516

open scoped Nat Polynomial
open Filter MeasureTheory Real Set Topology

namespace Erdos516

/-- A strictly increasing sequence `n` has Fabry gaps when `n k / k → ∞`. -/
def HasFabryGaps (n : ℕ → ℕ) : Prop :=
  StrictMono n ∧ Tendsto (fun k => n k / (k : ℝ)) atTop atTop

/-- The growth condition used for finite-order entire maps. -/
def OfFiniteOrder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E → F) : Prop :=
  Differentiable ℂ f ∧ ∃ c ≥ 0, ∃ a ≥ 0, ∀ z, ‖f z‖ ≤ c * rexp (‖z‖ ^ a)

/-- The logarithmic minimum-to-maximum modulus ratio on the circle of radius `r`. -/
noncomputable def ratio (r : ℝ) (f : ℂ → ℂ) : ℝ :=
  (⨅ z : {z : ℂ // ‖z‖ = r}, ‖f z‖).log /
    (⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖).log

private noncomputable def minModulus (r : ℝ) (f : ℂ → ℂ) : ℝ :=
  ⨅ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

private noncomputable def maxModulus (r : ℝ) (f : ℂ → ℂ) : ℝ :=
  ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

private lemma ratio_eq (r : ℝ) (f : ℂ → ℂ) :
    ratio r f = (minModulus r f).log / (maxModulus r f).log := rfl

private lemma circle_nonempty {r : ℝ} (hr : 0 ≤ r) :
    Nonempty {z : ℂ // ‖z‖ = r} := by
  exact ⟨⟨(r : ℂ), by simp [Real.norm_eq_abs, abs_of_nonneg hr]⟩⟩

private lemma maxModulus_bddAbove {f : ℂ → ℂ} {r c : ℝ} {a : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * rexp (‖z‖ ^ a)) :
    BddAbove (Set.range fun z : {z : ℂ // ‖z‖ = r} ↦ ‖f z‖) := by
  refine ⟨c * rexp (r ^ a), ?_⟩
  rintro _ ⟨z, rfl⟩
  calc
    ‖f z‖ ≤ c * rexp (‖(z : ℂ)‖ ^ a) := hbound z
    _ = c * rexp (r ^ a) := by rw [z.property]

/-- The circle supremum controls the whole enclosed disk. -/
private lemma norm_le_maxModulus_of_norm_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c R : ℝ} {a : ℕ} (hbound : ∀ z, ‖f z‖ ≤ c * rexp (‖z‖ ^ a))
    (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖f z‖ ≤ maxModulus R f := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.ball (0 : ℂ) R) Metric.isBounded_ball hf.diffContOnCl ?_ ?_
  · intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    have hwR : ‖w‖ = R := by simpa [Metric.mem_sphere] using hw
    exact le_ciSup (maxModulus_bddAbove hbound)
      (⟨w, hwR⟩ : {u : ℂ // ‖u‖ = R})
  · rw [closure_ball 0 hR.ne']
    simpa [Metric.mem_closedBall] using hz

private lemma minModulus_nonneg {f : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ minModulus r f := by
  let := circle_nonempty hr
  exact le_ciInf fun z ↦ norm_nonneg (f z)

private lemma minModulus_le_maxModulus {f : ℂ → ℂ} {r c : ℝ} {a : ℕ} (hr : 0 ≤ r)
    (hbound : ∀ z, ‖f z‖ ≤ c * rexp (‖z‖ ^ a)) :
    minModulus r f ≤ maxModulus r f := by
  let := circle_nonempty hr
  let z : {z : ℂ // ‖z‖ = r} := ⟨(r : ℂ), by simp [Real.norm_eq_abs, abs_of_nonneg hr]⟩
  calc
    minModulus r f ≤ ‖f z‖ := ciInf_le (by exact ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg (f w)⟩) z
    _ ≤ maxModulus r f := le_ciSup (maxModulus_bddAbove hbound) z

private lemma ratio_le_one_of_one_lt_maxModulus {f : ℂ → ℂ} {r c : ℝ} {a : ℕ} (hr : 0 ≤ r)
    (hbound : ∀ z, ‖f z‖ ≤ c * rexp (‖z‖ ^ a))
    (hmax : 1 < maxModulus r f) : ratio r f ≤ 1 := by
  rw [ratio_eq]
  have hden : 0 < (maxModulus r f).log := Real.log_pos hmax
  rw [div_le_one hden]
  by_cases hmin : minModulus r f = 0
  · simp [hmin, hden.le]
  · have hminpos : 0 < minModulus r f := lt_of_le_of_ne (minModulus_nonneg hr) (Ne.symm hmin)
    exact Real.strictMonoOn_log.monotoneOn hminpos (lt_trans zero_lt_one hmax)
      (minModulus_le_maxModulus hr hbound)

/-- A gap series with every displayed coefficient nonzero cannot be constant. -/
private lemma not_constant_of_gap_series {f : ℂ → ℂ} {n : ℕ → ℕ} (hn : StrictMono n)
    {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z)) :
    ¬ ∃ c, f = Function.const ℂ c := by
  classical
  let b : ℕ → ℂ := Function.extend n a 0
  have hsum : ∀ z, HasSum (fun m ↦ b m * z ^ m) (f z) := by
    intro z
    have hext : Function.extend n (fun k ↦ a k * z ^ n k) 0 =
        fun m ↦ b m * z ^ m := by
      funext m
      by_cases hm : ∃ k, n k = m
      · obtain ⟨k, rfl⟩ := hm
        simp [b, hn.injective.extend_apply]
      · simp [b, Function.extend_apply' _ _ _ hm]
    rw [← hext]
    exact (hasSum_extend_zero hn.injective).2 (hfn z)
  have hp : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ b) 0 := by
    rw [hasFPowerSeriesAt_iff]
    exact Filter.Eventually.of_forall fun z ↦ by
      simpa [FormalMultilinearSeries.coeff_ofScalars, mul_comm] using hsum z
  rintro ⟨c, hc⟩
  have hpc : HasFPowerSeriesAt f (constFormalMultilinearSeries ℂ ℂ c) 0 := by
    rw [hc]
    exact hasFPowerSeriesAt_const
  have heq := hp.eq_formalMultilinearSeries hpc
  have hcoeff := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff (n 1)) heq
  have hn1 : n 1 ≠ 0 := Nat.ne_of_gt ((Nat.zero_le (n 0)).trans_lt (hn Nat.zero_lt_one))
  have hconstzero : (constFormalMultilinearSeries ℂ ℂ c).coeff (n 1) = 0 :=
    FormalMultilinearSeries.coeff_eq_zero.2
      (constFormalMultilinearSeries_apply_of_nonzero hn1)
  have hbzero : b (n 1) = 0 := by
    simpa [FormalMultilinearSeries.coeff_ofScalars] using hcoeff.trans hconstzero
  change Function.extend n a 0 (n 1) = 0 at hbzero
  rw [hn.injective.extend_apply] at hbzero
  exact ha 1 hbzero

/-- Pull an entire function back along the exponential map. -/
private noncomputable def logLift (f : ℂ → ℂ) (w : ℂ) : ℂ := f (Complex.exp w)

private lemma logLift_hasSum {f : ℂ → ℂ} {n : ℕ → ℕ} {a : ℕ → ℂ}
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z)) (w : ℂ) :
    HasSum (fun k ↦ a k * Complex.exp ((n k : ℂ) * w)) (logLift f w) := by
  convert hfn (Complex.exp w) using 1
  · funext k
    rw [Complex.exp_nat_mul]
  · rfl

private lemma logLift_periodic (f : ℂ → ℂ) :
    Function.Periodic (logLift f) (2 * (Real.pi : ℂ) * Complex.I) := by
  intro w
  exact congrArg f (Complex.exp_periodic w)

private lemma logLift_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (logLift f) :=
  hf.comp Complex.differentiable_exp

private lemma logLift_growth {f : ℂ → ℂ} {c : ℝ} {A : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * rexp (‖z‖ ^ A)) (w : ℂ) :
    ‖logLift f w‖ ≤ c * rexp ((Real.exp w.re) ^ A) := by
  simpa only [logLift, Complex.norm_exp] using hbound (Complex.exp w)

private lemma circle_logLift_ranges (f : ℂ → ℂ) (σ : ℝ) :
    Set.range (fun z : {z : ℂ // ‖z‖ = Real.exp σ} ↦ ‖f z‖) =
      Set.range (fun t : ℝ ↦ ‖logLift f (σ + t * Complex.I)‖) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z.1.arg, ?_⟩
    change ‖f (Complex.exp (σ + (z.1.arg : ℂ) * Complex.I))‖ = ‖f z.1‖
    congr 2
    rw [Complex.exp_add]
    calc
      Complex.exp (σ : ℂ) * Complex.exp ((z.1.arg : ℂ) * Complex.I)
          = (‖z.1‖ : ℂ) * Complex.exp ((z.1.arg : ℂ) * Complex.I) := by
              rw [← Complex.ofReal_exp, z.2]
      _ = z.1 := Complex.norm_mul_exp_arg_mul_I z.1
  · rintro ⟨t, rfl⟩
    refine ⟨⟨Complex.exp (σ + t * Complex.I), ?_⟩, rfl⟩
    rw [Complex.norm_exp]
    simp

private lemma minModulus_exp_eq_logLift (f : ℂ → ℂ) (σ : ℝ) :
    minModulus (Real.exp σ) f = ⨅ t : ℝ, ‖logLift f (σ + t * Complex.I)‖ := by
  rw [minModulus, ← sInf_range, ← sInf_range, circle_logLift_ranges]

private lemma maxModulus_exp_eq_logLift (f : ℂ → ℂ) (σ : ℝ) :
    maxModulus (Real.exp σ) f = ⨆ t : ℝ, ‖logLift f (σ + t * Complex.I)‖ := by
  rw [maxModulus, ← sSup_range, ← sSup_range, circle_logLift_ranges]

private noncomputable def verticalRatio (F : ℂ → ℂ) (σ : ℝ) : ℝ :=
  (⨅ t : ℝ, ‖F (σ + t * Complex.I)‖).log /
    (⨆ t : ℝ, ‖F (σ + t * Complex.I)‖).log

private lemma ratio_exp_eq_verticalRatio (f : ℂ → ℂ) (σ : ℝ) :
    ratio (Real.exp σ) f = verticalRatio (logLift f) σ := by
  rw [ratio_eq, verticalRatio, minModulus_exp_eq_logLift, maxModulus_exp_eq_logLift]

private def HasVerticalGoodLines (F : ℂ → ℂ) : Prop :=
  ∀ y < (1 : ℝ), ∃ᶠ σ : ℝ in atTop, y < verticalRatio F σ

private lemma verticalRatio_gt_of_log_bounds {F : ℂ → ℂ} {σ B y y₀ : ℝ}
    (hy : y < y₀) (hy₀ : 0 < y₀) (hB : 1 < B)
    (hupper : ∀ t : ℝ, ‖F (σ + t * Complex.I)‖ ≤ B)
    (hlower : ∀ t : ℝ,
      y₀ * Real.log B ≤ Real.log ‖F (σ + t * Complex.I)‖) :
    y < verticalRatio F σ := by
  let m : ℝ := ⨅ t : ℝ, ‖F (σ + t * Complex.I)‖
  let M : ℝ := ⨆ t : ℝ, ‖F (σ + t * Complex.I)‖
  have hq : 0 < y₀ * Real.log B := mul_pos hy₀ (Real.log_pos hB)
  have hnorm : ∀ t : ℝ, 1 < ‖F (σ + t * Complex.I)‖ := by
    intro t
    exact (Real.log_pos_iff (norm_nonneg _)).1 (hq.trans_le (hlower t))
  have hMupper : M ≤ B := by
    dsimp [M]
    exact ciSup_le hupper
  have hMlower : 1 < M := by
    have hbdd : BddAbove (Set.range fun t : ℝ => ‖F (σ + t * Complex.I)‖) := by
      refine ⟨B, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact hupper t
    exact (hnorm 0).trans_le (le_ciSup hbdd 0)
  have hmLower : Real.exp (y₀ * Real.log B) ≤ m := by
    dsimp [m]
    apply le_ciInf
    intro t
    calc
      Real.exp (y₀ * Real.log B) ≤
          Real.exp (Real.log ‖F (σ + t * Complex.I)‖) :=
        Real.exp_le_exp.mpr (hlower t)
      _ = ‖F (σ + t * Complex.I)‖ :=
        Real.exp_log (lt_trans zero_lt_one (hnorm t))
  have hmPos : 0 < m := (Real.exp_pos _).trans_le hmLower
  have hlogm : y₀ * Real.log B ≤ Real.log m := by
    rw [← Real.log_exp (y₀ * Real.log B)]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hmPos hmLower
  have hlogMupper : Real.log M ≤ Real.log B :=
    Real.strictMonoOn_log.monotoneOn (lt_trans zero_lt_one hMlower)
      (lt_trans zero_lt_one hB) hMupper
  have hlogMpos : 0 < Real.log M := Real.log_pos hMlower
  have hy₀M : y₀ * Real.log M ≤ y₀ * Real.log B :=
    mul_le_mul_of_nonneg_left hlogMupper hy₀.le
  have hy₀ratio : y₀ ≤ Real.log m / Real.log M := by
    rw [le_div_iff₀ hlogMpos]
    exact hy₀M.trans hlogm
  exact hy.trans_le (by simpa [verticalRatio, m, M] using hy₀ratio)

/-- The largest term of the gap series on logarithmic radius `σ`. -/
private noncomputable def maximalTerm (a : ℕ → ℂ) (n : ℕ → ℕ) (σ : ℝ) : ℝ :=
  ⨆ k : ℕ, ‖a k‖ * Real.exp ((n k : ℝ) * σ)

private noncomputable def geometricExpSum (d : ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp (-(k : ℝ) * d)

private lemma geometricExpSum_pos {d : ℝ} (hd : 0 < d) :
    0 < geometricExpSum d := by
  have hs : Summable (fun k : ℕ => Real.exp (-(k : ℝ) * d)) := by
    have h := Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hd)
    simpa only [Nat.cast_comm, mul_neg, neg_mul, neg_neg] using h
  have hzero := hs.le_tsum 0 (fun k hk => Real.exp_nonneg _)
  have hone : 1 ≤ geometricExpSum d := by
    simpa [geometricExpSum] using hzero
  linarith

private lemma one_le_geometricExpSum {d : ℝ} (hd : 0 < d) :
    1 ≤ geometricExpSum d := by
  have hs : Summable (fun k : ℕ => Real.exp (-(k : ℝ) * d)) := by
    have h := Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hd)
    simpa only [Nat.cast_comm, mul_neg, neg_mul, neg_neg] using h
  simpa [geometricExpSum] using hs.le_tsum 0 (fun k hk => Real.exp_nonneg _)

private lemma maximalTerm_bddAbove {f : ℂ → ℂ} {a : ℕ → ℂ} {n : ℕ → ℕ}
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z)) (σ : ℝ) :
    BddAbove (Set.range fun k : ℕ ↦ ‖a k‖ * Real.exp ((n k : ℝ) * σ)) := by
  refine ⟨∑' k : ℕ, ‖a k * (Real.exp σ : ℂ) ^ n k‖, ?_⟩
  rintro _ ⟨k, rfl⟩
  have hs := (hfn (Real.exp σ : ℂ)).summable.norm
  have hle := hs.le_tsum k (fun j hj ↦ norm_nonneg _)
  simpa [norm_mul, norm_pow, ← Real.exp_nat_mul, mul_comm] using hle

private lemma maximalTerm_nonneg {f : ℂ → ℂ} {a : ℕ → ℂ} {n : ℕ → ℕ}
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z)) (σ : ℝ) :
    0 ≤ maximalTerm a n σ := by
  exact (mul_nonneg (norm_nonneg (a 0)) (Real.exp_nonneg _)).trans
    (le_ciSup (maximalTerm_bddAbove hfn σ) 0)

private lemma term_le_maximalTerm {f : ℂ → ℂ} {a : ℕ → ℂ} {n : ℕ → ℕ}
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z)) (σ : ℝ) (k : ℕ) :
    ‖a k‖ * Real.exp ((n k : ℝ) * σ) ≤ maximalTerm a n σ :=
  le_ciSup (maximalTerm_bddAbove hfn σ) k

/-- Moving a fixed positive distance to the right makes the sum of all terms bounded by
the shifted maximal term times a convergent geometric series.  Integrality and strict
increase of the exponents are used only through `k ≤ n k`. -/
private lemma maxModulus_exp_le_maximalTerm_shift {f : ℂ → ℂ} {a : ℕ → ℂ}
    {n : ℕ → ℕ} (hn : StrictMono n)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    {h : ℝ} (hh : 0 < h) (σ : ℝ) :
    maxModulus (Real.exp σ) f ≤
      maximalTerm a n (σ + h) * ∑' k : ℕ, Real.exp (-(k : ℝ) * h) := by
  have hgeom : Summable (fun k : ℕ ↦ Real.exp (-(k : ℝ) * h)) := by
    have hs := Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hh)
    simpa only [Nat.cast_comm, mul_neg, neg_mul, neg_neg] using hs
  let C : ℝ := ∑' k : ℕ, Real.exp (-(k : ℝ) * h)
  let := circle_nonempty (Real.exp_nonneg σ)
  rw [maxModulus]
  apply ciSup_le
  intro z
  have hmajor : ∀ k : ℕ,
      ‖a k * (z : ℂ) ^ n k‖ ≤
        maximalTerm a n (σ + h) * Real.exp (-(k : ℝ) * h) := by
    intro k
    have hkn : (k : ℝ) ≤ (n k : ℝ) := by
      exact_mod_cast StrictMono.id_le hn k
    have hexp : Real.exp (-(n k : ℝ) * h) ≤ Real.exp (-(k : ℝ) * h) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hkn) hh.le
    have hterm := term_le_maximalTerm hfn (σ + h) k
    have hexp_split : Real.exp ((n k : ℝ) * σ) =
        Real.exp ((n k : ℝ) * (σ + h)) * Real.exp (-(n k : ℝ) * h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      ‖a k * (z : ℂ) ^ n k‖ =
          ‖a k‖ * Real.exp ((n k : ℝ) * σ) := by
        rw [norm_mul, norm_pow, z.property, ← Real.exp_nat_mul]
      _ = (‖a k‖ * Real.exp ((n k : ℝ) * (σ + h))) *
            Real.exp (-(n k : ℝ) * h) := by rw [hexp_split, mul_assoc]
      _ ≤ maximalTerm a n (σ + h) * Real.exp (-(n k : ℝ) * h) :=
        mul_le_mul_of_nonneg_right hterm (Real.exp_nonneg _)
      _ ≤ maximalTerm a n (σ + h) * Real.exp (-(k : ℝ) * h) :=
        mul_le_mul_of_nonneg_left hexp (maximalTerm_nonneg hfn (σ + h))
  have hsum : HasSum
      (fun k : ℕ ↦ maximalTerm a n (σ + h) * Real.exp (-(k : ℝ) * h))
      (maximalTerm a n (σ + h) * C) := by
    exact hgeom.hasSum.mul_left _
  exact (hfn z).norm_le_of_bounded hsum hmajor

private lemma log_maximalTerm_shift_lower {f : ℂ → ℂ} {a : ℕ → ℂ}
    {n : ℕ → ℕ} (hn : StrictMono n)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    {d : ℝ} (hd : 0 < d) {σ : ℝ}
    (hM : 1 < maxModulus (Real.exp σ) f) :
    Real.log (maxModulus (Real.exp σ) f) - Real.log (geometricExpSum d) ≤
      Real.log (maximalTerm a n (σ + d)) := by
  have hbound := maxModulus_exp_le_maximalTerm_shift hn hfn hd σ
  have hgeom : 0 < geometricExpSum d := geometricExpSum_pos hd
  have hmaxpos : 0 < maxModulus (Real.exp σ) f := lt_trans zero_lt_one hM
  have htermpos : 0 < maximalTerm a n (σ + d) := by
    by_contra h
    have hnonpos : maximalTerm a n (σ + d) ≤ 0 := le_of_not_gt h
    have hrhs : maximalTerm a n (σ + d) * geometricExpSum d ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos hgeom.le
    have : maxModulus (Real.exp σ) f ≤ 0 := by
      exact hbound.trans (by simpa [geometricExpSum] using hrhs)
    linarith
  have hlog := Real.strictMonoOn_log.monotoneOn hmaxpos
    (mul_pos htermpos hgeom) (by simpa [geometricExpSum] using hbound)
  rw [Real.log_mul htermpos.ne' hgeom.ne'] at hlog
  linarith

/-- Identification of a displayed gap coefficient with the corresponding Taylor
coefficient of the entire function. -/
private lemma gapCoefficient_eq_iteratedDeriv_div_factorial {f : ℂ → ℂ}
    {a : ℕ → ℂ} {n : ℕ → ℕ} (hn : StrictMono n)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    (hf : Differentiable ℂ f) (k : ℕ) :
    a k = iteratedDeriv (n k) f 0 / ((n k).factorial : ℂ) := by
  classical
  let b : ℕ → ℂ := Function.extend n a 0
  have hsum : ∀ z, HasSum (fun m ↦ b m * z ^ m) (f z) := by
    intro z
    have hext : Function.extend n (fun j ↦ a j * z ^ n j) 0 =
        fun m ↦ b m * z ^ m := by
      funext m
      by_cases hm : ∃ j, n j = m
      · obtain ⟨j, rfl⟩ := hm
        simp [b, hn.injective.extend_apply]
      · simp [b, Function.extend_apply' _ _ _ hm]
    rw [← hext]
    exact (hasSum_extend_zero hn.injective).2 (hfn z)
  have hp : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ b) 0 := by
    rw [hasFPowerSeriesAt_iff]
    exact Filter.Eventually.of_forall fun z ↦ by
      simpa [FormalMultilinearSeries.coeff_ofScalars, mul_comm] using hsum z
  have hcanonical := (hf.analyticAt 0).hasFPowerSeriesAt
  have heq := hp.eq_formalMultilinearSeries hcanonical
  have hcoeff := congrArg
    (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff (n k)) heq
  have hcoeff' : b (n k) = iteratedDeriv (n k) f 0 / ((n k).factorial : ℂ) := by
    simpa [FormalMultilinearSeries.coeff_ofScalars] using hcoeff
  change Function.extend n a 0 (n k) = _ at hcoeff'
  rwa [hn.injective.extend_apply] at hcoeff'

/-- Cauchy's estimate bounds every displayed term by the maximum modulus on the same
circle. -/
private lemma gapTerm_le_maxModulus {f : ℂ → ℂ} {a : ℕ → ℂ} {n : ℕ → ℕ}
    (hn : StrictMono n) (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    (hf : Differentiable ℂ f) {c : ℝ} {A : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * Real.exp (‖z‖ ^ A))
    {R : ℝ} (hR : 0 < R) (k : ℕ) :
    ‖a k‖ * R ^ n k ≤ maxModulus R f := by
  have hC : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ maxModulus R f := by
    intro z hz
    have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere] using hz
    exact le_ciSup (maxModulus_bddAbove hbound)
      (⟨z, hzR⟩ : {w : ℂ // ‖w‖ = R})
  have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (n k) hR hf.diffContOnCl hC
  have hcoeff := gapCoefficient_eq_iteratedDeriv_div_factorial hn hfn hf k
  rw [hcoeff, norm_div, _root_.norm_natCast]
  have hfac : (0 : ℝ) < (n k).factorial := by positivity
  have hpow : 0 < R ^ n k := pow_pos hR _
  rw [div_mul_eq_mul_div, div_le_iff₀ hfac]
  have hm := (le_div_iff₀ hpow).mp hderiv
  simpa only [Nat.cast_ofNat, mul_comm] using hm

private lemma maximalTerm_le_maxModulus {f : ℂ → ℂ} {a : ℕ → ℂ} {n : ℕ → ℕ}
    (hn : StrictMono n) (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    (hf : Differentiable ℂ f) {c : ℝ} {A : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * Real.exp (‖z‖ ^ A)) (σ : ℝ) :
    maximalTerm a n σ ≤ maxModulus (Real.exp σ) f := by
  rw [maximalTerm]
  apply ciSup_le
  intro k
  simpa only [← Real.exp_nat_mul] using
    gapTerm_le_maxModulus hn hfn hf hbound (Real.exp_pos σ) k

/-- The finite set of displayed exponents below a cutoff.  The redundant
`range N` makes this a computable finite set; strict increase proves that it
contains exactly the indices whose exponents are below `N`. -/
private def gapHead (n : ℕ → ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun k ↦ n k < N

private lemma mem_gapHead_iff {n : ℕ → ℕ} (hn : StrictMono n) {N k : ℕ} :
    k ∈ gapHead n N ↔ n k < N := by
  rw [gapHead, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨Finset.mem_range.2 ((StrictMono.id_le hn k).trans_lt h), h⟩

/-- A quantitative inverse-counting estimate for the exponent set. -/
private lemma gapHead_card_le_add {n : ℕ → ℕ} (hn : StrictMono n)
    {K₀ : ℕ} {η : ℝ} (hη : 0 < η)
    (hindex : ∀ k ≥ K₀, (k : ℝ) ≤ η * (n k : ℝ)) (N : ℕ) :
    (gapHead n N).card ≤ K₀ + η * (N : ℝ) + 1 := by
  classical
  let K := (gapHead n N).card
  by_cases hsmall : K ≤ K₀
  · have hcast : (K : ℝ) ≤ K₀ := by exact_mod_cast hsmall
    dsimp [K] at hcast ⊢
    nlinarith [mul_nonneg hη.le (Nat.cast_nonneg N)]
  · have hKpos : 0 < K := lt_of_le_of_lt (Nat.zero_le K₀) (Nat.lt_of_not_ge hsmall)
    let k := K - 1
    have hkK : k + 1 = K := by dsimp [k]; omega
    have hk₀ : K₀ ≤ k := by dsimp [k]; omega
    have hkmem : k ∈ gapHead n N := by
      by_contra hknot
      have hnk : N ≤ n k := Nat.le_of_not_gt fun hlt ↦
        hknot ((mem_gapHead_iff hn).2 hlt)
      have hsubset : gapHead n N ⊆ Finset.range k := by
        intro j hj
        rw [Finset.mem_range]
        by_contra hjnot
        have hkj : k ≤ j := Nat.le_of_not_gt hjnot
        have hnj : n k ≤ n j := hn.monotone hkj
        have hjexp : n j < N := (mem_gapHead_iff hn).1 hj
        omega
      have hcard := Finset.card_le_card hsubset
      rw [Finset.card_range, show (gapHead n N).card = K by rfl, ← hkK] at hcard
      omega
    have hexp : n k < N := (mem_gapHead_iff hn).1 hkmem
    have hidx := hindex k hk₀
    have hexpR : (n k : ℝ) < N := by exact_mod_cast hexp
    have hKR : (K : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hkK.symm
    change (K : ℝ) ≤ K₀ + η * (N : ℝ) + 1
    rw [hKR]
    have : (k : ℝ) < η * (N : ℝ) :=
      hidx.trans_lt (mul_lt_mul_of_pos_left hexpR hη)
    have hK₀R : (0 : ℝ) ≤ (K₀ : ℝ) := Nat.cast_nonneg _
    linarith

/-- On a line a positive distance to the left of `τ`, the part of the gap
series whose exponents are at least `N` is geometrically small.  The second
half of the exponential decay is compared with `k ≤ n k`; this avoids any
counting or reindexing of the sparse exponent set. -/
private lemma logLift_sub_gapHead_norm_le {f : ℂ → ℂ} {a : ℕ → ℂ}
    {n : ℕ → ℕ} (hn : StrictMono n)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    (hf : Differentiable ℂ f) {c : ℝ} {A : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * Real.exp (‖z‖ ^ A))
    {d : ℝ} (hd : 0 < d) (N : ℕ) (w : ℂ) (hw : w.re ≤ τ - d) :
    ‖logLift f w -
        ∑ k ∈ gapHead n N, a k * Complex.exp ((n k : ℂ) * w)‖ ≤
      maxModulus (Real.exp τ) f * Real.exp (-(N : ℝ) * d / 2) *
        ∑' k : ℕ, Real.exp (-(k : ℝ) * d / 2) := by
  classical
  let u : ℕ → ℂ := fun k ↦ a k * Complex.exp ((n k : ℂ) * w)
  let B : ℝ := maxModulus (Real.exp τ) f * Real.exp (-(N : ℝ) * d / 2)
  let v : ℕ → ℝ := fun k ↦ B * Real.exp (-(k : ℝ) * d / 2)
  have huSum : Summable u := (logLift_hasSum hfn w).summable
  have hgeom : Summable (fun k : ℕ ↦ Real.exp (-(k : ℝ) * d / 2)) := by
    have hneg : -(d / 2) < 0 := by linarith
    have hs := Real.summable_exp_nat_mul_iff.mpr hneg
    refine hs.congr fun k ↦ ?_
    congr 1
    ring
  have hvSum : Summable v := hgeom.mul_left B
  have hMnonneg : 0 ≤ maxModulus (Real.exp τ) f := by
    let := circle_nonempty (Real.exp_nonneg τ)
    exact (norm_nonneg (f (Real.exp τ : ℂ))).trans
      (le_ciSup (maxModulus_bddAbove hbound)
        (⟨(Real.exp τ : ℂ), by simp⟩ : {z : ℂ // ‖z‖ = Real.exp τ}))
  have hmajor : ∀ k : ↑((↑(gapHead n N) : Set ℕ)ᶜ), ‖u k.1‖ ≤ v k.1 := by
    intro k
    have hknot := k.2
    change k.1 ∉ gapHead n N at hknot
    have hNk : N ≤ n k.1 := Nat.le_of_not_gt fun hlt ↦
      hknot ((mem_gapHead_iff hn).2 hlt)
    have hkn : k.1 ≤ n k.1 := StrictMono.id_le hn k.1
    have hterm := gapTerm_le_maxModulus hn hfn hf hbound (Real.exp_pos τ) k.1
    have hwdecay : (n k.1 : ℝ) * w.re ≤ (n k.1 : ℝ) * (τ - d) :=
      mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
    have hsplit :
        Real.exp ((n k.1 : ℝ) * w.re) ≤
          Real.exp ((n k.1 : ℝ) * τ) *
            (Real.exp (-(N : ℝ) * d / 2) *
              Real.exp (-(k.1 : ℝ) * d / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hNkR : (N : ℝ) ≤ n k.1 := by exact_mod_cast hNk
      have hknR : (k.1 : ℝ) ≤ n k.1 := by exact_mod_cast hkn
      calc
        (n k.1 : ℝ) * w.re ≤ (n k.1 : ℝ) * (τ - d) := hwdecay
        _ ≤ (n k.1 : ℝ) * τ - (N : ℝ) * d / 2 - (k.1 : ℝ) * d / 2 := by
          nlinarith
        _ = (n k.1 : ℝ) * τ +
            (-(N : ℝ) * d / 2 + -(k.1 : ℝ) * d / 2) := by ring
    change ‖a k.1 * Complex.exp ((n k.1 : ℂ) * w)‖ ≤
      B * Real.exp (-(k.1 : ℝ) * d / 2)
    have hnormexp : ‖Complex.exp ((n k.1 : ℂ) * w)‖ =
        Real.exp ((n k.1 : ℝ) * w.re) := by
      rw [Complex.norm_exp]
      simp
    rw [norm_mul, hnormexp]
    calc
      ‖a k.1‖ * Real.exp ((n k.1 : ℝ) * w.re) ≤
          ‖a k.1‖ * (Real.exp ((n k.1 : ℝ) * τ) *
            (Real.exp (-(N : ℝ) * d / 2) *
              Real.exp (-(k.1 : ℝ) * d / 2))) :=
        mul_le_mul_of_nonneg_left hsplit (norm_nonneg _)
      _ = (‖a k.1‖ * Real.exp ((n k.1 : ℝ) * τ)) *
          Real.exp (-(N : ℝ) * d / 2) *
            Real.exp (-(k.1 : ℝ) * d / 2) := by ring
      _ ≤ maxModulus (Real.exp τ) f * Real.exp (-(N : ℝ) * d / 2) *
            Real.exp (-(k.1 : ℝ) * d / 2) := by
        gcongr
        simpa only [← Real.exp_nat_mul] using hterm
      _ = B * Real.exp (-(k.1 : ℝ) * d / 2) := by rfl
  have htail := (huSum.subtype fun k ↦ k ∈ (↑(gapHead n N) : Set ℕ)ᶜ).hasSum.norm_le_of_bounded
    (hvSum.subtype fun k ↦ k ∈ (↑(gapHead n N) : Set ℕ)ᶜ).hasSum hmajor
  have htailEq :
      (∑' k : ↑((↑(gapHead n N) : Set ℕ)ᶜ), (u ∘ Subtype.val) k) =
        logLift f w - ∑ k ∈ gapHead n N, u k := by
    have hdecomp := huSum.sum_add_tsum_compl (s := gapHead n N)
    have htotal : (∑' k : ℕ, u k) = logLift f w :=
      (logLift_hasSum hfn w).tsum_eq
    rw [htotal] at hdecomp
    change (∑ k ∈ gapHead n N, u k) +
      (∑' k : ↑((↑(gapHead n N) : Set ℕ)ᶜ), (u ∘ Subtype.val) k) =
        logLift f w at hdecomp
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact hdecomp
  rw [htailEq] at htail
  calc
    ‖logLift f w - ∑ k ∈ gapHead n N, a k * Complex.exp ((n k : ℂ) * w)‖ ≤
        ∑' k : ↑((↑(gapHead n N) : Set ℕ)ᶜ), v k.1 := htail
    _ ≤ ∑' k : ℕ, v k := by
      exact Summable.tsum_subtype_le v ((↑(gapHead n N) : Set ℕ)ᶜ) (fun k ↦ by
        dsimp [v, B]
        positivity) hvSum
    _ = maxModulus (Real.exp τ) f * Real.exp (-(N : ℝ) * d / 2) *
          ∑' k : ℕ, Real.exp (-(k : ℝ) * d / 2) := by
      rw [show v = fun k : ℕ ↦ B * Real.exp (-(k : ℝ) * d / 2) by rfl,
        tsum_mul_left]

/-- The logarithmic maximum modulus tends to infinity.  One nonconstant
displayed monomial already supplies the required lower bound. -/
private lemma tendsto_log_maxModulus_exp_atTop {f : ℂ → ℂ} {a : ℕ → ℂ}
    {n : ℕ → ℕ} (hn : StrictMono n) (ha : ∀ k, a k ≠ 0)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    (hf : Differentiable ℂ f) {c : ℝ} {A : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * Real.exp (‖z‖ ^ A)) :
    Tendsto (fun σ : ℝ ↦ Real.log (maxModulus (Real.exp σ) f)) atTop atTop := by
  have hn1 : 0 < n 1 := lt_of_lt_of_le Nat.zero_lt_one (StrictMono.id_le hn 1)
  have hn1R : (0 : ℝ) < n 1 := by exact_mod_cast hn1
  have ha1 : 0 < ‖a 1‖ := norm_pos_iff.mpr (ha 1)
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop ((B - Real.log ‖a 1‖) / (n 1 : ℝ))] with σ hσ
  have hterm := gapTerm_le_maxModulus hn hfn hf hbound (Real.exp_pos σ) 1
  have htermpos : 0 < ‖a 1‖ * (Real.exp σ) ^ n 1 := mul_pos ha1 (by positivity)
  have hMpos : 0 < maxModulus (Real.exp σ) f := htermpos.trans_le hterm
  have hlogterm : Real.log (‖a 1‖ * (Real.exp σ) ^ n 1) =
      Real.log ‖a 1‖ + (n 1 : ℝ) * σ := by
    rw [Real.log_mul ha1.ne' (by positivity), Real.log_pow, Real.log_exp]
  calc
    B ≤ Real.log ‖a 1‖ + (n 1 : ℝ) * σ := by
      have hmul := (div_le_iff₀ hn1R).mp hσ
      linarith
    _ = Real.log (‖a 1‖ * (Real.exp σ) ^ n 1) := hlogterm.symm
    _ ≤ Real.log (maxModulus (Real.exp σ) f) :=
      Real.strictMonoOn_log.monotoneOn htermpos hMpos hterm

/-- Because the term norms form a summable sequence tending to zero and every displayed
coefficient is nonzero, the maximal term is attained at a finite index. -/
private lemma exists_term_eq_maximalTerm {f : ℂ → ℂ} {a : ℕ → ℂ}
    {n : ℕ → ℕ} (ha : ∀ k, a k ≠ 0)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z)) (σ : ℝ) :
    ∃ j : ℕ, ‖a j‖ * Real.exp ((n j : ℝ) * σ) = maximalTerm a n σ := by
  let u : ℕ → ℝ := fun k ↦ ‖a k‖ * Real.exp ((n k : ℝ) * σ)
  have hu : Summable u := by
    have hs := (hfn (Real.exp σ : ℂ)).summable.norm
    simpa [u, norm_mul, norm_pow, ← Real.exp_nat_mul, mul_comm] using hs
  have hu0 : Tendsto u atTop (𝓝 0) := hu.tendsto_atTop_zero
  have hupos : 0 < u 0 := by
    dsimp [u]
    exact mul_pos (norm_pos_iff.mpr (ha 0)) (Real.exp_pos _)
  have hevent : ∀ᶠ k : ℕ in atTop, u k < u 0 :=
    hu0.eventually (Iio_mem_nhds hupos)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  obtain ⟨j, hjmem, hjmax⟩ := Finset.exists_max_image (Finset.range (K + 1)) u
    ⟨0, Finset.mem_range.2 (by omega)⟩
  refine ⟨j, ?_⟩
  have hjall : ∀ k : ℕ, u k ≤ u j := by
    intro k
    by_cases hk : k < K + 1
    · exact hjmax k (Finset.mem_range.2 hk)
    · have hkK : K ≤ k := by omega
      have hk0 : u k ≤ u 0 := (hK k hkK).le
      exact hk0.trans (hjmax 0 (Finset.mem_range.2 (by omega)))
  have hle : u j ≤ maximalTerm a n σ := by
    exact term_le_maximalTerm hfn σ j
  have hge : maximalTerm a n σ ≤ u j := by
    rw [maximalTerm]
    exact ciSup_le hjall
  exact le_antisymm hle hge

/-- Between two nonzero displayed coefficients, the term with the larger exponent
eventually dominates on logarithmic radii. -/
private lemma eventually_gapTerm_lt {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0)
    {m q : ℕ} (hmq : m < q) :
    ∀ᶠ σ : ℝ in atTop,
      ‖α‖ * Real.exp ((m : ℝ) * σ) < ‖β‖ * Real.exp ((q : ℝ) * σ) := by
  let C : ℝ := ‖α‖ / ‖β‖
  let d : ℝ := (q : ℝ) - (m : ℝ)
  have hβpos : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have hC : 0 < C := div_pos (norm_pos_iff.mpr hα) hβpos
  have hd : 0 < d := by
    have hmqR : (m : ℝ) < (q : ℝ) := by exact_mod_cast hmq
    dsimp [d]
    linarith
  filter_upwards [eventually_ge_atTop (Real.log C / d + 1)] with σ hσ
  have hlog : Real.log C < d * σ := by
    have hdiv : Real.log C / d < σ := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hd).mp hdiv
  have hCexp : C < Real.exp (d * σ) := by
    rw [← Real.exp_log hC]
    exact Real.exp_lt_exp.mpr hlog
  have hcoeff : ‖α‖ < ‖β‖ * Real.exp (d * σ) := by
    have hmul := mul_lt_mul_of_pos_left hCexp hβpos
    have hcancel : ‖β‖ * C = ‖α‖ := by
      dsimp [C]
      field_simp
    rwa [hcancel] at hmul
  have hmul := mul_lt_mul_of_pos_right hcoeff (Real.exp_pos ((m : ℝ) * σ))
  calc
    ‖α‖ * Real.exp ((m : ℝ) * σ) <
        (‖β‖ * Real.exp (d * σ)) * Real.exp ((m : ℝ) * σ) := hmul
    _ = ‖β‖ * Real.exp ((q : ℝ) * σ) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [d]
      ring

/-- Every maximizing index of the maximal term eventually lies beyond any prescribed
finite initial segment.  This is the central-index escape property used when the Fabry
zero-density estimate is applied at selected radii. -/
private lemma eventually_exists_large_maximalTerm_index {f : ℂ → ℂ}
    {a : ℕ → ℂ} {n : ℕ → ℕ} (hn : StrictMono n) (ha : ∀ k, a k ≠ 0)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z)) (K : ℕ) :
    ∀ᶠ σ : ℝ in atTop, ∃ j : ℕ, K < j ∧
      ‖a j‖ * Real.exp ((n j : ℝ) * σ) = maximalTerm a n σ := by
  have hhead : ∀ k ∈ Finset.range (K + 1),
      ∀ᶠ σ : ℝ in atTop,
        ‖a k‖ * Real.exp ((n k : ℝ) * σ) <
          ‖a (K + 1)‖ * Real.exp ((n (K + 1) : ℝ) * σ) := by
    intro k hk
    exact eventually_gapTerm_lt (ha k) (ha (K + 1))
      (hn (Finset.mem_range.1 hk))
  have hall : ∀ᶠ σ : ℝ in atTop, ∀ k ∈ Finset.range (K + 1),
      ‖a k‖ * Real.exp ((n k : ℝ) * σ) <
        ‖a (K + 1)‖ * Real.exp ((n (K + 1) : ℝ) * σ) :=
    (eventually_all_finset (Finset.range (K + 1))).2 hhead
  filter_upwards [hall] with σ hσ
  obtain ⟨j, hj⟩ := exists_term_eq_maximalTerm ha hfn σ
  refine ⟨j, ?_, hj⟩
  by_contra hjK
  have hjmem : j ∈ Finset.range (K + 1) := Finset.mem_range.2 (by omega)
  have hstrict := hσ j hjmem
  have hle := term_le_maximalTerm hfn σ (K + 1)
  linarith

/-- The finite polynomial supported on a selected set of gap exponents. -/
private noncomputable def finiteGapPolynomial (n : ℕ → ℕ) (c : ℕ → ℂ)
    (s : Finset ℕ) : ℂ[X] :=
  ∑ k ∈ s, Polynomial.monomial (n k) (c k)

private lemma finiteGapPolynomial_coeff_of_mem {n : ℕ → ℕ} (hn : StrictMono n)
    {c : ℕ → ℂ} {s : Finset ℕ} {k : ℕ} (hk : k ∈ s) :
    (finiteGapPolynomial n c s).coeff (n k) = c k := by
  classical
  simp [finiteGapPolynomial, Polynomial.coeff_monomial, hn.injective.eq_iff, hk]

private lemma finiteGapPolynomial_eval {n : ℕ → ℕ} {c : ℕ → ℂ}
    {s : Finset ℕ} (z : ℂ) :
    (finiteGapPolynomial n c s).eval z = ∑ k ∈ s, c k * z ^ n k := by
  classical
  simp [finiteGapPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_monomial]

/-- Some point of the unit circle evaluates a complex polynomial at least as
large as any prescribed coefficient.  This is Cauchy's coefficient estimate,
with compactness used to choose an actual maximizer. -/
private lemma exists_unit_norm_eval_ge_coeff (P : ℂ[X]) (d : ℕ) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ ‖P.coeff d‖ ≤ ‖P.eval w‖ := by
  classical
  let F : ℂ → ℂ := fun z ↦ P.eval z
  have hdiff : Differentiable ℂ F := by
    dsimp [F]
    fun_prop
  obtain ⟨w, hwfront, hwmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
    Metric.isBounded_ball ⟨0, Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)⟩
    hdiff.diffContOnCl
  have hwsphere : w ∈ Metric.sphere (0 : ℂ) 1 := by
    rwa [← frontier_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
  have hwnorm : ‖w‖ = 1 := by simpa [Metric.mem_sphere] using hwsphere
  have hcircle : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ‖F z‖ ≤ ‖F w‖ := by
    intro z hz
    apply hwmax
    rw [closure_ball 0 (by norm_num : (1 : ℝ) ≠ 0)]
    exact Metric.sphere_subset_closedBall hz
  have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    d (by norm_num : (0 : ℝ) < 1) hdiff.diffContOnCl hcircle
  have hsum : ∀ z : ℂ, HasSum (fun k : ℕ ↦ P.coeff k * z ^ k) (F z) := by
    intro z
    have hsumm : Summable (fun k : ℕ ↦ P.coeff k * z ^ k) :=
      summable_of_ne_finset_zero (s := P.support) fun k hk ↦ by
        have hcoeff : P.coeff k = 0 := by simpa [Polynomial.mem_support_iff] using hk
        rw [hcoeff, zero_mul]
    have hs := hsumm.hasSum
    convert hs using 1
    rw [tsum_eq_sum (s := P.support) (fun k hk ↦ by
      have hcoeff : P.coeff k = 0 := by simpa [Polynomial.mem_support_iff] using hk
      rw [hcoeff, zero_mul])]
    simpa [F, Polynomial.eval_eq_sum, Polynomial.sum_def]
  have hcoeff := gapCoefficient_eq_iteratedDeriv_div_factorial
    (n := fun k : ℕ ↦ k) (a := fun k ↦ P.coeff k) strictMono_id hsum hdiff d
  refine ⟨w, hwnorm, ?_⟩
  rw [hcoeff, norm_div, _root_.norm_natCast]
  have hfac : (0 : ℝ) < d.factorial := by positivity
  apply (div_le_iff₀ hfac).2
  simpa [F, mul_comm] using hderiv

/-! ### A quantitative Turán interpolation lemma

For the integer-frequency specialization needed here, a short-interval localization
estimate follows from a power-sum argument.  The following root polynomial and its
Cauchy-integral remainder coefficients give a separation-free proof: the constants
depend exponentially only on the number of frequencies. -/

private noncomputable def turanRootPolynomial {K : ℕ} (w : Fin K → ℂ) : ℂ[X] :=
  ∏ j : Fin K, (Polynomial.X - Polynomial.C (w j))

private lemma turanRootPolynomial_monic {K : ℕ} (w : Fin K → ℂ) :
    (turanRootPolynomial w).Monic := by
  simpa only [turanRootPolynomial] using
    Polynomial.monic_prod_X_sub_C w (Finset.univ : Finset (Fin K))

private lemma turanRootPolynomial_natDegree {K : ℕ} (w : Fin K → ℂ) :
    (turanRootPolynomial w).natDegree = K := by
  rw [turanRootPolynomial]
  simpa using Polynomial.natDegree_finsetProd_X_sub_C_eq_card
    (s := Finset.univ) w

private lemma turanRootPolynomial_eval_root {K : ℕ} (w : Fin K → ℂ) (j : Fin K) :
    (turanRootPolynomial w).eval (w j) = 0 := by
  rw [turanRootPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp

private lemma turanRootPolynomial_mahlerMeasure_eq_one {K : ℕ} (w : Fin K → ℂ)
    (hw : ∀ j, ‖w j‖ ≤ 1) :
    (turanRootPolynomial w).mahlerMeasure = 1 := by
  rw [turanRootPolynomial]
  induction (Finset.univ : Finset (Fin K)) using Finset.induction with
  | empty => simp [Polynomial.mahlerMeasure_one]
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs, Polynomial.mahlerMeasure_mul, ih]
      rw [Polynomial.mahlerMeasure_X_sub_C]
      simp [max_eq_left (hw j)]

private lemma turanRootPolynomial_coeff_norm_le_choose {K : ℕ} (w : Fin K → ℂ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (d : ℕ) :
    ‖(turanRootPolynomial w).coeff d‖ ≤ K.choose d := by
  have h := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure d
    (turanRootPolynomial w)
  rw [turanRootPolynomial_natDegree, turanRootPolynomial_mahlerMeasure_eq_one w hw,
    mul_one] at h
  exact h

private lemma turanRootPolynomial_norm_ge_one_on_sphere_two {K : ℕ}
    (w : Fin K → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1) {ζ : ℂ} (hζ : ‖ζ‖ = 2) :
    1 ≤ ‖(turanRootPolynomial w).eval ζ‖ := by
  rw [turanRootPolynomial, Polynomial.eval_prod]
  simp_rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_prod]
  have hfactor : ∀ j : Fin K, 1 ≤ ‖ζ - w j‖ := by
    intro j
    have hrev := norm_sub_norm_le ζ (w j)
    rw [hζ] at hrev
    linarith [hw j]
  exact Finset.one_le_prod (fun j _ ↦ hfactor j)

private noncomputable def turanDividedCoeff (P : ℂ[X]) (K i : ℕ) (ζ : ℂ) : ℂ :=
  ∑ d ∈ Finset.range (K + 1),
    if i < d then P.coeff d * ζ ^ (d - 1 - i) else 0

private lemma mul_turanMonomialDividedSum (ζ x : ℂ) (d : ℕ) :
    (ζ - x) * ∑ i ∈ Finset.range d, ζ ^ (d - 1 - i) * x ^ i = ζ ^ d - x ^ d := by
  have hsum :
      (∑ i ∈ Finset.range d, ζ ^ i * x ^ (d - 1 - i)) =
        ∑ i ∈ Finset.range d, ζ ^ (d - 1 - i) * x ^ i := by
    simpa only [mul_comm] using geom_sum₂_comm ζ x d
  rw [mul_comm (ζ - x), ← hsum]
  exact (Commute.all ζ x).geom_sum₂_mul d

private lemma turanDividedCoeff_sum_identity (P : ℂ[X]) {K : ℕ}
    (hP : P.natDegree ≤ K) (ζ x : ℂ) :
    (ζ - x) * ∑ i ∈ Finset.range K, turanDividedCoeff P K i ζ * x ^ i =
      P.eval ζ - P.eval x := by
  have hPK : P.natDegree < K + 1 := by omega
  rw [Polynomial.eval_eq_sum_range' hPK, Polynomial.eval_eq_sum_range' hPK,
    ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  simp_rw [turanDividedCoeff, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hdK : d < K + 1 := Finset.mem_range.1 hd
  have hrange : Finset.range d ⊆ Finset.range K := by
    intro i hi
    have hid := Finset.mem_range.1 hi
    exact Finset.mem_range.2 (by omega)
  have htri :
      (∑ i ∈ Finset.range K,
          (if i < d then P.coeff d * ζ ^ (d - 1 - i) else 0) * x ^ i) =
        P.coeff d * ∑ i ∈ Finset.range d, ζ ^ (d - 1 - i) * x ^ i := by
    calc
      (∑ i ∈ Finset.range K,
          (if i < d then P.coeff d * ζ ^ (d - 1 - i) else 0) * x ^ i) =
          ∑ i ∈ Finset.range d,
            (if i < d then P.coeff d * ζ ^ (d - 1 - i) else 0) * x ^ i := by
        rw [Finset.sum_subset hrange]
        intro i hiK hid
        have hnot : ¬ i < d := by
          simpa only [Finset.mem_range, not_lt] using hid
        simp [hnot]
      _ = ∑ i ∈ Finset.range d,
          P.coeff d * (ζ ^ (d - 1 - i) * x ^ i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hid : i < d := Finset.mem_range.1 hi
        simp only [hid, if_true]
        ring
      _ = P.coeff d * ∑ i ∈ Finset.range d,
          ζ ^ (d - 1 - i) * x ^ i := by rw [Finset.mul_sum]
  rw [← Finset.mul_sum, htri]
  rw [show (ζ - x) * (P.coeff d * ∑ i ∈ Finset.range d,
      ζ ^ (d - 1 - i) * x ^ i) =
      P.coeff d * ((ζ - x) * ∑ i ∈ Finset.range d,
        ζ ^ (d - 1 - i) * x ^ i) by ring]
  rw [mul_turanMonomialDividedSum]
  ring

private lemma turanDividedCoeff_norm_le {K : ℕ} (w : Fin K → ℂ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (i : ℕ) {ζ : ℂ} (hζ : ‖ζ‖ = 2) :
    ‖turanDividedCoeff (turanRootPolynomial w) K i ζ‖ ≤
      (K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K := by
  rw [turanDividedCoeff]
  calc
    ‖∑ d ∈ Finset.range (K + 1),
        if i < d then (turanRootPolynomial w).coeff d * ζ ^ (d - 1 - i) else 0‖ ≤
        ∑ d ∈ Finset.range (K + 1),
          ‖if i < d then (turanRootPolynomial w).coeff d * ζ ^ (d - 1 - i) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.range (K + 1), (2 : ℝ) ^ K * (2 : ℝ) ^ K := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs with hid
      · rw [norm_mul, norm_pow, hζ]
        have hcoeff := turanRootPolynomial_coeff_norm_le_choose w hw d
        have hchoose : (K.choose d : ℝ) ≤ (2 : ℝ) ^ K := by
          exact_mod_cast Nat.choose_le_two_pow K d
        have hpow : (2 : ℝ) ^ (d - 1 - i) ≤ (2 : ℝ) ^ K := by
          have hdle : d ≤ K := by
            have := Finset.mem_range.1 hd
            omega
          have hexp : d - 1 - i ≤ K := by omega
          exact pow_le_pow_right₀ (by norm_num) hexp
        exact mul_le_mul (hcoeff.trans hchoose) hpow (by positivity) (by positivity)
      · simp
    _ = (K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K := by
      simp [mul_assoc]

private noncomputable def turanInterpolationCoeff {K : ℕ} (w : Fin K → ℂ)
    (n i : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    ∮ ζ in C(0, 2),
      ζ ^ n * turanDividedCoeff (turanRootPolynomial w) K i ζ /
        (turanRootPolynomial w).eval ζ

private lemma turanInterpolationCoeff_norm_le {K : ℕ} (w : Fin K → ℂ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (n i : ℕ) :
    ‖turanInterpolationCoeff w n i‖ ≤
      2 * ((2 : ℝ) ^ n * ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K)) := by
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (show (0 : ℝ) ≤ 2 by norm_num)
  intro ζ hζ
  have hζnorm : ‖ζ‖ = 2 := by simpa [Metric.mem_sphere] using hζ
  have hP := turanRootPolynomial_norm_ge_one_on_sphere_two w hw hζnorm
  have hq := turanDividedCoeff_norm_le w hw i hζnorm
  rw [norm_div, norm_mul, norm_pow, hζnorm]
  have hden : 0 < ‖(turanRootPolynomial w).eval ζ‖ := lt_of_lt_of_le zero_lt_one hP
  rw [div_le_iff₀ hden]
  calc
    (2 : ℝ) ^ n * ‖turanDividedCoeff (turanRootPolynomial w) K i ζ‖ ≤
        (2 : ℝ) ^ n * ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ ≤ ((2 : ℝ) ^ n * ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K)) *
        ‖(turanRootPolynomial w).eval ζ‖ := by
      exact le_mul_of_one_le_right (by positivity) hP

private lemma turanInterpolationIntegrand_circleIntegrable {K : ℕ}
    (w : Fin K → ℂ) (hw : ∀ j, ‖w j‖ ≤ 1) (n i : ℕ) :
    CircleIntegrable
      (fun ζ ↦ ζ ^ n * turanDividedCoeff (turanRootPolynomial w) K i ζ /
        (turanRootPolynomial w).eval ζ) 0 2 := by
  apply ContinuousOn.circleIntegrable (show (0 : ℝ) ≤ 2 by norm_num)
  apply ContinuousOn.div
  · have hq : Continuous (fun ζ ↦
        turanDividedCoeff (turanRootPolynomial w) K i ζ) := by
      unfold turanDividedCoeff
      apply continuous_finsetSum
      intro d hd
      by_cases hid : i < d
      · simp only [hid, if_true]
        fun_prop
      · simp only [hid, if_false]
        fun_prop
    exact ((continuous_id.pow n).mul hq).continuousOn
  · fun_prop
  · intro ζ hζ
    have hζnorm : ‖ζ‖ = 2 := by simpa [Metric.mem_sphere] using hζ
    have hP := turanRootPolynomial_norm_ge_one_on_sphere_two w hw hζnorm
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hP))

private lemma turanInterpolationCoeff_interpolates {K : ℕ} (w : Fin K → ℂ)
    (hw : ∀ j, ‖w j‖ ≤ 1) (n : ℕ) (j : Fin K) :
    ∑ i ∈ Finset.range K, turanInterpolationCoeff w n i * w j ^ i = w j ^ n := by
  let P : ℂ[X] := turanRootPolynomial w
  let c₀ : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹
  let g : ℕ → ℂ → ℂ := fun i ζ ↦
    ζ ^ n * turanDividedCoeff P K i ζ / P.eval ζ
  have hint : ∀ i ∈ Finset.range K, CircleIntegrable (g i) 0 2 := by
    intro i hi
    simpa only [g, P] using turanInterpolationIntegrand_circleIntegrable w hw n i
  have hintMul : ∀ i ∈ Finset.range K,
      CircleIntegrable (fun ζ ↦ g i ζ * w j ^ i) 0 2 := by
    intro i hi
    have h := hint i hi
    change IntervalIntegrable
      (fun θ : ℝ ↦ g i (circleMap 0 2 θ) * w j ^ i) MeasureTheory.volume 0 (2 * Real.pi)
    change IntervalIntegrable
      (fun θ : ℝ ↦ g i (circleMap 0 2 θ)) MeasureTheory.volume 0 (2 * Real.pi) at h
    exact h.mul_const (w j ^ i)
  have hsumIntegral :
      (∮ ζ in C(0, 2), ∑ i ∈ Finset.range K, g i ζ * w j ^ i) =
        ∑ i ∈ Finset.range K, ∮ ζ in C(0, 2), g i ζ * w j ^ i :=
    circleIntegral.integral_fun_sum hintMul
  have hpoint : ∀ ζ ∈ Metric.sphere (0 : ℂ) 2,
      (∑ i ∈ Finset.range K, g i ζ * w j ^ i) = ζ ^ n / (ζ - w j) := by
    intro ζ hζ
    have hζnorm : ‖ζ‖ = 2 := by simpa [Metric.mem_sphere] using hζ
    have hPnorm := turanRootPolynomial_norm_ge_one_on_sphere_two w hw hζnorm
    have hPne : P.eval ζ ≠ 0 := by
      dsimp [P]
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le zero_lt_one hPnorm))
    have hζwj : ζ - w j ≠ 0 := by
      intro hzero
      have heq : ζ = w j := sub_eq_zero.mp hzero
      have := hw j
      rw [← heq, hζnorm] at this
      norm_num at this
    have hroot : P.eval (w j) = 0 := by
      exact turanRootPolynomial_eval_root w j
    have hid := turanDividedCoeff_sum_identity P
      (by dsimp [P]; rw [turanRootPolynomial_natDegree]) ζ (w j)
    rw [hroot, sub_zero] at hid
    have hqsum : (∑ i ∈ Finset.range K,
        turanDividedCoeff P K i ζ * w j ^ i) = P.eval ζ / (ζ - w j) := by
      apply (eq_div_iff hζwj).2
      simpa only [mul_comm] using hid
    calc
      (∑ i ∈ Finset.range K, g i ζ * w j ^ i) =
          (ζ ^ n / P.eval ζ) * ∑ i ∈ Finset.range K,
            turanDividedCoeff P K i ζ * w j ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [g]
        field_simp
      _ = (ζ ^ n / P.eval ζ) * (P.eval ζ / (ζ - w j)) := by rw [hqsum]
      _ = ζ ^ n / (ζ - w j) := by field_simp
  calc
    (∑ i ∈ Finset.range K, turanInterpolationCoeff w n i * w j ^ i) =
        ∑ i ∈ Finset.range K,
          c₀ * ((∮ ζ in C(0, 2), g i ζ) * w j ^ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [turanInterpolationCoeff, c₀, g, P, smul_eq_mul, mul_assoc]
    _ = c₀ * ∑ i ∈ Finset.range K, (∮ ζ in C(0, 2), g i ζ) * w j ^ i := by
      rw [Finset.mul_sum]
    _ = c₀ * ∑ i ∈ Finset.range K,
        ∮ ζ in C(0, 2), g i ζ * w j ^ i := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (∮ ζ in C(0, 2), g i ζ) * w j ^ i =
          w j ^ i * ∮ ζ in C(0, 2), g i ζ by ring,
        ← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr (show (0 : ℝ) ≤ 2 by norm_num)
      intro ζ hζ
      ring
    _ = c₀ * ∮ ζ in C(0, 2),
        ∑ i ∈ Finset.range K, g i ζ * w j ^ i := by rw [hsumIntegral]
    _ = c₀ * ∮ ζ in C(0, 2), ζ ^ n / (ζ - w j) := by
      congr 1
      apply circleIntegral.integral_congr (show (0 : ℝ) ≤ 2 by norm_num)
      exact hpoint
    _ = w j ^ n := by
      have hwball : w j ∈ Metric.ball (0 : ℂ) 2 := by
        rw [Metric.mem_ball, dist_zero_right]
        exact (hw j).trans_lt (by norm_num)
      have hcauchy := (differentiableOn_pow n).circleIntegral_sub_inv_smul
        (c := (0 : ℂ)) (R := (2 : ℝ)) hwball
      dsimp [c₀]
      rw [show (fun ζ : ℂ ↦ ζ ^ n / (ζ - w j)) =
          fun ζ ↦ (ζ - w j)⁻¹ • ζ ^ n by
        funext ζ
        simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]]
      rw [hcauchy]
      rw [smul_eq_mul]
      have hconst : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      rw [← mul_assoc, inv_mul_cancel₀ hconst, one_mul]

/-- Turán's power-sum estimate in the exact form needed below.  Among any `K`
consecutive positive translates after `M`, one translate is large compared with the
zeroth power sum.  The deliberately coarse constant is separation-free. -/
private lemma exists_large_powerSum {K M : ℕ} (hK : 0 < K)
    (w b : Fin K → ℂ) (hw : ∀ j, ‖w j‖ = 1) :
    ∃ ν ∈ Finset.Icc (M + 1) (M + K),
      ‖∑ j, b j‖ ≤
        (K : ℝ) *
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
          ‖∑ j, b j * w j ^ ν‖ := by
  let v : Fin K → ℂ := fun j ↦ (w j)⁻¹
  let c : ℕ → ℂ := fun i ↦ turanInterpolationCoeff v (M + K) i
  have hv : ∀ j, ‖v j‖ ≤ 1 := by
    intro j
    dsimp [v]
    rw [norm_inv, hw]
    norm_num
  have hwne : ∀ j, w j ≠ 0 := fun j ↦ norm_ne_zero_iff.mp (by rw [hw]; norm_num)
  have hinterp : ∀ j, (w j ^ (M + K))⁻¹ =
      ∑ i ∈ Finset.range K, c i * (w j ^ i)⁻¹ := by
    intro j
    have h := turanInterpolationCoeff_interpolates v hv (M + K) j
    simpa only [v, c, inv_pow] using h.symm
  have hidentity : (∑ j, b j) =
      ∑ i ∈ Finset.range K, c i * ∑ j, b j * w j ^ (M + K - i) := by
    calc
      (∑ j, b j) = ∑ j, (b j * w j ^ (M + K)) *
          (w j ^ (M + K))⁻¹ := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          b j = b j * 1 := by rw [mul_one]
          _ = b j * (w j ^ (M + K) * (w j ^ (M + K))⁻¹) := by
            rw [mul_inv_cancel₀ (pow_ne_zero _ (hwne j))]
          _ = b j * w j ^ (M + K) * (w j ^ (M + K))⁻¹ := by ring
      _ = ∑ j, (b j * w j ^ (M + K)) *
          ∑ i ∈ Finset.range K, c i * (w j ^ i)⁻¹ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hinterp]
      _ = ∑ i ∈ Finset.range K, c i * ∑ j, b j * w j ^ (M + K - i) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        have hiK : i < K := Finset.mem_range.1 hi
        have hiN : i ≤ M + K := by omega
        rw [pow_sub₀ _ (hwne j) hiN]
        ring
  obtain ⟨i, hi, himax⟩ := Finset.exists_max_image
    (Finset.range K) (fun i ↦ ‖∑ j, b j * w j ^ (M + K - i)‖)
    ⟨0, Finset.mem_range.2 hK⟩
  refine ⟨M + K - i, ?_, ?_⟩
  · simp only [Finset.mem_Icc]
    have hiK : i < K := Finset.mem_range.1 hi
    omega
  · rw [hidentity]
    calc
      ‖∑ i ∈ Finset.range K, c i * ∑ j, b j * w j ^ (M + K - i)‖ ≤
          ∑ i ∈ Finset.range K,
            ‖c i * ∑ j, b j * w j ^ (M + K - i)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Finset.range K,
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
            ‖∑ j, b j * w j ^ (M + K - q)‖ := by
        apply Finset.sum_le_sum
        intro q hq
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (turanInterpolationCoeff_norm_le v hv (M + K) q) (norm_nonneg _)
      _ ≤ ∑ _q ∈ Finset.range K,
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
            ‖∑ j, b j * w j ^ (M + K - i)‖ := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left (himax q hq) (by positivity)
      _ = (K : ℝ) *
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
          ‖∑ j, b j * w j ^ (M + K - i)‖ := by
        simp [mul_assoc]

/-- Turán's estimate transported from `Fin K` to an arbitrary nonempty
finite set of frequencies. -/
private lemma exists_large_finite_exponential_sum {s : Finset ℕ} (hs : s.Nonempty)
    (n : ℕ → ℕ) (c : ℕ → ℂ) (t₀ δ : ℝ) (M : ℕ) :
    ∃ ν ∈ Finset.Icc (M + 1) (M + s.card),
      ‖∑ k ∈ s, c k * Complex.exp ((n k : ℂ) * ((t₀ : ℂ) * Complex.I))‖ ≤
        (s.card : ℝ) *
          (2 * ((2 : ℝ) ^ (M + s.card) *
            ((s.card + 1 : ℝ) * (2 : ℝ) ^ s.card * (2 : ℝ) ^ s.card))) *
          ‖∑ k ∈ s, c k * Complex.exp
            ((n k : ℂ) * (((t₀ + (ν : ℝ) * δ : ℝ) : ℂ) * Complex.I))‖ := by
  classical
  let e : s ≃ Fin s.card := s.equivFin
  let idx : Fin s.card → ℕ := fun j ↦ (e.symm j).1
  let w : Fin s.card → ℂ := fun j ↦
    Complex.exp ((n (idx j) : ℂ) * ((δ : ℂ) * Complex.I))
  let b : Fin s.card → ℂ := fun j ↦
    c (idx j) * Complex.exp ((n (idx j) : ℂ) * ((t₀ : ℂ) * Complex.I))
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  have hw : ∀ j, ‖w j‖ = 1 := by
    intro j
    dsimp [w]
    rw [Complex.norm_exp]
    have hre : (((n (idx j) : ℂ) * ((δ : ℂ) * Complex.I)).re) = 0 := by simp
    rw [hre, Real.exp_zero]
  obtain ⟨ν, hνmem, hν⟩ := exists_large_powerSum hcard w b hw
  refine ⟨ν, hνmem, ?_⟩
  have hbase : (∑ j, b j) =
      ∑ k ∈ s, c k * Complex.exp ((n k : ℂ) * ((t₀ : ℂ) * Complex.I)) := by
    calc
      (∑ j, b j) = ∑ k : s,
          c k.1 * Complex.exp ((n k.1 : ℂ) * ((t₀ : ℂ) * Complex.I)) := by
        exact e.symm.sum_comp (fun k : s ↦
          c k.1 * Complex.exp ((n k.1 : ℂ) * ((t₀ : ℂ) * Complex.I)))
      _ = ∑ k ∈ s, c k * Complex.exp ((n k : ℂ) * ((t₀ : ℂ) * Complex.I)) := by
        simpa only [Finset.attach_eq_univ] using s.sum_attach (fun k ↦
          c k * Complex.exp ((n k : ℂ) * ((t₀ : ℂ) * Complex.I)))
  have hshift : (∑ j, b j * w j ^ ν) =
      ∑ k ∈ s, c k * Complex.exp
        ((n k : ℂ) * (((t₀ + (ν : ℝ) * δ : ℝ) : ℂ) * Complex.I)) := by
    have hterm : ∀ j : Fin s.card, b j * w j ^ ν =
        c (idx j) * Complex.exp
          ((n (idx j) : ℂ) * (((t₀ + (ν : ℝ) * δ : ℝ) : ℂ) * Complex.I)) := by
      intro j
      dsimp [b, w]
      rw [← Complex.exp_nat_mul]
      calc
        (c (idx j) * Complex.exp
              ((n (idx j) : ℂ) * ((t₀ : ℂ) * Complex.I))) *
            Complex.exp
              ((ν : ℂ) * ((n (idx j) : ℂ) * ((δ : ℂ) * Complex.I))) =
            c (idx j) * Complex.exp
              (((n (idx j) : ℂ) * ((t₀ : ℂ) * Complex.I)) +
                ((ν : ℂ) * ((n (idx j) : ℂ) * ((δ : ℂ) * Complex.I)))) := by
              rw [mul_assoc, ← Complex.exp_add]
        _ = c (idx j) * Complex.exp
              ((n (idx j) : ℂ) * (((t₀ + (ν : ℝ) * δ : ℝ) : ℂ) * Complex.I)) := by
              congr 2
              push_cast
              ring
    calc
      (∑ j, b j * w j ^ ν) = ∑ j : Fin s.card,
          c (idx j) * Complex.exp
            ((n (idx j) : ℂ) * (((t₀ + (ν : ℝ) * δ : ℝ) : ℂ) * Complex.I)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j
      _ = ∑ k : s,
          c k.1 * Complex.exp
            ((n k.1 : ℂ) * (((t₀ + (ν : ℝ) * δ : ℝ) : ℂ) * Complex.I)) := by
        exact e.symm.sum_comp (fun k : s ↦ c k.1 * Complex.exp
          ((n k.1 : ℂ) * (((t₀ + (ν : ℝ) * δ : ℝ) : ℂ) * Complex.I)))
      _ = ∑ k ∈ s, c k * Complex.exp
          ((n k : ℂ) * (((t₀ + (ν : ℝ) * δ : ℝ) : ℂ) * Complex.I)) := by
        simpa only [Finset.attach_eq_univ] using s.sum_attach (fun k ↦ c k * Complex.exp
          ((n k : ℂ) * (((t₀ + (ν : ℝ) * δ : ℝ) : ℂ) * Complex.I)))
  simpa only [hbase, hshift] using hν

/-- A quantitative localization form of Turán's estimate.  Starting from a
large value at a phase `t₀ ∈ [-π,π]`, it produces a comparably large value
immediately to the right of any target phase in that interval (after adding
one period).  The interpolation index is bounded linearly in `card s / d`.
This is the finite-frequency covering input for the disk argument below. -/
private lemma exists_large_finite_exponential_sum_near {s : Finset ℕ}
    (hs : s.Nonempty) (n : ℕ → ℕ) (c : ℕ → ℂ)
    {t₀ target d : ℝ} (ht₀l : -Real.pi ≤ t₀) (ht₀r : t₀ ≤ Real.pi)
    (htl : -Real.pi ≤ target) (htr : target ≤ Real.pi) (hd : 0 < d) :
    ∃ (M ν : ℕ),
      M ≤ Nat.ceil (64 * Real.pi * (s.card : ℝ) / d) ∧
      ν ∈ Finset.Icc (M + 1) (M + s.card) ∧
      0 ≤ t₀ + (ν : ℝ) * (d / (16 * (s.card : ℝ))) -
        (target + 2 * Real.pi) ∧
      t₀ + (ν : ℝ) * (d / (16 * (s.card : ℝ))) -
          (target + 2 * Real.pi) ≤ d / 16 ∧
      ‖∑ k ∈ s, c k * Complex.exp ((n k : ℂ) * ((t₀ : ℂ) * Complex.I))‖ ≤
        (s.card : ℝ) *
          (2 * ((2 : ℝ) ^ (M + s.card) *
            ((s.card + 1 : ℝ) * (2 : ℝ) ^ s.card * (2 : ℝ) ^ s.card))) *
          ‖∑ k ∈ s, c k * Complex.exp
            ((n k : ℂ) * (((t₀ + (ν : ℝ) *
              (d / (16 * (s.card : ℝ))) : ℝ) : ℂ) * Complex.I))‖ := by
  classical
  let K : ℕ := s.card
  have hK : 0 < K := by simpa [K] using Finset.card_pos.mpr hs
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  let δ : ℝ := d / (16 * (K : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let D : ℝ := target + 2 * Real.pi - t₀
  have hD0 : 0 ≤ D := by
    dsimp [D]
    have hpi := Real.pi_pos
    linarith
  have hD4 : D ≤ 4 * Real.pi := by
    dsimp [D]
    linarith
  let M : ℕ := Nat.floor (D / δ)
  have hfloor : (M : ℝ) ≤ D / δ := by
    exact_mod_cast Nat.floor_le (div_nonneg hD0 hδ.le)
  have hltfloor : D / δ < (M : ℝ) + 1 := by
    simpa [M] using Nat.lt_floor_add_one (D / δ)
  have hMboundR : (M : ℝ) ≤ 64 * Real.pi * (K : ℝ) / d := by
    calc
      (M : ℝ) ≤ D / δ := hfloor
      _ ≤ (4 * Real.pi) / δ :=
        div_le_div_of_nonneg_right hD4 hδ.le
      _ = 64 * Real.pi * (K : ℝ) / d := by
        dsimp [δ]
        field_simp
        ring
  have hMbound : M ≤ Nat.ceil (64 * Real.pi * (K : ℝ) / d) := by
    have hcast : (M : ℝ) ≤ (Nat.ceil (64 * Real.pi * (K : ℝ) / d) : ℕ) :=
      hMboundR.trans (Nat.le_ceil _)
    exact_mod_cast hcast
  obtain ⟨ν, hνmem, hν⟩ :=
    exists_large_finite_exponential_sum hs n c t₀ δ M
  have hνlow : (M : ℝ) + 1 ≤ (ν : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.1 hνmem).1
  have hνhigh : (ν : ℝ) ≤ (M : ℝ) + K := by
    exact_mod_cast (Finset.mem_Icc.1 hνmem).2
  have hlow : D ≤ (ν : ℝ) * δ := by
    have hdiv : D / δ < (ν : ℝ) := hltfloor.trans_le hνlow
    exact (div_lt_iff₀ hδ).1 hdiv |>.le
  have hhigh : (ν : ℝ) * δ - D ≤ d / 16 := by
    have hMδ : (M : ℝ) * δ ≤ D := (le_div_iff₀ hδ).1 hfloor
    have hνδ : (ν : ℝ) * δ ≤ ((M : ℝ) + K) * δ :=
      mul_le_mul_of_nonneg_right hνhigh hδ.le
    have hKδ : (K : ℝ) * δ = d / 16 := by
      dsimp [δ]
      field_simp
    nlinarith
  refine ⟨M, ν, ?_, hνmem, ?_, ?_, ?_⟩
  · simpa [K] using hMbound
  · dsimp [D, δ] at hlow ⊢
    linarith
  · dsimp [D, δ] at hhigh ⊢
    linarith
  · simpa only [K, δ] using hν

/-- Equally spaced target phases used to cover one imaginary period.  The
filter removes the (at most one) overshooting endpoint, so every retained
target belongs to `[-π,π]`. -/
private noncomputable def phaseGrid (d : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil (4 * Real.pi / d) + 1)).filter
    (fun j => -Real.pi + (j : ℝ) * d / 2 ≤ Real.pi)

private noncomputable def phaseTarget (d : ℝ) (j : ℕ) : ℝ :=
  -Real.pi + (j : ℝ) * d / 2

private lemma phaseGrid_card_le (d : ℝ) :
    (phaseGrid d).card ≤ Nat.ceil (4 * Real.pi / d) + 1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- Every phase has a representative modulo the exponential period lying
less than `d/2` to the right of a target in `phaseGrid d`. -/
private lemma exists_phaseGrid_target {d : ℝ} (hd : 0 < d) (t : ℝ) :
    ∃ j ∈ phaseGrid d,
      let u := (Complex.exp ((t : ℂ) * Complex.I)).arg
      Complex.exp ((u : ℂ) * Complex.I) =
          Complex.exp ((t : ℂ) * Complex.I) ∧
        0 ≤ u - phaseTarget d j ∧ u - phaseTarget d j < d / 2 := by
  let z : ℂ := Complex.exp ((t : ℂ) * Complex.I)
  let u : ℝ := z.arg
  have hzNorm : ‖z‖ = 1 := by
    dsimp [z]
    rw [Complex.norm_exp]
    simp
  have hzNe : z ≠ 0 := by dsimp [z]; exact Complex.exp_ne_zero _
  have huLower : -Real.pi ≤ u := (Complex.neg_pi_lt_arg z).le
  have huUpper : u ≤ Real.pi := Complex.arg_le_pi _
  let q : ℝ := 2 * (u + Real.pi) / d
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) hd.le
  let j : ℕ := Nat.floor q
  have hjq : (j : ℝ) ≤ q := by exact_mod_cast Nat.floor_le hq0
  have hqj : q < (j : ℝ) + 1 := by simpa [j] using Nat.lt_floor_add_one q
  have htargetLower : 0 ≤ u - phaseTarget d j := by
    have hmul := (le_div_iff₀ hd).1 hjq
    dsimp [phaseTarget, q] at hmul ⊢
    nlinarith
  have htargetUpper : u - phaseTarget d j < d / 2 := by
    have hmul := (div_lt_iff₀ hd).1 hqj
    dsimp [phaseTarget, q] at hmul ⊢
    nlinarith
  have hjBoundR : (j : ℝ) ≤ 4 * Real.pi / d := by
    calc
      (j : ℝ) ≤ q := hjq
      _ ≤ 4 * Real.pi / d := by
        dsimp [q]
        apply (div_le_div_iff_of_pos_right hd).2
        linarith
  have hjCeil : j ≤ Nat.ceil (4 * Real.pi / d) := by
    have hcast : (j : ℝ) ≤ (Nat.ceil (4 * Real.pi / d) : ℕ) :=
      hjBoundR.trans (Nat.le_ceil _)
    exact_mod_cast hcast
  have hjRange : j ∈ Finset.range (Nat.ceil (4 * Real.pi / d) + 1) :=
    Finset.mem_range.2 (by omega)
  have hjTarget : phaseTarget d j ≤ Real.pi := by
    dsimp [phaseTarget] at htargetLower ⊢
    linarith
  have hjGrid : j ∈ phaseGrid d := by
    exact Finset.mem_filter.2 ⟨hjRange, hjTarget⟩
  refine ⟨j, hjGrid, ?_, htargetLower, htargetUpper⟩
  have hzPolar := Complex.norm_mul_exp_arg_mul_I z
  rw [hzNorm, Complex.ofReal_one, one_mul] at hzPolar
  simpa [z, u] using hzPolar

/-- A selected coefficient of a finite gap polynomial is attained in norm at
some phase of the unit circle. -/
private lemma exists_phase_ge_gapTerm {n : ℕ → ℕ} (hn : StrictMono n)
    (a : ℕ → ℂ) {s : Finset ℕ} {j : ℕ} (hj : j ∈ s) (σ : ℝ) :
    ∃ t₀ : ℝ, -Real.pi ≤ t₀ ∧ t₀ ≤ Real.pi ∧
      ‖a j‖ * Real.exp ((n j : ℝ) * σ) ≤
        ‖∑ k ∈ s, (a k * Complex.exp ((n k : ℂ) * (σ : ℂ))) *
          Complex.exp ((n k : ℂ) * ((t₀ : ℂ) * Complex.I))‖ := by
  let c : ℕ → ℂ := fun k => a k * Complex.exp ((n k : ℂ) * (σ : ℂ))
  let P : ℂ[X] := finiteGapPolynomial n c s
  obtain ⟨ζ, hζnorm, hζ⟩ := exists_unit_norm_eval_ge_coeff P (n j)
  have hcoeff : P.coeff (n j) = c j := finiteGapPolynomial_coeff_of_mem hn hj
  let t₀ : ℝ := ζ.arg
  have hζne : ζ ≠ 0 := norm_ne_zero_iff.mp (by rw [hζnorm]; norm_num)
  have hexpArg : Complex.exp ((t₀ : ℂ) * Complex.I) = ζ := by
    have hpolar := Complex.norm_mul_exp_arg_mul_I ζ
    rw [hζnorm, Complex.ofReal_one, one_mul] at hpolar
    simpa [t₀] using hpolar
  have heval : P.eval ζ =
      ∑ k ∈ s, c k * Complex.exp ((n k : ℂ) * ((t₀ : ℂ) * Complex.I)) := by
    rw [show P = finiteGapPolynomial n c s by rfl, finiteGapPolynomial_eval]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Complex.exp_nat_mul, hexpArg]
  refine ⟨t₀, (Complex.neg_pi_lt_arg ζ).le, Complex.arg_le_pi ζ, ?_⟩
  have hcj : ‖c j‖ = ‖a j‖ * Real.exp ((n j : ℝ) * σ) := by
    dsimp [c]
    rw [norm_mul, Complex.norm_exp]
    simp
  rw [← hcj, ← hcoeff, ← heval]
  exact hζ

private noncomputable def turanFactor (K M : ℕ) : ℝ :=
  (K : ℝ) *
    (2 * ((2 : ℝ) ^ (M + K) *
      ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K)))

/-- The deliberately coarse Turán factor used above has logarithm linear in
the number of frequencies when its translation index is linear in that
number. -/
private lemma log_turanFactor_le {K M : ℕ} (hK : 0 < K) {d : ℝ} (hd : 0 < d)
    (hM : (M : ℝ) ≤ 64 * Real.pi * (K : ℝ) / d + 1) :
    Real.log (turanFactor K M) ≤
      (64 * Real.pi / d + 10) * ((K : ℝ) + 1) := by
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hK1 : 0 < (K + 1 : ℝ) := by positivity
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hlogK : Real.log (K : ℝ) ≤ (K : ℝ) := by
    exact (Real.log_le_sub_one_of_pos hKR).trans (by linarith)
  have hlogK1 : Real.log (K + 1 : ℝ) ≤ (K : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hK1
    norm_num at h
    exact h
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos htwo
    linarith
  have hM' : (M : ℝ) ≤ (64 * Real.pi / d) * (K : ℝ) + 1 := by
    convert hM using 1 <;> ring
  have hlogEq : Real.log (turanFactor K M) =
      Real.log (K : ℝ) + Real.log 2 +
        ((M + K : ℕ) : ℝ) * Real.log 2 +
        Real.log (K + 1 : ℝ) +
        (K : ℝ) * Real.log 2 + (K : ℝ) * Real.log 2 := by
    have hinner : Real.log ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K) =
        Real.log (K + 1 : ℝ) + (K : ℝ) * Real.log 2 +
          (K : ℝ) * Real.log 2 := by
      rw [Real.log_mul (by positivity : (K + 1 : ℝ) * 2 ^ K ≠ 0) (by positivity),
        Real.log_mul (by positivity : (K + 1 : ℝ) ≠ 0) (by positivity)]
      rw [Real.log_pow]
    dsimp [turanFactor]
    rw [Real.log_mul hKR.ne' (by positivity),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
      Real.log_mul (by positivity : (2 : ℝ) ^ (M + K) ≠ 0) (by positivity),
      Real.log_pow, hinner]
    push_cast
    ring
  rw [hlogEq]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcoef : 0 ≤ 64 * Real.pi / d := by positivity
  have hlog20 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hMKmul : ((M + K : ℕ) : ℝ) * Real.log 2 ≤ (M + K : ℕ) :=
    mul_le_of_le_one_right (by positivity) hlog2
  have hKmul : (K : ℝ) * Real.log 2 ≤ K :=
    mul_le_of_le_one_right (by positivity) hlog2
  push_cast at hMKmul
  rw [Nat.cast_add]
  nlinarith

/-- Simultaneous finite-frequency localization on a complete phase grid. -/
private lemma exists_turan_phase_cover {n : ℕ → ℕ} (hn : StrictMono n)
    (a : ℕ → ℂ) {s : Finset ℕ} {j : ℕ} (hj : j ∈ s)
    {σ d : ℝ} (hd : 0 < d) :
    ∃ (center : {q : ℕ // q ∈ phaseGrid d} → ℝ)
      (M ν : {q : ℕ // q ∈ phaseGrid d} → ℕ),
      (∀ q,
        M q ≤ Nat.ceil (64 * Real.pi * (s.card : ℝ) / d) ∧
        ν q ∈ Finset.Icc (M q + 1) (M q + s.card) ∧
        0 ≤ center q - (phaseTarget d q.1 + 2 * Real.pi) ∧
        center q - (phaseTarget d q.1 + 2 * Real.pi) ≤ d / 16 ∧
        ‖∑ k ∈ s, (a k * Complex.exp ((n k : ℂ) * (σ : ℂ))) *
            Complex.exp ((n k : ℂ) * ((center q : ℂ) * Complex.I))‖ *
            turanFactor s.card (M q) ≥
          ‖a j‖ * Real.exp ((n j : ℝ) * σ)) ∧
      ∀ t : ℝ, ∃ q : {q : ℕ // q ∈ phaseGrid d}, ∃ u : ℝ,
        Complex.exp ((u : ℂ) * Complex.I) =
          Complex.exp ((t : ℂ) * Complex.I) ∧
        |(u + 2 * Real.pi) - center q| < 9 * d / 16 := by
  classical
  have hs : s.Nonempty := ⟨j, hj⟩
  obtain ⟨t₀, ht₀l, ht₀r, ht₀large⟩ := exists_phase_ge_gapTerm hn a hj σ
  have hexists : ∀ q : {q : ℕ // q ∈ phaseGrid d},
      ∃ M ν : ℕ,
        M ≤ Nat.ceil (64 * Real.pi * (s.card : ℝ) / d) ∧
        ν ∈ Finset.Icc (M + 1) (M + s.card) ∧
        0 ≤ t₀ + (ν : ℝ) * (d / (16 * (s.card : ℝ))) -
          (phaseTarget d q.1 + 2 * Real.pi) ∧
        t₀ + (ν : ℝ) * (d / (16 * (s.card : ℝ))) -
            (phaseTarget d q.1 + 2 * Real.pi) ≤ d / 16 ∧
        ‖∑ k ∈ s, (a k * Complex.exp ((n k : ℂ) * (σ : ℂ))) *
            Complex.exp ((n k : ℂ) * ((t₀ : ℂ) * Complex.I))‖ ≤
          turanFactor s.card M *
            ‖∑ k ∈ s, (a k * Complex.exp ((n k : ℂ) * (σ : ℂ))) *
              Complex.exp ((n k : ℂ) *
                (((t₀ + (ν : ℝ) * (d / (16 * (s.card : ℝ))) : ℝ) : ℂ) *
                  Complex.I))‖ := by
    intro q
    have htarget := Finset.mem_filter.1 q.2 |>.2
    have htargetLower : -Real.pi ≤ phaseTarget d q.1 := by
      dsimp [phaseTarget]
      exact le_add_of_nonneg_right (div_nonneg
        (mul_nonneg (Nat.cast_nonneg _) hd.le) (by norm_num))
    simpa only [turanFactor] using
      exists_large_finite_exponential_sum_near hs n
        (fun k => a k * Complex.exp ((n k : ℂ) * (σ : ℂ)))
        ht₀l ht₀r htargetLower htarget hd
  choose M ν hM hν hlow hhigh hlarge using hexists
  let center : {q : ℕ // q ∈ phaseGrid d} → ℝ := fun q =>
    t₀ + (ν q : ℝ) * (d / (16 * (s.card : ℝ)))
  refine ⟨center, M, ν, ?_, ?_⟩
  · intro q
    refine ⟨hM q, hν q, ?_, ?_, ?_⟩
    · simpa [center] using hlow q
    · simpa [center] using hhigh q
    · calc
        ‖a j‖ * Real.exp ((n j : ℝ) * σ) ≤
            ‖∑ k ∈ s, (a k * Complex.exp ((n k : ℂ) * (σ : ℂ))) *
              Complex.exp ((n k : ℂ) * ((t₀ : ℂ) * Complex.I))‖ := ht₀large
        _ ≤ turanFactor s.card (M q) *
            ‖∑ k ∈ s, (a k * Complex.exp ((n k : ℂ) * (σ : ℂ))) *
              Complex.exp ((n k : ℂ) * ((center q : ℂ) * Complex.I))‖ := by
          simpa [center, mul_comm, mul_left_comm, mul_assoc] using hlarge q
        _ = ‖∑ k ∈ s, (a k * Complex.exp ((n k : ℂ) * (σ : ℂ))) *
              Complex.exp ((n k : ℂ) * ((center q : ℂ) * Complex.I))‖ *
              turanFactor s.card (M q) := by ring
  · intro t
    obtain ⟨j₀, hj₀, hexp, hlowGrid, hhighGrid⟩ := exists_phaseGrid_target hd t
    let q : {q : ℕ // q ∈ phaseGrid d} := ⟨j₀, by simpa using hj₀⟩
    let u : ℝ := (Complex.exp ((t : ℂ) * Complex.I)).arg
    refine ⟨q, u, ?_, ?_⟩
    · simpa [u] using hexp
    · have hcLow := hlow q
      have hcHigh := hhigh q
      have hdiff : -(d / 16) ≤
          (u + 2 * Real.pi) - center q := by
        dsimp [center, q] at hcHigh ⊢
        linarith
      have hdiff' : (u + 2 * Real.pi) - center q < 9 * d / 16 := by
        dsimp [center, q] at hcLow ⊢
        linarith
      rw [abs_lt]
      constructor
      · have : -(9 * d / 16) < -(d / 16) := by nlinarith
        exact this.trans_le hdiff
      · exact hdiff'

/-! ### A quantitative zero-free minimum-modulus estimate -/

/-- A zero-free analytic function on a disk cannot fall much below its value at the
center when its boundary maximum is controlled.  This is the Borel--Carathéodory
estimate applied to an analytic logarithm, constructed from a primitive of `g'/g`. -/
private lemma log_norm_lower_of_zeroFree {g : ℂ → ℂ} {R M r : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall 0 R))
    (hne : ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0)
    (hM : 0 < M) (hbound : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖g z‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    Real.log ‖g 0‖ - 2 * (Real.log M - Real.log ‖g 0‖ + 1) * r / (R - r) ≤
      Real.log ‖g z‖ := by
  have hRne : R ≠ 0 := hR.ne'
  have h0closed : (0 : ℂ) ∈ Metric.closedBall 0 R := by simp [hR.le]
  have hg0 : g 0 ≠ 0 := hne 0 h0closed
  have hgdiff : DifferentiableOn ℂ g (Metric.ball 0 R) :=
    hg.differentiableOn.mono Metric.ball_subset_closedBall
  have hgcl : DiffContOnCl ℂ g (Metric.ball 0 R) := by
    refine ⟨hgdiff, ?_⟩
    rw [closure_ball 0 hRne]
    exact hg.continuousOn
  have hg_le : ∀ w ∈ Metric.closedBall (0 : ℂ) R, ‖g w‖ ≤ M := by
    intro w hw
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hgcl
      ?_ ?_
    · intro u hu
      rw [frontier_ball _ hRne] at hu
      exact hbound u hu
    · rwa [closure_ball 0 hRne]
  have hg0norm : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hM0 : ‖g 0‖ ≤ M := hg_le 0 h0closed
  have hlogle : Real.log ‖g 0‖ ≤ Real.log M :=
    Real.strictMonoOn_log.monotoneOn hg0norm hM hM0
  let q : ℂ → ℂ := fun w ↦ deriv g w / g w
  have hqdiff : DifferentiableOn ℂ q (Metric.ball 0 R) := by
    apply (hgdiff.deriv Metric.isOpen_ball).div hgdiff
    intro w hw
    exact hne w (Metric.ball_subset_closedBall hw)
  obtain ⟨H, hH0, hHderiv⟩ :=
    hqdiff.isExactOn_ball.with_val_at (0 : ℂ) 0
  have hHdiff : DifferentiableOn ℂ H (Metric.ball 0 R) := by
    intro w hw
    exact (hHderiv w hw).differentiableAt.differentiableWithinAt
  let k : ℂ → ℂ := fun w ↦ Complex.exp (H w) / g w
  have hkdiff : DifferentiableOn ℂ k (Metric.ball 0 R) := by
    exact (hHdiff.cexp).div hgdiff
      (fun w hw ↦ hne w (Metric.ball_subset_closedBall hw))
  have hkderiv : Set.EqOn (deriv k) 0 (Metric.ball (0 : ℂ) R) := by
    intro w hw
    change deriv k w = 0
    have hHw := hHderiv w hw
    have hgw := ((hgdiff w hw).differentiableAt
      (Metric.isOpen_ball.mem_nhds hw)).hasDerivAt
    have hkw := hHw.cexp.div hgw (hne w (Metric.ball_subset_closedBall hw))
    have hd := hkw.deriv
    change deriv k w =
      (Complex.exp (H w) * q w * g w - Complex.exp (H w) * deriv g w) /
        g w ^ 2 at hd
    rw [hd]
    dsimp [q]
    field_simp [hne w (Metric.ball_subset_closedBall hw)]
    ring
  have h0ball : (0 : ℂ) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
  have hkconst : ∀ w ∈ Metric.ball (0 : ℂ) R, k w = k 0 := by
    intro w hw
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball 0 R).isPreconnected hkdiff hkderiv hw h0ball
  have hexp_eq : ∀ w ∈ Metric.ball (0 : ℂ) R,
      Complex.exp (H w) = g w / g 0 := by
    intro w hw
    have hk := hkconst w hw
    dsimp [k] at hk
    rw [hH0, Complex.exp_zero] at hk
    have hgw : g w ≠ 0 := hne w (Metric.ball_subset_closedBall hw)
    field_simp [hgw, hg0] at hk
    exact (eq_div_iff hg0).2 hk
  have hre_eq : ∀ w ∈ Metric.ball (0 : ℂ) R,
      (H w).re = Real.log ‖g w‖ - Real.log ‖g 0‖ := by
    intro w hw
    have he := congrArg norm (hexp_eq w hw)
    rw [Complex.norm_exp, norm_div] at he
    have hgw : 0 < ‖g w‖ := norm_pos_iff.mpr (hne w (Metric.ball_subset_closedBall hw))
    apply Real.exp_injective
    rw [he, Real.exp_sub, Real.exp_log hgw, Real.exp_log hg0norm]
  let D : ℝ := Real.log M - Real.log ‖g 0‖ + 1
  have hD : 0 < D := by dsimp [D]; linarith
  have hmaps : Set.MapsTo H (Metric.ball (0 : ℂ) R) {w | w.re ≤ D} := by
    intro w hw
    change (H w).re ≤ D
    rw [hre_eq w hw]
    have hgwpos : 0 < ‖g w‖ := norm_pos_iff.mpr (hne w (Metric.ball_subset_closedBall hw))
    have hlogw : Real.log ‖g w‖ ≤ Real.log M :=
      Real.strictMonoOn_log.monotoneOn hgwpos hM (hg_le w (Metric.ball_subset_closedBall hw))
    dsimp [D]
    linarith
  have hzball : z ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hz.trans_lt hrR
  have hBC := Complex.borelCaratheodory_zero hD hHdiff hmaps hR hzball hH0
  have hdenpos : 0 < R - ‖z‖ := sub_pos.mpr (hz.trans_lt hrR)
  have hdenr : 0 < R - r := sub_pos.mpr hrR
  have hnormH : ‖H z‖ ≤ 2 * D * r / (R - r) := by
    calc
      ‖H z‖ ≤ 2 * D * ‖z‖ / (R - ‖z‖) := hBC
      _ ≤ 2 * D * r / (R - r) := by
        apply div_le_div₀ (by positivity)
        · exact mul_le_mul_of_nonneg_left hz (by positivity)
        · exact hdenr
        · exact sub_le_sub_left hz R
  have hre_lower : -(2 * D * r / (R - r)) ≤ (H z).re := by
    calc
      -(2 * D * r / (R - r)) ≤ -‖H z‖ := neg_le_neg hnormH
      _ ≤ (H z).re := neg_le_of_abs_le (Complex.abs_re_le_norm (H z))
  rw [hre_eq z hzball] at hre_lower
  dsimp [D] at hre_lower
  linarith

/-- Between radii two and three one can choose a circle containing no zero of a
nonzero analytic function.  Compactness makes the set of zeros in the larger disk
finite, so this is a finite-avoidance argument. -/
private lemma exists_radius_avoiding_zeros {p : ℂ → ℂ}
    (hp : AnalyticOnNhd ℂ p (Metric.closedBall 0 3)) (hp0 : p 0 ≠ 0) :
    ∃ R : ℝ, 2 < R ∧ R < 5 / 2 ∧ ∀ z ∈ Metric.sphere (0 : ℂ) R, p z ≠ 0 := by
  classical
  have hm : MeromorphicOn p (Metric.closedBall (0 : ℂ) 3) := hp.meromorphicOn
  have horders : ∀ u : Metric.closedBall (0 : ℂ) 3,
      meromorphicOrderAt p u ≠ ⊤ := by
    apply (hm.exists_meromorphicOrderAt_ne_top_iff_forall
      (Metric.isConnected_closedBall (by norm_num))).1
    refine ⟨⟨0, by norm_num [Metric.mem_closedBall]⟩, ?_⟩
    have hzero : meromorphicOrderAt p 0 = 0 :=
      (hp 0 (by norm_num [Metric.mem_closedBall])).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hp0
    simp [hzero]
  let t : Finset ℂ := hm.divisor_ball_support_finite.toFinset
  obtain ⟨R, hRmem, hRavoid⟩ :=
    (Set.Ioo_infinite (show (2 : ℝ) < 5 / 2 by norm_num)).exists_notMem_finset
    (t.image norm)
  refine ⟨R, hRmem.1, hRmem.2, ?_⟩
  intro z hz hpz
  have hznorm : ‖z‖ = R := by simpa [Metric.mem_sphere] using hz
  have hzclosed : z ∈ Metric.closedBall (0 : ℂ) 3 := by
    rw [Metric.mem_closedBall, dist_zero_right, hznorm]
    exact hRmem.2.le.trans (by norm_num)
  have hdivne : (MeromorphicOn.divisor p (Metric.ball 0 3)) z ≠ 0 := by
    rw [(hm.mono_set Metric.ball_subset_closedBall).divisor_apply]
    · rw [ne_eq, WithTop.untop₀_eq_zero]
      simp only [not_or]
      exact ⟨fun hzero ↦ ((hp z hzclosed).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mp hzero) hpz, horders ⟨z, hzclosed⟩⟩
    · rw [Metric.mem_ball, dist_zero_right, hznorm]
      exact hRmem.2.trans (by norm_num)
  have hzmem : z ∈ t := by
    dsimp [t]
    simpa only [Set.Finite.mem_toFinset, Function.mem_support] using hdivne
  apply hRavoid
  rw [Finset.mem_image]
  exact ⟨z, hzmem, hznorm⟩

private lemma canonicalFactor_norm_at_zero_ge_one {R : ℝ} (hR : 0 < R)
    {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) R) (hu0 : u ≠ 0) :
    1 ≤ ‖Complex.canonicalFactor R u 0‖ := by
  have hunorm : ‖u‖ < R := by simpa [Metric.mem_ball] using hu
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul]
  simp only [mul_zero, sub_zero, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hR, zero_sub, norm_neg]
  have hunormpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  rw [le_div_iff₀ (mul_pos hR hunormpos)]
  nlinarith

private lemma canonicalFactor_norm_le_four_div {R : ℝ} (hR2 : 2 < R) (hR3 : R < 3)
    {u z : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) R) (hz : ‖z‖ ≤ 1) (hzu : z ≠ u) :
    ‖Complex.canonicalFactor R u z‖ ≤ 4 / ‖z - u‖ := by
  have hR : 0 < R := by linarith
  have hunorm : ‖u‖ < R := by simpa [Metric.mem_ball] using hu
  have hdist : 0 < ‖z - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzu)
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR]
  apply (div_le_div_iff₀ (mul_pos hR hdist) hdist).2
  calc
    ‖(R : ℂ) ^ 2 - starRingEnd ℂ u * z‖ * ‖z - u‖ ≤
        (R ^ 2 + ‖u‖ * ‖z‖) * ‖z - u‖ := by
      gcongr
      calc
        ‖(R : ℂ) ^ 2 - starRingEnd ℂ u * z‖ ≤
            ‖(R : ℂ) ^ 2‖ + ‖starRingEnd ℂ u * z‖ := norm_sub_le _ _
        _ = R ^ 2 + ‖u‖ * ‖z‖ := by simp [norm_pow, abs_of_pos hR]
    _ ≤ (R ^ 2 + R) * ‖z - u‖ := by
      gcongr
      calc
        ‖u‖ * ‖z‖ ≤ R * 1 := mul_le_mul hunorm.le hz (norm_nonneg z) hR.le
        _ = R := mul_one R
    _ ≤ (4 * R) * ‖z - u‖ := by
      gcongr
      nlinarith
    _ = 4 * (R * ‖z - u‖) := by ring

/-- Local minimum-modulus estimate after extracting the zeros in a disk.  The
finite set `t` contains every extracted zero, with its analytic multiplicity.
The loss not involving `t` is controlled solely by the logarithmic gap between
the boundary maximum and the value at the center. -/
private lemma exists_local_minimum_estimate {p : ℂ → ℂ} {M : ℝ}
    (hp : AnalyticOnNhd ℂ p (Metric.closedBall 0 3)) (hp0 : p 0 ≠ 0)
    (hM : 1 ≤ M) (hpM : ∀ z ∈ Metric.sphere (0 : ℂ) 3, ‖p z‖ ≤ M) :
    ∃ (R : ℝ) (t : Finset ℂ), 2 < R ∧ R < 5 / 2 ∧
      (∀ u, u ∈ t ↔
        (MeromorphicOn.divisor p (Metric.ball (0 : ℂ) R)) u ≠ 0) ∧
      (∀ u, 0 ≤ (MeromorphicOn.divisor p (Metric.ball (0 : ℂ) R)) u) ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → p z ≠ 0 →
        Real.log ‖p 0‖ - 2 * (Real.log M - Real.log ‖p 0‖ + 1) +
            ∑ u ∈ t, ((MeromorphicOn.divisor p (Metric.ball 0 R)) u : ℝ) *
              Real.log (‖z - u‖ / 4) ≤ Real.log ‖p z‖ := by
  classical
  obtain ⟨R, hR2, hR25, hnoSphere⟩ := exists_radius_avoiding_zeros hp hp0
  have hR3 : R < 3 := hR25.trans (by norm_num)
  have hR : 0 < R := by linarith
  have hclosed : Metric.closedBall (0 : ℂ) R ⊆ Metric.closedBall 0 3 :=
    Metric.closedBall_subset_closedBall hR3.le
  have hpR : AnalyticOnNhd ℂ p (Metric.closedBall (0 : ℂ) R) := hp.mono hclosed
  have hmR : MeromorphicOn p (Metric.closedBall (0 : ℂ) R) := hpR.meromorphicOn
  have horders : ∀ u : Metric.closedBall (0 : ℂ) R,
      meromorphicOrderAt p u ≠ ⊤ := by
    apply (hmR.exists_meromorphicOrderAt_ne_top_iff_forall
      (Metric.isConnected_closedBall hR.le)).1
    refine ⟨⟨0, by simp [hR.le]⟩, ?_⟩
    have hzero : meromorphicOrderAt p 0 = 0 :=
      (hpR 0 (by simp [hR.le])).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hp0
    simp [hzero]
  obtain ⟨g, D⟩ := hmR.exists_ecanonicalDecomp horders
  have hdivSphere : MeromorphicOn.divisor p (Metric.sphere (0 : ℂ) R) = 0 := by
    ext u
    by_cases hu : u ∈ Metric.sphere (0 : ℂ) R
    · rw [(hmR.mono_set Metric.sphere_subset_closedBall).divisor_apply hu]
      have hpu : p u ≠ 0 := hnoSphere u hu
      have horder : meromorphicOrderAt p u = 0 :=
        (hpR u (Metric.sphere_subset_closedBall hu)).meromorphicNFAt
          |>.meromorphicOrderAt_eq_zero_iff.mpr hpu
      simp [horder]
    · exact (MeromorphicOn.divisor p (Metric.sphere 0 R)).apply_eq_zero_of_notMem hu
  let divR := MeromorphicOn.divisor p (Metric.ball (0 : ℂ) R)
  let t : Finset ℂ := D.meromorphicOn.divisor_ball_support_finite.toFinset
  have ht : ∀ u, u ∈ t ↔ divR u ≠ 0 := by
    intro u
    simp only [t, Set.Finite.mem_toFinset, Function.mem_support, divR]
  have hdiv_nonneg : ∀ u, 0 ≤ divR u := by
    exact fun u ↦ (MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hpR.mono Metric.ball_subset_closedBall)) u
  have hlogg0 : Real.log ‖p 0‖ ≤ Real.log ‖g 0‖ := by
    have horder0 : meromorphicOrderAt p 0 = 0 :=
      (hpR 0 (by simp [hR.le])).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hp0
    have heq := D.log_norm_eq (w := (0 : ℂ)) (by simp [hR.le]) horder0 hR
    rw [hdivSphere] at heq
    have hbzero : (∑ᶠ i : ℂ, ((0 : Function.locallyFinsuppWithin
        (Metric.sphere (0 : ℂ) R) ℤ) i : ℝ) * Real.log ‖(0 : ℂ) - i‖) = 0 := by simp
    rw [hbzero, sub_zero,
      (hpR 0 (by simp [hR.le])).meromorphicTrailingCoeffAt_of_ne_zero hp0] at heq
    change Real.log ‖g 0‖ =
      (∑ᶠ i, (divR i : ℝ) * Real.log ‖Complex.canonicalFactor R i 0‖) +
        Real.log ‖p 0‖ at heq
    rw [heq]
    exact le_add_of_nonneg_left (finsum_nonneg fun u ↦ by
      change 0 ≤ (divR u : ℝ) * Real.log ‖Complex.canonicalFactor R u 0‖
      by_cases hdu : divR u = 0
      · rw [hdu, Int.cast_zero, zero_mul]
      have hu : u ∈ Metric.ball (0 : ℂ) R := divR.supportWithinDomain hdu
      have hu0 : u ≠ 0 := by
        intro hu0
        subst u
        have horder := (hpR 0 (by simp [hR.le])).meromorphicNFAt
          |>.meromorphicOrderAt_eq_zero_iff.mpr hp0
        exact hdu (by simp [divR, (hmR.mono_set Metric.ball_subset_closedBall).divisor_apply,
          hR, horder])
      have hmreal : 0 ≤ (divR u : ℝ) := by exact_mod_cast hdiv_nonneg u
      exact mul_nonneg hmreal
        (Real.log_nonneg (canonicalFactor_norm_at_zero_ge_one hR hu hu0)))
  have hgBoundary : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖g z‖ ≤ M := by
    intro z hz
    have hpz : p z ≠ 0 := hnoSphere z hz
    have horderz : meromorphicOrderAt p z = 0 :=
      (hpR z (Metric.sphere_subset_closedBall hz)).meromorphicNFAt
        |>.meromorphicOrderAt_eq_zero_iff.mpr hpz
    have heq := D.log_norm_eq (w := z) (Metric.sphere_subset_closedBall hz) horderz hR
    rw [hdivSphere] at heq
    have hinner : (∑ᶠ u, (divR u : ℝ) *
        Real.log ‖Complex.canonicalFactor R u z‖) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro u
      by_cases hdu : divR u = 0
      · simp [hdu]
      have hu := divR.supportWithinDomain hdu
      rw [Complex.norm_canonicalFactor_eval_circle_eq_one hu hz, Real.log_one, mul_zero]
    have hbzero : (∑ᶠ i : ℂ, ((0 : Function.locallyFinsuppWithin
        (Metric.sphere (0 : ℂ) R) ℤ) i : ℝ) * Real.log ‖z - i‖) = 0 := by simp
    rw [hbzero, sub_zero,
      (hpR z (Metric.sphere_subset_closedBall hz)).meromorphicTrailingCoeffAt_of_ne_zero hpz]
      at heq
    change Real.log ‖g z‖ =
      (∑ᶠ u, (divR u : ℝ) * Real.log ‖Complex.canonicalFactor R u z‖) +
        Real.log ‖p z‖ at heq
    rw [hinner, zero_add] at heq
    have hgpos : 0 < ‖g z‖ := norm_pos_iff.mpr (D.ne_zero z (Metric.sphere_subset_closedBall hz))
    have hppos : 0 < ‖p z‖ := norm_pos_iff.mpr hpz
    have hnormeq : ‖g z‖ = ‖p z‖ := by
      calc
        ‖g z‖ = Real.exp (Real.log ‖g z‖) := (Real.exp_log hgpos).symm
        _ = Real.exp (Real.log ‖p z‖) := by rw [heq]
        _ = ‖p z‖ := Real.exp_log hppos
    rw [hnormeq]
    have hznorm : ‖z‖ = R := by simpa [Metric.mem_sphere] using hz
    have hz3 : z ∈ Metric.closedBall (0 : ℂ) 3 := by
      rw [Metric.mem_closedBall, dist_zero_right, hznorm]
      exact hR3.le
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      ⟨hp.differentiableOn.mono Metric.ball_subset_closedBall,
        by rw [closure_ball 0 (by norm_num : (3 : ℝ) ≠ 0)]; exact hp.continuousOn⟩
      ?_ ?_
    · intro w hw
      rw [frontier_ball 0 (by norm_num : (3 : ℝ) ≠ 0)] at hw
      exact hpM w hw
    · rwa [closure_ball 0 (by norm_num : (3 : ℝ) ≠ 0)]
  refine ⟨R, t, hR2, hR25, ?_, hdiv_nonneg, ?_⟩
  · exact fun u ↦ by simpa [divR] using ht u
  intro z hz hpz
  have hglower := log_norm_lower_of_zeroFree hR (show (0 : ℝ) ≤ 1 by norm_num)
    (show (1 : ℝ) < R by linarith)
    D.analyticOnNhd D.ne_zero (lt_of_lt_of_le zero_lt_one hM) hgBoundary hz
  have hbase : Real.log ‖p 0‖ - 2 * (Real.log M - Real.log ‖p 0‖ + 1) ≤
      Real.log ‖g z‖ := by
    have hD0 : 0 ≤ Real.log M - Real.log ‖g 0‖ + 1 := by
      have hg0leM : ‖g 0‖ ≤ M := by
        refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
          ⟨D.analyticOnNhd.differentiableOn.mono Metric.ball_subset_closedBall,
            by rw [closure_ball 0 hR.ne']; exact D.analyticOnNhd.continuousOn⟩
          ?_ (by rw [closure_ball 0 hR.ne']; simp [hR.le])
        intro w hw
        rw [frontier_ball 0 hR.ne'] at hw
        exact hgBoundary w hw
      have hg0pos : 0 < ‖g 0‖ := norm_pos_iff.mpr (D.ne_zero 0 (by simp [hR.le]))
      have := Real.strictMonoOn_log.monotoneOn hg0pos (lt_of_lt_of_le zero_lt_one hM)
        hg0leM
      linarith
    have hfrac : 2 * (Real.log M - Real.log ‖g 0‖ + 1) / (R - 1) ≤
        2 * (Real.log M - Real.log ‖g 0‖ + 1) := by
      apply (div_le_iff₀ (by linarith : 0 < R - 1)).2
      nlinarith
    norm_num at hglower
    linarith [hlogg0, hfrac]
  have horderz : meromorphicOrderAt p z = 0 :=
    (hpR z (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hpz
  have heq := D.log_norm_eq (w := z)
    (by rw [Metric.mem_closedBall, dist_zero_right]; linarith) horderz hR
  rw [hdivSphere] at heq
  have hbzero : (∑ᶠ i : ℂ, ((0 : Function.locallyFinsuppWithin
      (Metric.sphere (0 : ℂ) R) ℤ) i : ℝ) * Real.log ‖z - i‖) = 0 := by simp
  rw [hbzero, sub_zero,
    (hpR z (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)).meromorphicTrailingCoeffAt_of_ne_zero hpz]
    at heq
  have hsum_eq : (∑ᶠ u, (MeromorphicOn.divisor p (Metric.ball 0 R) u : ℝ) *
      Real.log ‖Complex.canonicalFactor R u z‖) =
      ∑ u ∈ t, (MeromorphicOn.divisor p (Metric.ball 0 R) u : ℝ) *
        Real.log ‖Complex.canonicalFactor R u z‖ := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    have hdu : divR u ≠ 0 := by
      intro hzero
      simp [divR, hzero] at hu
    exact Finset.mem_coe.2 ((ht u).2 hdu)
  rw [hsum_eq] at heq
  have hsums :
      (∑ u ∈ t, (MeromorphicOn.divisor p (Metric.ball 0 R) u : ℝ) *
          Real.log (‖z - u‖ / 4)) ≤
        -(∑ u ∈ t, (MeromorphicOn.divisor p (Metric.ball 0 R) u : ℝ) *
          Real.log ‖Complex.canonicalFactor R u z‖) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro u hu
    have hdu : divR u ≠ 0 := (ht u).1 (by simpa using hu)
    have huball : u ∈ Metric.ball (0 : ℂ) R := divR.supportWithinDomain hdu
    have hzu : z ≠ u := by
      intro h
      subst u
      have horder : meromorphicOrderAt p z = 0 :=
        (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff
          (hpR z (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)).meromorphicNFAt).mpr hpz
      apply hdu
      rw [(hmR.mono_set Metric.ball_subset_closedBall).divisor_apply huball, horder]
      rfl
    have hcf := canonicalFactor_norm_le_four_div hR2 hR3 huball hz hzu
    have hdist : 0 < ‖z - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzu)
    have hlog : Real.log ‖Complex.canonicalFactor R u z‖ ≤
        Real.log (4 / ‖z - u‖) := by
      have hcfpos : 0 < ‖Complex.canonicalFactor R u z‖ :=
        norm_pos_iff.mpr (Complex.canonicalFactor_ne_zero huball
          (by rw [Metric.mem_closedBall, dist_zero_right]; linarith) hzu)
      have hfourdiv : 0 < 4 / ‖z - u‖ := div_pos (by norm_num) hdist
      exact Real.strictMonoOn_log.monotoneOn hcfpos hfourdiv hcf
    have hlogdiv : Real.log (‖z - u‖ / 4) = -Real.log (4 / ‖z - u‖) := by
      rw [Real.log_div hdist.ne' (by norm_num), Real.log_div (by norm_num) hdist.ne']
      ring
    rw [hlogdiv]
    have hmnonneg : 0 ≤ (divR u : ℝ) := by exact_mod_cast hdiv_nonneg u
    dsimp [divR] at hmnonneg ⊢
    nlinarith
  linarith [add_le_add hbase hsums]

/-- Jensen's inequality bounds the total multiplicity of the zeros extracted by
`exists_local_minimum_estimate`.  Choosing the extraction radius below `5/2`
makes the denominator uniform. -/
private lemma local_zero_count_le {p : ℂ → ℂ} {M R : ℝ} {t : Finset ℂ}
    (hp : AnalyticOnNhd ℂ p (Metric.closedBall 0 3)) (hp0 : p 0 ≠ 0)
    (hM : 1 ≤ M) (hpM : ∀ z ∈ Metric.sphere (0 : ℂ) 3, ‖p z‖ ≤ M)
    (hR2 : 2 < R) (hR25 : R < 5 / 2)
    (ht : ∀ u, u ∈ t ↔
      (MeromorphicOn.divisor p (Metric.ball (0 : ℂ) R)) u ≠ 0) :
    ∑ u ∈ t, ((MeromorphicOn.divisor p (Metric.ball (0 : ℂ) R)) u : ℝ) ≤
      Real.log (M / ‖p 0‖) / Real.log (6 / 5) := by
  classical
  have hR0 : 0 < R := by linarith
  have hR3 : R < 3 := hR25.trans (by norm_num)
  have hpR : AnalyticOnNhd ℂ p (Metric.closedBall (0 : ℂ) R) :=
    hp.mono (Metric.closedBall_subset_closedBall hR3.le)
  have hpBall : AnalyticOnNhd ℂ p (Metric.ball (0 : ℂ) R) :=
    hpR.mono Metric.ball_subset_closedBall
  let dBall := MeromorphicOn.divisor p (Metric.ball (0 : ℂ) R)
  let dClosed := MeromorphicOn.divisor p (Metric.closedBall (0 : ℂ) R)
  have hpoint : ∀ u : ℂ, (dBall u : ℝ) ≤ (dClosed u : ℝ) := by
    intro u
    by_cases hu : u ∈ Metric.ball (0 : ℂ) R
    · rw [show dBall u = ((analyticOrderAt p u).map (↑)).untop₀ by
        exact MeromorphicOn.AnalyticOnNhd.divisor_apply hpBall hu]
      rw [show dClosed u = ((analyticOrderAt p u).map (↑)).untop₀ by
        exact MeromorphicOn.AnalyticOnNhd.divisor_apply hpR (Metric.ball_subset_closedBall hu)]
    · have hdBall : dBall u = 0 := by
        exact (MeromorphicOn.divisor p (Metric.ball 0 R)).apply_eq_zero_of_notMem hu
      rw [hdBall, Int.cast_zero]
      exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hpR) u
  have hfiniteBall : (Function.support fun u : ℂ ↦ (dBall u : ℝ)).Finite := by
    apply (hpR.meromorphicOn.divisor_ball_support_finite).subset
    intro u hu
    have : dBall u ≠ 0 := by
      simpa only [Function.mem_support, ne_eq, Int.cast_eq_zero, not_false_eq_true] using hu
    simpa only [Function.mem_support, ne_eq] using this
  have hfiniteClosed : (Function.support fun u : ℂ ↦ (dClosed u : ℝ)).Finite := by
    apply ((MeromorphicOn.divisor p (Metric.closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall (0 : ℂ) R)).subset
    intro u hu
    have : dClosed u ≠ 0 := by
      simpa only [Function.mem_support, ne_eq, Int.cast_eq_zero, not_false_eq_true] using hu
    simpa only [Function.mem_support, ne_eq] using this
  have hsumle : (∑ᶠ u : ℂ, (dBall u : ℝ)) ≤ ∑ᶠ u : ℂ, (dClosed u : ℝ) :=
    finsum_le_finsum' hfiniteBall hfiniteClosed hpoint
  have hsumt : (∑ u ∈ t, (dBall u : ℝ)) = ∑ᶠ u : ℂ, (dBall u : ℝ) := by
    symm
    apply finsum_eq_sum_of_support_subset
    intro u hu
    apply Finset.mem_coe.2
    apply (ht u).2
    have hcast : (dBall u : ℝ) ≠ 0 := by simpa only [Function.mem_support] using hu
    exact_mod_cast hcast
  have hpabs : AnalyticOnNhd ℂ p (Metric.closedBall (0 : ℂ) |(3 : ℝ)|) := by
    norm_num
    exact hp
  have hpMabs : ∀ z ∈ Metric.sphere (0 : ℂ) |(3 : ℝ)|, ‖p z‖ ≤ M := by
    simpa [Metric.mem_sphere] using hpM
  have hjensen := AnalyticOnNhd.sum_divisor_le (f := p) (c := (0 : ℂ))
    (r := R) (R := (3 : ℝ)) (M := M) (by simpa [abs_of_pos hR0] using hR0)
    (by simp only [abs_of_pos hR0, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; exact hR3)
    hM hpabs hp0 hpMabs
  have hjensen' : (∑ᶠ u : ℂ, (dClosed u : ℝ)) ≤
      Real.log (M / ‖p 0‖) / Real.log (3 / R) := by
    have hfinite : (Function.support dClosed).Finite :=
      (MeromorphicOn.divisor p (Metric.closedBall (0 : ℂ) R)).finiteSupport
        (isCompact_closedBall (0 : ℂ) R)
    have hmap := map_finsum (Int.castRingHom ℝ) hfinite
    rw [abs_of_pos hR0] at hjensen
    change ((↑(∑ᶠ u : ℂ, dClosed u) : ℝ) ≤
      Real.log (M / ‖p 0‖) / Real.log (3 / R)) at hjensen
    change (∑ᶠ u : ℂ, (Int.castRingHom ℝ) (dClosed u)) ≤
      Real.log (M / ‖p 0‖) / Real.log (3 / R)
    rw [← hmap]
    exact hjensen
  have hlog65 : 0 < Real.log (6 / 5) := Real.log_pos (by norm_num)
  have hratio : 6 / 5 < 3 / R := by
    apply (lt_div_iff₀ hR0).2
    nlinarith
  have hthreeR : 0 < 3 / R := div_pos (by norm_num) hR0
  have hlogratio : Real.log (6 / 5) ≤ Real.log (3 / R) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hthreeR hratio.le
  have hlogratioPos : 0 < Real.log (3 / R) := hlog65.trans_le hlogratio
  have hsumClosedNonneg : 0 ≤ ∑ᶠ u : ℂ, (dClosed u : ℝ) :=
    finsum_nonneg fun u ↦ by exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hpR) u
  have hnum : 0 ≤ Real.log (M / ‖p 0‖) := by
    have hquot : 0 ≤ Real.log (M / ‖p 0‖) / Real.log (3 / R) :=
      hsumClosedNonneg.trans hjensen'
    by_contra hnegative
    have hnumneg : Real.log (M / ‖p 0‖) < 0 := lt_of_not_ge hnegative
    have := div_neg_of_neg_of_pos hnumneg hlogratioPos
    linarith
  rw [hsumt]
  exact hsumle.trans (hjensen'.trans
    (div_le_div_of_nonneg_left hnum hlog65 hlogratio))

/-- Apply the local disk estimate to a finite family of affine rescalings and
select one horizontal shift that works for every disk. -/
private lemma exists_common_scaled_disk_shift {κ : Type*} [Fintype κ]
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (center : κ → ℂ)
    {d M C β : ℝ} (hd : 0 < d) (hM : 1 ≤ M) (hC : 0 < C) (hβ : 0 ≤ β)
    (hboundary : ∀ q : κ, ∀ z : ℂ, ‖z‖ = 3 → ‖F (center q + d * z)‖ ≤ M)
    (hcenter : ∀ q : κ, C ≤ Real.log ‖F (center q)‖)
    (hcard : 16 * (Fintype.card κ : ℝ) < Real.exp (β / 2)) :
    ∃ α : ℝ, -(1 / 2 : ℝ) < α ∧ α ≤ 1 / 2 ∧
      ∀ q : κ, ∀ v : ℝ, ‖(α : ℂ) + (v : ℂ) * Complex.I‖ ≤ 1 →
        C - 2 * (Real.log M - C + 1) -
            β * ((Real.log M - C) / Real.log (6 / 5)) ≤
          Real.log ‖F (center q + d * ((α : ℂ) + (v : ℂ) * Complex.I))‖ := by
  classical
  let p : κ → ℂ → ℂ := fun q z => F (center q + d * z)
  have hpAnalytic : ∀ q : κ, AnalyticOnNhd ℂ (p q) (Metric.closedBall 0 3) := by
    intro q
    have hpdiff : Differentiable ℂ (p q) := by
      dsimp [p]
      fun_prop
    exact (hpdiff.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hp0 : ∀ q : κ, p q 0 ≠ 0 := by
    intro q hzero
    have hcq : C ≤ Real.log ‖p q 0‖ := by
      simpa [p] using hcenter q
    rw [hzero] at hcq
    simp only [norm_zero, Real.log_zero] at hcq
    linarith
  have hpBoundary : ∀ q : κ, ∀ z ∈ Metric.sphere (0 : ℂ) 3, ‖p q z‖ ≤ M := by
    intro q z hz
    apply hboundary q z
    simpa [Metric.mem_sphere] using hz
  have hextract : ∀ q : κ, ∃ (R : ℝ) (t : Finset ℂ),
      2 < R ∧ R < 5 / 2 ∧
      (∀ u, u ∈ t ↔
        (MeromorphicOn.divisor (p q) (Metric.ball (0 : ℂ) R)) u ≠ 0) ∧
      (∀ u, 0 ≤ (MeromorphicOn.divisor (p q) (Metric.ball (0 : ℂ) R)) u) ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → p q z ≠ 0 →
        Real.log ‖p q 0‖ - 2 * (Real.log M - Real.log ‖p q 0‖ + 1) +
            ∑ u ∈ t,
              ((MeromorphicOn.divisor (p q) (Metric.ball 0 R)) u : ℝ) *
                Real.log (‖z - u‖ / 4) ≤ Real.log ‖p q z‖ := by
    intro q
    exact exists_local_minimum_estimate (hpAnalytic q) (hp0 q) hM (hpBoundary q)
  choose R roots hR2 hR25 hroots hdivNonneg hlocal using hextract
  let mult : κ → ℂ → ℝ := fun q u =>
    (MeromorphicOn.divisor (p q) (Metric.ball (0 : ℂ) (R q)) u : ℝ)
  let W : κ → ℝ := fun q => ∑ u ∈ roots q, mult q u
  have hmult : ∀ q : κ, ∀ u ∈ roots q, 0 ≤ mult q u := by
    intro q u hu
    dsimp [mult]
    exact_mod_cast hdivNonneg q u
  have hWnonneg : ∀ q : κ, 0 ≤ W q := by
    intro q
    exact Finset.sum_nonneg (hmult q)
  let J : Finset κ := Finset.univ.filter fun q => 0 < W q
  have hreal : ∀ q ∈ J, ∀ u ∈ roots q, |u.re| < 5 / 2 := by
    intro q hq u hu
    have hdu : (MeromorphicOn.divisor (p q) (Metric.ball (0 : ℂ) (R q))) u ≠ 0 :=
      (hroots q u).1 hu
    have huball := (MeromorphicOn.divisor (p q) (Metric.ball (0 : ℂ) (R q))).supportWithinDomain hdu
    have hunorm : ‖u‖ < R q := by simpa [Metric.mem_ball] using huball
    exact (Complex.abs_re_le_norm u).trans_lt (hunorm.trans (hR25 q))
  have hmultJ : ∀ q ∈ J, ∀ u ∈ roots q, 0 ≤ mult q u :=
    fun q hq => hmult q
  have hWpos : ∀ q ∈ J, 0 < ∑ u ∈ roots q, mult q u := by
    intro q hq
    exact (Finset.mem_filter.1 hq).2
  have hJcard : J.card ≤ Fintype.card κ := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq Finset.card_univ
  have hcardJ : 16 * (J.card : ℝ) < Real.exp (β / 2) := by
    have hcast : (J.card : ℝ) ≤ Fintype.card κ := by exact_mod_cast hJcard
    exact (mul_le_mul_of_nonneg_left hcast (by norm_num)).trans_lt hcard
  obtain ⟨α, hαleft, hαright, havoid, hshift⟩ :=
    Erdos516CommonShift.exists_simultaneous_log_shift J roots
      (fun q u => u.re) mult hreal hmultJ hWpos hcardJ
  refine ⟨α, hαleft, hαright, ?_⟩
  intro q v hz
  let z : ℂ := (α : ℂ) + (v : ℂ) * Complex.I
  have hz' : ‖z‖ ≤ 1 := by simpa [z] using hz
  have hsumLower : -β * W q ≤
      ∑ u ∈ roots q, mult q u * Real.log (‖z - u‖ / 4) := by
    by_cases hqJ : q ∈ J
    · have hs := hshift q hqJ
      calc
        -β * W q ≤
            ∑ u ∈ roots q, mult q u * Real.log (|α - u.re| / 4) := by
          simpa [W] using hs
        _ ≤ ∑ u ∈ roots q, mult q u * Real.log (‖z - u‖ / 4) := by
          apply Finset.sum_le_sum
          intro u hu
          have hmu := hmult q u hu
          have hdist : |α - u.re| ≤ ‖z - u‖ := by
            calc
              |α - u.re| = |(z - u).re| := by simp [z]
              _ ≤ ‖z - u‖ := Complex.abs_re_le_norm _
          by_cases hre : α = u.re
          · have hmuNe : mult q u ≠ 0 := by
              intro hm0
              apply (hroots q u).1 hu
              have hm0' :
                  ((MeromorphicOn.divisor (p q) (Metric.ball 0 (R q))) u : ℝ) = 0 := by
                simpa [mult] using hm0
              exact_mod_cast hm0'
            exact (havoid q hqJ u hu (lt_of_le_of_ne hmu (Ne.symm hmuNe)) hre).elim
          · have hleftPos : 0 < |α - u.re| := abs_pos.mpr (sub_ne_zero.mpr hre)
            have hrightPos : 0 < ‖z - u‖ := hleftPos.trans_le hdist
            have hlog := Real.strictMonoOn_log.monotoneOn
              (div_pos hleftPos (by norm_num : (0 : ℝ) < 4))
              (div_pos hrightPos (by norm_num : (0 : ℝ) < 4))
              (div_le_div_of_nonneg_right hdist (by norm_num : (0 : ℝ) ≤ 4))
            exact mul_le_mul_of_nonneg_left hlog hmu
    · have hWzero : W q = 0 := by
        have := Finset.mem_filter.not.1 hqJ
        simp only [Finset.mem_univ, true_and] at this
        exact le_antisymm (le_of_not_gt this) (hWnonneg q)
      have hallZero : ∀ u ∈ roots q, mult q u = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (hmult q)).1 (by simpa [W] using hWzero)
      have hleftZero : -β * W q = 0 := by simp [hWzero]
      have hsumZero : (∑ u ∈ roots q,
          mult q u * Real.log (‖z - u‖ / 4)) = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        rw [hallZero u hu, zero_mul]
      rw [hleftZero, hsumZero]
  have hpz : p q z ≠ 0 := by
    intro hpzero
    have hzR : z ∈ Metric.ball (0 : ℂ) (R q) := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith [hR2 q]
    have hpBall : AnalyticOnNhd ℂ (p q) (Metric.ball (0 : ℂ) (R q)) :=
      (hpAnalytic q).mono fun w hw => by
        rw [Metric.mem_closedBall, dist_zero_right]
        have hwR : ‖w‖ < R q := by simpa [Metric.mem_ball] using hw
        linarith [hR25 q]
    have hzeroBall : (0 : ℂ) ∈ Metric.ball 0 (R q) := by
      simp only [Metric.mem_ball, dist_self]
      linarith [hR2 q]
    have hfiniteAll : ∀ u : Metric.ball (0 : ℂ) (R q),
        meromorphicOrderAt (p q) u ≠ ⊤ := by
      rw [← hpBall.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
        (Metric.isConnected_ball (by linarith [hR2 q]))]
      refine ⟨⟨0, hzeroBall⟩, ?_⟩
      have horderZero : meromorphicOrderAt (p q) 0 = 0 :=
        (hpBall 0 hzeroBall).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 (hp0 q)
      rw [horderZero]
      exact WithTop.zero_ne_top
    have hdivNe : (MeromorphicOn.divisor (p q) (Metric.ball (0 : ℂ) (R q))) z ≠ 0 := by
      have hsupp : z ∈ Function.support
          (MeromorphicOn.divisor (p q) (Metric.ball (0 : ℂ) (R q))) := by
        rw [← hpBall.meromorphicNFOn.zero_set_eq_divisor_support hfiniteAll]
        exact ⟨hzR, hpzero⟩
      simpa only [Function.mem_support] using hsupp
    have hzroot : z ∈ roots q := (hroots q z).2 hdivNe
    by_cases hqJ : q ∈ J
    · have hmz : 0 < mult q z := lt_of_le_of_ne (hmult q z hzroot)
          (Ne.symm fun hm0 => hdivNe (by
            have hm0' :
                ((MeromorphicOn.divisor (p q) (Metric.ball 0 (R q))) z : ℝ) = 0 := by
              simpa [mult] using hm0
            exact_mod_cast hm0'))
      exact havoid q hqJ z hzroot hmz (by simp [z])
    · have hWzero : W q = 0 := by
        have := Finset.mem_filter.not.1 hqJ
        simp only [Finset.mem_univ, true_and] at this
        exact le_antisymm (le_of_not_gt this) (hWnonneg q)
      have hallZero := (Finset.sum_eq_zero_iff_of_nonneg (hmult q)).1
        (by simpa [W] using hWzero)
      have hmz := hallZero z hzroot
      apply hdivNe
      have hmz' :
          ((MeromorphicOn.divisor (p q) (Metric.ball 0 (R q))) z : ℝ) = 0 := by
        simpa [mult] using hmz
      exact_mod_cast hmz'
  have hloc := hlocal q z hz' hpz
  have hcount := local_zero_count_le (hpAnalytic q) (hp0 q) hM (hpBoundary q)
    (hR2 q) (hR25 q) (hroots q)
  have hcenterq : C ≤ Real.log ‖p q 0‖ := by
    simpa [p] using hcenter q
  have hlogMcenter : 0 ≤ Real.log M - C := by
    have hnormCenter : ‖p q 0‖ ≤ M := by
      refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
        ⟨(hpAnalytic q).differentiableOn.mono Metric.ball_subset_closedBall,
          by rw [closure_ball 0 (by norm_num : (3 : ℝ) ≠ 0)]
             exact (hpAnalytic q).continuousOn⟩ ?_ ?_
      · intro w hw
        rw [frontier_ball 0 (by norm_num : (3 : ℝ) ≠ 0)] at hw
        exact hpBoundary q w hw
      · rw [closure_ball 0 (by norm_num : (3 : ℝ) ≠ 0)]
        simp
    have hp0pos : 0 < ‖p q 0‖ := norm_pos_iff.mpr (hp0 q)
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have := Real.strictMonoOn_log.monotoneOn hp0pos hMpos hnormCenter
    linarith
  have hWbound : W q ≤ (Real.log M - C) / Real.log (6 / 5) := by
    calc
      W q ≤ Real.log (M / ‖p q 0‖) / Real.log (6 / 5) := by
        simpa [W, mult] using hcount
      _ = (Real.log M - Real.log ‖p q 0‖) / Real.log (6 / 5) := by
        rw [Real.log_div (ne_of_gt (lt_of_lt_of_le zero_lt_one hM))
          (norm_ne_zero_iff.mpr (hp0 q))]
      _ ≤ (Real.log M - C) / Real.log (6 / 5) := by
        exact div_le_div_of_nonneg_right (sub_le_sub_left hcenterq _)
          (Real.log_nonneg (by norm_num))
  have hβW : -β * ((Real.log M - C) / Real.log (6 / 5)) ≤ -β * W q := by
    nlinarith
  dsimp [mult, p, z] at hloc hsumLower ⊢
  nlinarith [hloc, hsumLower, hcenterq, hβW]

/-- The removable singularity of `x * log x` is uniformly bounded on the
interval needed for logarithmic averaging. -/
private lemma abs_mul_log_le_six {x : ℝ} (hx : |x| ≤ 3) :
    |x * Real.log x| ≤ 6 := by
  let q := |x|
  have hq0 : 0 ≤ q := abs_nonneg x
  have hq3 : q ≤ 3 := hx
  have hlower : -1 ≤ q * Real.log q := by
    have h := Real.self_sub_one_le_mul_log hq0
    linarith
  have hupper : q * Real.log q ≤ 6 := by
    by_cases hq1 : q ≤ 1
    · exact (Real.mul_log_nonpos hq0 hq1).trans (by norm_num)
    · have h1q : 1 ≤ q := le_of_not_ge hq1
      have hlog0 : 0 ≤ Real.log q := Real.log_nonneg h1q
      have hlog2 : Real.log q ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one h1q)
        linarith
      calc
        q * Real.log q ≤ 3 * 2 := mul_le_mul hq3 hlog2 hlog0 (by norm_num)
        _ = 6 := by norm_num
  have habsq : |q * Real.log q| ≤ 6 := abs_le.2 ⟨by linarith, hupper⟩
  rw [← Real.log_abs x, abs_mul]
  simpa [q, abs_mul, abs_of_nonneg hq0] using habsq

/-- A translated logarithmic singularity has a uniformly bounded-below
integral on the unit interval.  Only the coarse constant is relevant: its
independence of the position of the singularity is what makes the eventual
zero-avoidance loss linear in the zero count. -/
private lemma integral_log_abs_sub_lower {x : ℝ} (hx : |x| < 5 / 2) :
    -(13 : ℝ) ≤ ∫ α in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.log |α - x| := by
  let a : ℝ := -(1 / 2) - x
  let b : ℝ := 1 / 2 - x
  have ha : |a| ≤ 3 := by
    dsimp [a]
    apply le_of_lt
    calc
      |-(1 / 2 : ℝ) - x| ≤ |-(1 / 2 : ℝ)| + |x| := abs_sub _ _
      _ < 3 := by norm_num at hx ⊢; linarith
  have hb : |b| ≤ 3 := by
    dsimp [b]
    apply le_of_lt
    calc
      |(1 / 2 : ℝ) - x| ≤ |(1 / 2 : ℝ)| + |x| := abs_sub _ _
      _ < 3 := by norm_num at hx ⊢; linarith
  have hab : b - a = 1 := by dsimp [a, b]; ring
  have haBound := abs_mul_log_le_six ha
  have hbBound := abs_mul_log_le_six hb
  have heq : (∫ α in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.log |α - x|) =
      b * Real.log b - a * Real.log a - b + a := by
    calc
      (∫ α in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.log |α - x|) =
          ∫ α in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), Real.log (α - x) := by
            apply intervalIntegral.integral_congr
            intro α hα
            exact Real.log_abs (α - x)
      _ = ∫ y in a..b, Real.log y := by
        simpa [a, b] using
          (intervalIntegral.integral_comp_sub_right (fun y : ℝ ↦ Real.log y) x
            (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ)))
      _ = b * Real.log b - a * Real.log a - b + a := by
        exact integral_log
  rw [heq]
  have haLower : -6 ≤ a * Real.log a := (abs_le.1 haBound).1
  have haUpper : a * Real.log a ≤ 6 := (abs_le.1 haBound).2
  have hbLower : -6 ≤ b * Real.log b := (abs_le.1 hbBound).1
  linarith

/-- Logarithmic averaging for a finite weighted family of real points.  The
selected point lies in the unit interval, avoids every point with positive
weight, and loses at most a fixed constant times total weight. -/
private lemma exists_common_log_shift { ι : Type* } [DecidableEq ι]
    (s : Finset ι) (x m : ι → ℝ)
    (hx : ∀ i ∈ s, |x i| < 5 / 2) (hm : ∀ i ∈ s, 0 ≤ m i) :
    ∃ α : ℝ, -(1 / 2 : ℝ) < α ∧ α ≤ 1 / 2 ∧
      (∀ i ∈ s, 0 < m i → α ≠ x i) ∧
      -(20 : ℝ) * ∑ i ∈ s, m i ≤
        ∑ i ∈ s, m i * Real.log (|α - x i| / 4) := by
  classical
  have hsumNonneg : 0 ≤ ∑ i ∈ s, m i := Finset.sum_nonneg fun i hi ↦ hm i hi
  by_cases hsumZero : ∑ i ∈ s, m i = 0
  · have hallZero : ∀ i ∈ s, m i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hm).1 hsumZero
    refine ⟨0, by norm_num, by norm_num, ?_, ?_⟩
    · intro i hi hpos
      rw [hallZero i hi] at hpos
      exact (lt_irrefl 0 hpos).elim
    · rw [hsumZero, mul_zero]
      have hrhs : (∑ i ∈ s, m i * Real.log (|(0 : ℝ) - x i| / 4)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hallZero i hi, zero_mul]
      rw [hrhs]
  let left : ℝ := -(1 / 2)
  let right : ℝ := 1 / 2
  let G : ℝ → ℝ := fun α ↦ ∑ i ∈ s, m i * Real.log |α - x i|
  have hleftRight : left ≤ right := by dsimp [left, right]; norm_num
  have hlogInt : ∀ i ∈ s,
      IntervalIntegrable (fun α : ℝ ↦ Real.log |α - x i|) volume left right := by
    intro i hi
    have h := (intervalIntegral.intervalIntegrable_log'
      (a := left - x i) (b := right - x i)).comp_sub_right (x i)
    have h' : IntervalIntegrable (fun α : ℝ ↦ Real.log (α - x i)) volume left right := by
      simpa [left, right] using h
    exact h'.congr (fun α hα ↦ (Real.log_abs (α - x i)).symm)
  have hGinterval : IntervalIntegrable G volume left right := by
    have h := IntervalIntegrable.sum s fun i hi ↦ (hlogInt i hi).const_mul (m i)
    refine h.congr ?_
    intro α hα
    simp [G]
  let μ : Measure ℝ := volume.restrict (Set.Ioc left right)
  let : MeasureTheory.IsProbabilityMeasure μ :=
    ⟨by simp [μ, left, right]; norm_num⟩
  have hGint : Integrable G μ := by
    change IntegrableOn G (Set.Ioc left right) volume
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hleftRight).1 hGinterval
  let roots : Finset ℝ := s.filter (fun i ↦ 0 < m i) |>.image x
  let bad : Set ℝ := (Set.Ioc left right)ᶜ ∪ (roots : Set ℝ)
  have hbad : μ bad = 0 := by
    rw [Measure.restrict_apply (measurableSet_Ioc.compl.union roots.measurableSet)]
    have hdisjoint : bad ∩ Set.Ioc left right = (roots : Set ℝ) ∩ Set.Ioc left right := by
      ext z
      constructor
      · rintro ⟨hzbad, hzint⟩
        rcases hzbad with hzoutside | hzroot
        · exact (hzoutside hzint).elim
        · exact ⟨hzroot, hzint⟩
      · rintro ⟨hzroot, hzint⟩
        exact ⟨Or.inr hzroot, hzint⟩
    rw [hdisjoint]
    exact (roots.finite_toSet.inter_of_left (Set.Ioc left right)).measure_zero volume
  have hsumPos : 0 < ∑ i ∈ s, m i := lt_of_le_of_ne hsumNonneg (Ne.symm hsumZero)
  have hexists : ∃ α : ℝ, α ∉ bad ∧
      (∫ β, G β ∂μ) - ∑ i ∈ s, m i ≤ G α := by
    by_contra h
    push Not at h
    have haeGood : ∀ᵐ α : ℝ ∂μ, α ∉ bad := by
      apply (ae_iff).2
      have hset : {α : ℝ | ¬ α ∉ bad} = bad := by ext α; simp
      rw [hset]
      exact hbad
    have haeBound : G ≤ᵐ[μ] fun _ ↦ (∫ β, G β ∂μ) - ∑ i ∈ s, m i :=
      haeGood.mono fun α hα ↦ (h α hα).le
    have hle := integral_mono_ae hGint
      (integrable_const ((∫ β, G β ∂μ) - ∑ i ∈ s, m i)) haeBound
    have hmuReal : μ.real Set.univ = 1 := by simp
    rw [integral_const, hmuReal, one_smul] at hle
    linarith
  obtain ⟨α, hαbad, hαavg⟩ := hexists
  have hαinterval : α ∈ Set.Ioc left right := by
    by_contra h
    exact hαbad (by simp [bad, h])
  have hαroots : α ∉ (roots : Set ℝ) := by
    intro h
    exact hαbad (by simp [bad, h])
  have hIntegralEq : (∫ β, G β ∂μ) = ∫ β in left..right, G β := by
    rw [intervalIntegral.integral_of_le hleftRight]
  have hsumIntegral : (∫ β in left..right, G β) =
      ∑ i ∈ s, m i * (∫ β in left..right, Real.log |β - x i|) := by
    dsimp [G]
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [intervalIntegral.integral_const_mul]
    · intro i hi
      exact (hlogInt i hi).const_mul (m i)
  have hIntegralLower : -(13 : ℝ) * ∑ i ∈ s, m i ≤ ∫ β, G β ∂μ := by
    rw [hIntegralEq, hsumIntegral]
    calc
      -(13 : ℝ) * ∑ i ∈ s, m i =
          ∑ i ∈ s, m i * (-(13 : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ ≤ ∑ i ∈ s, m i * (∫ β in left..right, Real.log |β - x i|) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (by simpa [left, right] using integral_log_abs_sub_lower (hx i hi)) (hm i hi)
  refine ⟨α, ?_, ?_, ?_, ?_⟩
  · simpa [left] using hαinterval.1
  · simpa [right] using hαinterval.2
  · intro i hi hmi hEq
    apply hαroots
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hmi⟩, hEq.symm⟩
  have hGalpha : -(14 : ℝ) * ∑ i ∈ s, m i ≤ G α := by
    linarith [hIntegralLower, hαavg]
  have hlog4 : Real.log 4 ≤ 3 :=
    by convert Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num) using 1 <;> norm_num
  have hrewrite : (∑ i ∈ s, m i * Real.log (|α - x i| / 4)) =
      G α - Real.log 4 * ∑ i ∈ s, m i := by
    dsimp [G]
    calc
      (∑ i ∈ s, m i * Real.log (|α - x i| / 4)) =
          ∑ i ∈ s, (m i * Real.log |α - x i| - m i * Real.log 4) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hmi : m i = 0
        · simp [hmi]
        have hmipos : 0 < m i := lt_of_le_of_ne (hm i hi) (Ne.symm hmi)
        have hne : α ≠ x i := by
          intro h
          apply hαroots
          rw [Finset.mem_coe, Finset.mem_image]
          exact ⟨i, Finset.mem_filter.2 ⟨hi, hmipos⟩, h.symm⟩
        have habs : |α - x i| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
        rw [Real.log_div habs (by norm_num)]
        ring
      _ = (∑ i ∈ s, m i * Real.log |α - x i|) -
          ∑ i ∈ s, m i * Real.log 4 := by rw [Finset.sum_sub_distrib]
      _ = (∑ i ∈ s, m i * Real.log |α - x i|) -
          Real.log 4 * ∑ i ∈ s, m i := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [hrewrite]
  nlinarith

/-- A frequent-point form of the elementary Borel growth lemma.  If a real function has an
eventual affine upper bound, its increment over a fixed step cannot eventually exceed every
number larger than the affine slope times that step.  This is the selection principle needed
for a limsup conclusion; unlike the density-one version, it needs no measure theory. -/
private lemma frequently_increment_le_of_eventually_le_affine (u : ℝ → ℝ)
    {A B h c : ℝ} (hh : 0 < h) (hc : A * h < c)
    (hu : ∀ᶠ x : ℝ in atTop, u x ≤ A * x + B) :
    ∃ᶠ x : ℝ in atTop, u (x + h) ≤ u x + c := by
  by_contra hfreq
  rw [Filter.not_frequently] at hfreq
  obtain ⟨T, hT⟩ := (eventually_atTop.1 (hu.and hfreq))
  have hlower : ∀ q : ℕ, u T + (q : ℝ) * c ≤ u (T + (q : ℝ) * h) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        have hx : T ≤ T + (q : ℝ) * h := by
          have hq : 0 ≤ (q : ℝ) := by positivity
          nlinarith [mul_nonneg hq hh.le]
        have hstep : u (T + (q : ℝ) * h) + c <
            u ((T + (q : ℝ) * h) + h) := by
          exact lt_of_not_ge (hT _ hx).2
        calc
          u T + ((q + 1 : ℕ) : ℝ) * c =
              (u T + (q : ℝ) * c) + c := by push_cast; ring
          _ ≤ u (T + (q : ℝ) * h) + c := by linarith
          _ ≤ u ((T + (q : ℝ) * h) + h) := hstep.le
          _ = u (T + ((q + 1 : ℕ) : ℝ) * h) := by push_cast; congr 1 <;> ring
  have hgap : 0 < c - A * h := sub_pos.mpr hc
  obtain ⟨q : ℕ, hq⟩ := exists_nat_gt ((A * T + B - u T) / (c - A * h))
  have hx : T ≤ T + (q : ℝ) * h := by
    have hq0 : 0 ≤ (q : ℝ) := by positivity
    nlinarith [mul_nonneg hq0 hh.le]
  have hupper := (hT _ hx).1
  have hboth := (hlower q).trans hupper
  have hqR : (A * T + B - u T) / (c - A * h) < (q : ℝ) := hq
  rw [div_lt_iff₀ hgap] at hqR
  nlinarith

private lemma summable_inverse_square_exponents {n : ℕ → ℕ} (hn : StrictMono n) :
    Summable (fun k : ℕ ↦ 1 / (n (k + 1) : ℝ) ^ 2) := by
  have hbase : Summable (fun k : ℕ ↦ 1 / (k + 1 : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_) hbase
  have hk : k + 1 ≤ n (k + 1) := StrictMono.id_le hn (k + 1)
  gcongr
  exact_mod_cast hk

/-- The symmetric canonical product associated with the positive tail of the exponents. -/
private noncomputable def exponentCanonicalProduct (n : ℕ → ℕ) (ζ : ℂ) : ℂ :=
  ∏' k : ℕ, (1 - ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)

private lemma exponentCanonicalProduct_multipliable {n : ℕ → ℕ} (hn : StrictMono n) (ζ : ℂ) :
    Multipliable (fun k : ℕ ↦ 1 - ζ ^ 2 / (n (k + 1) : ℂ) ^ 2) := by
  have hs := summable_inverse_square_exponents hn
  have hsnorm : Summable
      (fun k : ℕ ↦ ‖-(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)‖) := by
    have hmul := hs.mul_left ‖ζ ^ 2‖
    refine hmul.congr fun k ↦ ?_
    simp [norm_pow, div_eq_mul_inv]
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hsnorm

private lemma exponentCanonicalProduct_hasProdLocallyUniformly {n : ℕ → ℕ}
    (hn : StrictMono n) : HasProdLocallyUniformlyOn
      (fun (k : ℕ) (ζ : ℂ) ↦ 1 - ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)
      (exponentCanonicalProduct n) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K hKuniv hK
  obtain ⟨B, hBpos, hB⟩ := hK.isBounded.exists_pos_norm_le
  let u : ℕ → ℝ := fun k ↦ B ^ 2 * (1 / (n (k + 1) : ℝ) ^ 2)
  have hu : Summable u := (summable_inverse_square_exponents hn).mul_left (B ^ 2)
  have hmajor : ∀ᶠ k : ℕ in atTop, ∀ ζ ∈ K,
      ‖-(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)‖ ≤ u k := by
    filter_upwards with k ζ hζ
    have hζB : ‖ζ‖ ≤ B := hB ζ hζ
    simp only [norm_neg, norm_div, norm_pow, _root_.norm_natCast, u, one_div]
    rw [div_eq_mul_inv]
    gcongr
  change HasProdUniformlyOn
    (fun (k : ℕ) (ζ : ℂ) ↦ 1 + -(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2))
    (fun ζ : ℂ ↦ ∏' k : ℕ, (1 + -(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2))) K
  exact hu.hasProdUniformlyOn_nat_one_add hK hmajor (fun k ↦ by fun_prop)

private lemma exponentCanonicalProduct_differentiable {n : ℕ → ℕ} (hn : StrictMono n) :
    Differentiable ℂ (exponentCanonicalProduct n) := by
  have hprod := (exponentCanonicalProduct_hasProdLocallyUniformly hn)
    |>.tendstoLocallyUniformlyOn_finsetRange
  have hdiff : ∀ N, DifferentiableOn ℂ (fun ζ : ℂ ↦
      ∏ k ∈ Finset.range N, (1 - ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)) Set.univ := by
    intro N
    fun_prop
  rw [← differentiableOn_univ]
  exact hprod.differentiableOn (Filter.Eventually.of_forall hdiff) isOpen_univ

/-- Every positive exponent is a zero of the symmetric canonical product. -/
private lemma exponentCanonicalProduct_at_exponent {n : ℕ → ℕ} (hn : StrictMono n) (j : ℕ) :
    exponentCanonicalProduct n (n (j + 1) : ℂ) = 0 := by
  rw [exponentCanonicalProduct]
  apply tprod_of_exists_eq_zero
  refine ⟨j, ?_⟩
  have hnpos : n (j + 1) ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ j) (StrictMono.id_le hn (j + 1)))
  field_simp
  exact sub_self 1

/-- The canonical product with the factor indexed by `j` removed.  Keeping the missing
factor equal to one makes it convenient to compare with the original `tprod`. -/
private noncomputable def exponentCanonicalProductAway (n : ℕ → ℕ) (j : ℕ) (ζ : ℂ) : ℂ :=
  ∏' k : ℕ, (1 + if k = j then 0 else -(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2))

private lemma exponentCanonicalProductAway_multipliable {n : ℕ → ℕ} (hn : StrictMono n)
    (j : ℕ) (ζ : ℂ) :
    Multipliable (fun k : ℕ ↦ 1 + if k = j then 0 else
      -(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)) := by
  have hs := summable_inverse_square_exponents hn
  have hbase : Summable
      (fun k : ℕ ↦ ‖-(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)‖) := by
    have hmul := hs.mul_left ‖ζ ^ 2‖
    refine hmul.congr fun k ↦ ?_
    simp [norm_pow, div_eq_mul_inv]
  have hsnorm : Summable (fun k : ℕ ↦
      ‖if k = j then (0 : ℂ) else -(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun k ↦ ‖-(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)‖)
      (g := fun k ↦ ‖if k = j then (0 : ℂ) else
        -(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)‖)
      (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hbase
    · split_ifs
      · simpa only [norm_zero] using
          (norm_nonneg (-(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)))
      · exact le_rfl
  exact multipliable_one_add_of_summable hsnorm

private lemma exponentCanonicalProduct_eq_factor_mul_away {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) (ζ : ℂ) :
    exponentCanonicalProduct n ζ =
      (1 - ζ ^ 2 / (n (j + 1) : ℂ) ^ 2) * exponentCanonicalProductAway n j ζ := by
  classical
  rw [exponentCanonicalProduct]
  have hawayUpdate : Multipliable (Function.update
      (fun k : ℕ ↦ 1 - ζ ^ 2 / (n (k + 1) : ℂ) ^ 2) j 1) := by
    convert exponentCanonicalProductAway_multipliable hn j ζ using 1
    funext k
    by_cases hkj : k = j <;> simp [Function.update, hkj] <;> ring
  calc
    ∏' k : ℕ, (1 - ζ ^ 2 / (n (k + 1) : ℂ) ^ 2) =
        (1 - ζ ^ 2 / (n (j + 1) : ℂ) ^ 2) *
          ∏' k : ℕ, if k = j then 1 else
            (1 - ζ ^ 2 / (n (k + 1) : ℂ) ^ 2) :=
      Multipliable.tprod_eq_mul_tprod_ite' j hawayUpdate
    _ = (1 - ζ ^ 2 / (n (j + 1) : ℂ) ^ 2) *
        exponentCanonicalProductAway n j ζ := by
      congr 1
      rw [exponentCanonicalProductAway]
      apply tprod_congr
      intro k
      by_cases hkj : k = j <;> simp [hkj] <;> ring

private lemma exponentCanonicalProductAway_hasProdLocallyUniformly {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) : HasProdLocallyUniformlyOn
      (fun (k : ℕ) (ζ : ℂ) ↦ 1 + if k = j then 0 else
        -(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2))
      (exponentCanonicalProductAway n j) Set.univ := by
  unfold exponentCanonicalProductAway
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K hKuniv hK
  obtain ⟨B, hBpos, hB⟩ := hK.isBounded.exists_pos_norm_le
  let u : ℕ → ℝ := fun k ↦ B ^ 2 * (1 / (n (k + 1) : ℝ) ^ 2)
  have hu : Summable u := (summable_inverse_square_exponents hn).mul_left (B ^ 2)
  have hmajor : ∀ᶠ k : ℕ in atTop, ∀ ζ ∈ K,
      ‖if k = j then (0 : ℂ) else -(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2)‖ ≤ u k := by
    filter_upwards with k ζ hζ
    split_ifs
    · simp only [norm_zero]
      positivity
    · have hζB : ‖ζ‖ ≤ B := hB ζ hζ
      simp only [norm_neg, norm_div, norm_pow, _root_.norm_natCast, u, one_div]
      rw [div_eq_mul_inv]
      gcongr
  exact hu.hasProdUniformlyOn_nat_one_add hK hmajor (fun k ↦ by
    by_cases hkj : k = j
    · simp [hkj]
      fun_prop
    · simp [hkj]
      fun_prop)

private lemma exponentCanonicalProductAway_differentiable {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) : Differentiable ℂ (exponentCanonicalProductAway n j) := by
  have hprod := (exponentCanonicalProductAway_hasProdLocallyUniformly hn j)
    |>.tendstoLocallyUniformlyOn_finsetRange
  have hdiff : ∀ N, DifferentiableOn ℂ (fun ζ : ℂ ↦
      ∏ k ∈ Finset.range N, (1 + if k = j then 0 else
        -(ζ ^ 2 / (n (k + 1) : ℂ) ^ 2))) Set.univ := by
    intro N
    apply DifferentiableOn.fun_finsetProd
    intro k hk
    by_cases hkj : k = j
    · simp [hkj]
    · simp only [hkj, ↓reduceIte, differentiableOn_const_add_iff]
      fun_prop
  rw [← differentiableOn_univ]
  exact hprod.differentiableOn (Filter.Eventually.of_forall hdiff) isOpen_univ

/-- Derivative of the canonical product at one of its positive zeros.  This is the
starting identity for the separated-zero condensation estimate. -/
private lemma deriv_exponentCanonicalProduct_at_exponent {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) :
    deriv (exponentCanonicalProduct n) (n (j + 1) : ℂ) =
      (-2 / (n (j + 1) : ℂ)) *
        exponentCanonicalProductAway n j (n (j + 1) : ℂ) := by
  let m : ℂ := n (j + 1)
  have hm : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ j)
      (StrictMono.id_le hn (j + 1)))
  have hfactor : Differentiable ℂ (fun ζ : ℂ ↦ 1 - ζ ^ 2 / m ^ 2) := by fun_prop
  have haway := exponentCanonicalProductAway_differentiable hn j
  rw [show exponentCanonicalProduct n = fun ζ ↦
      (1 - ζ ^ 2 / m ^ 2) * exponentCanonicalProductAway n j ζ by
    funext ζ
    exact exponentCanonicalProduct_eq_factor_mul_away hn j ζ]
  change deriv ((fun ζ : ℂ ↦ 1 - ζ ^ 2 / m ^ 2) *
      exponentCanonicalProductAway n j) m =
    (-2 / m) * exponentCanonicalProductAway n j m
  rw [deriv_mul (hfactor _) (haway _)]
  have hz : 1 - m ^ 2 / m ^ 2 = 0 := by
    field_simp
    ring
  have hderiv : deriv (fun ζ : ℂ ↦ 1 - ζ ^ 2 / m ^ 2) m = -2 / m := by
    calc
      deriv (fun ζ : ℂ ↦ 1 - ζ ^ 2 / m ^ 2) m =
          0 - (2 * m) / m ^ 2 := by
        simpa using ((hasDerivAt_const (x := m) (c := (1 : ℂ))).sub
          ((hasDerivAt_pow 2 m).div_const (m ^ 2))).deriv
      _ = -2 / m := by
        field_simp
        ring
  rw [hderiv, hz, zero_mul, add_zero]

/-- Removing the vanishing factor leaves a nonzero product.  The only possible zero of
another factor would force two entries of the strictly increasing exponent sequence to
coincide. -/
private lemma exponentCanonicalProductAway_at_exponent_ne_zero {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) :
    exponentCanonicalProductAway n j (n (j + 1) : ℂ) ≠ 0 := by
  unfold exponentCanonicalProductAway
  apply tprod_one_add_ne_zero_of_summable
  · intro k
    by_cases hkj : k = j
    · simp [hkj]
    · simp only [hkj, if_false]
      rw [← sub_eq_add_neg]
      apply sub_ne_zero.mpr
      intro hdiv
      have hqpos : 0 < n (k + 1) := lt_of_lt_of_le (Nat.zero_lt_succ k)
        (StrictMono.id_le hn (k + 1))
      have hq : (n (k + 1) : ℂ) ^ 2 ≠ 0 := by
        exact pow_ne_zero 2 (by exact_mod_cast hqpos.ne')
      have hsqC : (n (j + 1) : ℂ) ^ 2 = (n (k + 1) : ℂ) ^ 2 := by
        exact (div_eq_one_iff_eq hq).mp hdiv.symm
      have hsqN : n (j + 1) ^ 2 = n (k + 1) ^ 2 := by
        exact_mod_cast hsqC
      have hvalues : n (j + 1) = n (k + 1) :=
        Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) hsqN
      have hindices : j + 1 = k + 1 := hn.injective hvalues
      exact hkj (by omega)
  · have hs := summable_inverse_square_exponents hn
    have hbase : Summable
        (fun k : ℕ ↦ ‖-((n (j + 1) : ℂ) ^ 2 /
          (n (k + 1) : ℂ) ^ 2)‖) := by
      have hmul := hs.mul_left ‖(n (j + 1) : ℂ) ^ 2‖
      refine hmul.congr fun k ↦ ?_
      simp [norm_pow, div_eq_mul_inv]
    refine Summable.of_nonneg_of_le
      (f := fun k ↦ ‖-((n (j + 1) : ℂ) ^ 2 /
        (n (k + 1) : ℂ) ^ 2)‖)
      (g := fun k ↦ ‖if k = j then (0 : ℂ) else
        -((n (j + 1) : ℂ) ^ 2 / (n (k + 1) : ℂ) ^ 2)‖)
      (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hbase
    split_ifs
    · simpa only [norm_zero] using
        (norm_nonneg (-((n (j + 1) : ℂ) ^ 2 / (n (k + 1) : ℂ) ^ 2)))
    · exact le_rfl

/-- The comparison product for all positive integer zeros to the right of `m`. -/
private noncomputable def integerTailProduct (m : ℕ) : ℝ :=
  ∏' d : ℕ, (1 - (m : ℝ) ^ 2 / (m + d + 1 : ℝ) ^ 2)

private lemma integerTailProduct_multipliable (m : ℕ) :
    Multipliable (fun d : ℕ ↦ 1 - (m : ℝ) ^ 2 / (m + d + 1 : ℝ) ^ 2) := by
  have hbase : Summable (fun d : ℕ ↦ 1 / (d + 1 : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  have hshift : Summable (fun d : ℕ ↦ 1 / (m + d + 1 : ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun d ↦ ?_) hbase
    have hle : (d + 1 : ℝ) ≤ (m + d + 1 : ℝ) := by
      exact_mod_cast (show d + 1 ≤ m + d + 1 by omega)
    gcongr
  have hnorm : Summable (fun d : ℕ ↦
      ‖-((m : ℝ) ^ 2 / (m + d + 1 : ℝ) ^ 2)‖) := by
    have hmul := hshift.mul_left ‖(m : ℝ) ^ 2‖
    refine hmul.congr fun d ↦ ?_
    simp [abs_of_nonneg, div_eq_mul_inv]
  simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable hnorm

/-- The finite integer-tail product telescopes to a quotient of factorials. -/
private lemma integerTailPartial_formula (m N : ℕ) :
    (∏ d ∈ Finset.range N,
        (1 - (m : ℝ) ^ 2 / (m + d + 1 : ℝ) ^ 2)) =
      ((N.factorial : ℝ) * ((2 * m + N).factorial : ℝ) *
          (m.factorial : ℝ) ^ 2) /
        (((m + N).factorial : ℝ) ^ 2 * ((2 * m).factorial : ℝ)) := by
  induction N with
  | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one,
        Nat.zero_add, one_mul]
      field_simp
      ring_nf
  | succ N ih =>
      rw [Finset.prod_range_succ, ih]
      have h₁ : 2 * m + (N + 1) = (2 * m + N) + 1 := by omega
      have h₂ : m + (N + 1) = (m + N) + 1 := by omega
      rw [h₁, h₂, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      have hmN : (m + N + 1 : ℝ) ≠ 0 := by positivity
      have hfacN : (N.factorial : ℝ) ≠ 0 := by positivity
      have hfacM : (m.factorial : ℝ) ≠ 0 := by positivity
      have hfacMN : ((m + N).factorial : ℝ) ≠ 0 := by positivity
      have hfac2M : ((2 * m).factorial : ℝ) ≠ 0 := by positivity
      have hfac2MN : ((2 * m + N).factorial : ℝ) ≠ 0 := by positivity
      field_simp
      ring

private lemma integerTail_factorial_balance (m N : ℕ) :
    ((N.factorial : ℝ) * ((2 * m + N).factorial : ℝ)) /
        ((m + N).factorial : ℝ) ^ 2 =
      ((N + m + 1).ascFactorial m : ℝ) /
        ((N + 1).ascFactorial m : ℝ) := by
  have hleftNat := Nat.factorial_mul_ascFactorial N m
  have hrightNat := Nat.factorial_mul_ascFactorial (N + m) m
  have hleft : (N.factorial : ℝ) * ((N + 1).ascFactorial m : ℝ) =
      ((N + m).factorial : ℝ) := by
    exact_mod_cast hleftNat
  have hright : ((N + m).factorial : ℝ) * ((N + m + 1).ascFactorial m : ℝ) =
      ((2 * m + N).factorial : ℝ) := by
    have hrightNat' : (N + m).factorial * (N + m + 1).ascFactorial m =
        (2 * m + N).factorial := by
      calc
        (N + m).factorial * (N + m + 1).ascFactorial m =
            (N + m + m).factorial := hrightNat
        _ = (2 * m + N).factorial := by congr 1; omega
    exact_mod_cast hrightNat'
  have hNm : ((N + m).factorial : ℝ) ≠ 0 := by positivity
  have hasc : ((N + 1).ascFactorial m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ascFactorial_pos N m).ne'
  rw [Nat.add_comm m N]
  apply (div_eq_div_iff (pow_ne_zero 2 hNm) hasc).2
  calc
    (N.factorial : ℝ) * ((2 * m + N).factorial : ℝ) *
        ((N + 1).ascFactorial m : ℝ) =
        ((N + m).factorial : ℝ) * ((2 * m + N).factorial : ℝ) := by
      rw [← hleft]
      ring
    _ = ((N + m + 1).ascFactorial m : ℝ) *
        ((N + m).factorial : ℝ) ^ 2 := by
      rw [← hright]
      ring

private lemma integerTailProduct_formula (m : ℕ) :
    integerTailProduct m =
      (m.factorial : ℝ) ^ 2 / ((2 * m).factorial : ℝ) := by
  let q : ℕ → ℝ := fun N ↦ ∏ d ∈ Finset.range N,
    (1 - (m : ℝ) ^ 2 / (m + d + 1 : ℝ) ^ 2)
  let b : ℕ → ℝ := fun N ↦ ∏ i ∈ Finset.range m,
    ((N + m + 1 + i : ℕ) : ℝ) / ((N + 1 + i : ℕ) : ℝ)
  have hb : Tendsto b atTop (𝓝 1) := by
    have h := tendsto_finsetProd (M := ℝ) (Finset.range m)
      (f := fun i N ↦ ((N + m + 1 + i : ℕ) : ℝ) /
        ((N + 1 + i : ℕ) : ℝ)) (a := fun _ ↦ 1) (by
        intro i hi
        convert tendsto_add_mul_div_add_mul_atTop_nhds
          (𝕜 := ℝ) (m + 1 + i : ℝ) (1 + i : ℝ) 1 one_ne_zero using 1 <;>
          ext N <;> push_cast <;> ring_nf)
    simpa [b] using h
  have hq : Tendsto q atTop
      (𝓝 ((m.factorial : ℝ) ^ 2 / ((2 * m).factorial : ℝ))) := by
    let c : ℝ := (m.factorial : ℝ) ^ 2 / ((2 * m).factorial : ℝ)
    have hc : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c) := tendsto_const_nhds
    have hconst := hc.mul hb
    convert hconst using 1
    · ext N
      dsimp [q, b]
      rw [integerTailPartial_formula]
      rw [show
        ((N.factorial : ℝ) * ((2 * m + N).factorial : ℝ) * (m.factorial : ℝ) ^ 2) /
            (((m + N).factorial : ℝ) ^ 2 * ((2 * m).factorial : ℝ)) =
          (((N.factorial : ℝ) * ((2 * m + N).factorial : ℝ)) /
            ((m + N).factorial : ℝ) ^ 2) *
          ((m.factorial : ℝ) ^ 2 / ((2 * m).factorial : ℝ)) by ring]
      rw [integerTail_factorial_balance]
      have hratio :
          ((N + m + 1).ascFactorial m : ℝ) /
              ((N + 1).ascFactorial m : ℝ) =
            ∏ i ∈ Finset.range m,
              ((N + m + 1 + i : ℕ) : ℝ) / ((N + 1 + i : ℕ) : ℝ) := by
        rw [Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_prod_range,
          Finset.prod_div_distrib]
        simp only [Nat.cast_prod]
      rw [hratio]
      dsimp [c]
      ring
    · simp [c]
  have hprod : Tendsto q atTop (𝓝 (integerTailProduct m)) := by
    exact (integerTailProduct_multipliable m).hasProd.tendsto_prod_nat
  exact tendsto_nhds_unique hprod hq

private lemma integerTailProduct_lower_bound (m : ℕ) :
    (2 : ℝ) ^ (-(2 * m : ℤ)) ≤ integerTailProduct m := by
  rw [integerTailProduct_formula]
  have hchoose : (Nat.choose (2 * m) m : ℝ) ≤ (2 : ℝ) ^ (2 * m) := by
    exact_mod_cast Nat.choose_le_two_pow (2 * m) m
  have hfac : ((2 * m).factorial : ℝ) =
      (Nat.choose (2 * m) m : ℝ) * (m.factorial : ℝ) ^ 2 := by
    have hmle : m ≤ 2 * m := by omega
    have h := Nat.choose_mul_factorial_mul_factorial hmle
    have h' : Nat.choose (2 * m) m * m.factorial * m.factorial =
        (2 * m).factorial := by
      have hsub : 2 * m - m = m := by omega
      simpa only [hsub] using h
    calc
      ((2 * m).factorial : ℝ) =
          ((Nat.choose (2 * m) m * m.factorial * m.factorial : ℕ) : ℝ) := by
        exact_mod_cast h'.symm
      _ = (Nat.choose (2 * m) m : ℝ) * (m.factorial : ℝ) ^ 2 := by
        push_cast
        ring
  rw [hfac]
  have hmfac : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hchoosepos : (0 : ℝ) < Nat.choose (2 * m) m := by
    exact_mod_cast Nat.choose_pos (by omega : m ≤ 2 * m)
  have hcancel : (m.factorial : ℝ) ^ 2 /
      ((Nat.choose (2 * m) m : ℝ) * (m.factorial : ℝ) ^ 2) =
      1 / (Nat.choose (2 * m) m : ℝ) := by
    field_simp
  rw [hcancel, one_div, zpow_neg]
  exact (inv_le_inv₀ (by positivity) hchoosepos).2 hchoose

private lemma canonicalFactor_norm_lower_of_gap {m q d : ℕ} (hq : 0 < q)
    (hgap : d + q ≤ m) :
    (d : ℝ) / (m : ℝ) ≤
      ‖1 - (m : ℂ) ^ 2 / (q : ℂ) ^ 2‖ := by
  have hm : 0 < m := lt_of_lt_of_le hq (le_trans (Nat.le_add_left q d) hgap)
  have hqm : q ≤ m := le_trans (Nat.le_add_left q d) hgap
  have hdsub : d ≤ m - q := Nat.le_sub_of_add_le hgap
  have hmq : (1 : ℝ) ≤ (m : ℝ) / (q : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hq)).2
    simpa using (show (q : ℝ) ≤ (m : ℝ) by exact_mod_cast hqm)
  have hreal : (d : ℝ) / (m : ℝ) ≤
      (m : ℝ) ^ 2 / (q : ℝ) ^ 2 - 1 := by
    calc
      (d : ℝ) / (m : ℝ) ≤ ((m - q : ℕ) : ℝ) / (m : ℝ) := by
        gcongr
      _ ≤ ((m - q : ℕ) : ℝ) / (q : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hq) (by exact_mod_cast hqm)
      _ = (m : ℝ) / (q : ℝ) - 1 := by
        rw [Nat.cast_sub hqm]
        field_simp
      _ ≤ ((m : ℝ) / (q : ℝ)) ^ 2 - 1 := by
        nlinarith [sq_nonneg ((m : ℝ) / (q : ℝ) - 1)]
      _ = (m : ℝ) ^ 2 / (q : ℝ) ^ 2 - 1 := by field_simp
  have hnorm : ‖(m : ℂ) ^ 2 / (q : ℂ) ^ 2‖ - ‖(1 : ℂ)‖ ≤
      ‖(m : ℂ) ^ 2 / (q : ℂ) ^ 2 - 1‖ := norm_sub_norm_le _ _
  calc
    (d : ℝ) / (m : ℝ) ≤ (m : ℝ) ^ 2 / (q : ℝ) ^ 2 - 1 := hreal
    _ = ‖(m : ℂ) ^ 2 / (q : ℂ) ^ 2‖ - ‖(1 : ℂ)‖ := by
      simp [norm_div, norm_pow]
    _ ≤ ‖(m : ℂ) ^ 2 / (q : ℂ) ^ 2 - 1‖ := hnorm
    _ = ‖1 - (m : ℂ) ^ 2 / (q : ℂ) ^ 2‖ := by
      rw [← norm_neg]
      congr 1
      ring

private lemma exponentCanonicalProduct_head_lower_bound {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) :
    Real.exp (-(n (j + 1) : ℝ)) ≤
      ∏ k ∈ Finset.range j,
        ‖1 - (n (j + 1) : ℂ) ^ 2 / (n (k + 1) : ℂ) ^ 2‖ := by
  let m := n (j + 1)
  have hm : 0 < m := lt_of_lt_of_le (Nat.zero_lt_succ j) (StrictMono.id_le hn (j + 1))
  have hpoint : ∀ k ∈ Finset.range j,
      ((j - k : ℕ) : ℝ) / (m : ℝ) ≤
        ‖1 - (m : ℂ) ^ 2 / (n (k + 1) : ℂ) ^ 2‖ := by
    intro k hk
    have hkj : k < j := Finset.mem_range.1 hk
    have hq : 0 < n (k + 1) := lt_of_lt_of_le (Nat.zero_lt_succ k)
      (StrictMono.id_le hn (k + 1))
    have hgap : (j - k) + n (k + 1) ≤ m := by
      have hadd := hn.add_le_nat (j - k) (k + 1)
      have hidx : (j - k) + (k + 1) = j + 1 := by omega
      simpa [m, hidx] using hadd
    exact canonicalFactor_norm_lower_of_gap hq hgap
  have hprod : ((j.factorial : ℝ) / (m : ℝ) ^ j) ≤
      ∏ k ∈ Finset.range j,
        ‖1 - (m : ℂ) ^ 2 / (n (k + 1) : ℂ) ^ 2‖ := by
    have hnumNat : ∏ k ∈ Finset.range j, (j - k) = j.factorial := by
      calc
        ∏ k ∈ Finset.range j, (j - k) =
            ∏ k ∈ Finset.range j, (j - 1 - k + 1) := by
          apply Finset.prod_congr rfl
          intro k hk
          have hkj : k < j := Finset.mem_range.1 hk
          omega
        _ = ∏ k ∈ Finset.range j, (k + 1) := by
          exact Finset.prod_range_reflect (fun k : ℕ ↦ k + 1) j
        _ = j.factorial := Finset.prod_range_add_one_eq_factorial j
    calc
      (j.factorial : ℝ) / (m : ℝ) ^ j =
          ∏ k ∈ Finset.range j, (((j - k : ℕ) : ℝ) / (m : ℝ)) := by
        rw [Finset.prod_div_distrib]
        simp only [Finset.card_range, Finset.prod_const, nsmul_eq_mul]
        congr 1
        exact_mod_cast hnumNat.symm
      _ ≤ ∏ k ∈ Finset.range j,
          ‖1 - (m : ℂ) ^ 2 / (n (k + 1) : ℂ) ^ 2‖ := by
        apply Finset.prod_le_prod
        · intro k hk
          positivity
        · exact hpoint
  have hpow : (m : ℝ) ^ j / (j.factorial : ℝ) ≤ Real.exp (m : ℝ) :=
    Real.pow_div_factorial_le_exp (m : ℝ) (by positivity) j
  have hinv : (Real.exp (m : ℝ))⁻¹ ≤
      ((m : ℝ) ^ j / (j.factorial : ℝ))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  have hleft : Real.exp (-(m : ℝ)) ≤ (j.factorial : ℝ) / (m : ℝ) ^ j := by
    rw [Real.exp_neg]
    convert hinv using 1
    field_simp
  exact hleft.trans hprod

private lemma canonicalFactor_norm_ge_integerTail {m q d : ℕ}
    (hgap : m + d + 1 ≤ q) :
    1 - (m : ℝ) ^ 2 / (m + d + 1 : ℝ) ^ 2 ≤
      ‖1 - (m : ℂ) ^ 2 / (q : ℂ) ^ 2‖ := by
  have hdenpos : (0 : ℝ) < (m + d + 1 : ℕ) := by positivity
  have hqpos : (0 : ℝ) < q := by exact_mod_cast lt_of_lt_of_le (by omega : 0 < m + d + 1) hgap
  have hmleq : m ≤ q := le_trans (by omega : m ≤ m + d + 1) hgap
  have hfrac : (m : ℝ) ^ 2 / (q : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hqpos)]
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 (by exact_mod_cast hmleq)
  have hden : ((m + d + 1 : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 (by exact_mod_cast hgap)
  have hquot : (m : ℝ) ^ 2 / (q : ℝ) ^ 2 ≤
      (m : ℝ) ^ 2 / ((m + d + 1 : ℕ) : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hdenpos) hden
  have hcast : 1 - (m : ℂ) ^ 2 / (q : ℂ) ^ 2 =
      ((1 - (m : ℝ) ^ 2 / (q : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hnormeq : ‖1 - (m : ℂ) ^ 2 / (q : ℂ) ^ 2‖ =
      1 - (m : ℝ) ^ 2 / (q : ℝ) ^ 2 := by
    calc
      ‖1 - (m : ℂ) ^ 2 / (q : ℂ) ^ 2‖ =
          ‖((1 - (m : ℝ) ^ 2 / (q : ℝ) ^ 2 : ℝ) : ℂ)‖ :=
        congrArg norm hcast
      _ = |1 - (m : ℝ) ^ 2 / (q : ℝ) ^ 2| := Complex.norm_real _
      _ = 1 - (m : ℝ) ^ 2 / (q : ℝ) ^ 2 :=
        abs_of_nonneg (sub_nonneg.2 hfrac)
  rw [hnormeq]
  push_cast at hquot
  linarith

private lemma exponentCanonicalProduct_tail_lower_bound {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) :
    integerTailProduct (n (j + 1)) ≤
      ∏' d : ℕ,
        ‖1 - (n (j + 1) : ℂ) ^ 2 /
          (n (d + (j + 1) + 1) : ℂ) ^ 2‖ := by
  let s : ℕ → ℝ := fun d ↦
    1 - (n (j + 1) : ℝ) ^ 2 / (n (j + 1) + d + 1 : ℝ) ^ 2
  let p : ℕ → ℝ := fun d ↦
    ‖1 - (n (j + 1) : ℂ) ^ 2 /
      (n (d + (j + 1) + 1) : ℂ) ^ 2‖
  have hs : Multipliable s := integerTailProduct_multipliable (n (j + 1))
  have hp : Multipliable p := by
    have hbase : Summable (fun d : ℕ ↦
        1 / (n (d + (j + 1) + 1) : ℝ) ^ 2) := by
      have hfull := summable_inverse_square_exponents hn
      simpa only [Nat.add_assoc] using (summable_nat_add_iff (j + 1)).2 hfull
    have hnorm : Summable (fun d : ℕ ↦
        ‖-((n (j + 1) : ℂ) ^ 2 /
          (n (d + (j + 1) + 1) : ℂ) ^ 2)‖) := by
      have hmul := hbase.mul_left ‖(n (j + 1) : ℂ) ^ 2‖
      refine hmul.congr fun d ↦ ?_
      simp [norm_pow, div_eq_mul_inv]
    have hc : Multipliable (fun d : ℕ ↦ 1 +
        -((n (j + 1) : ℂ) ^ 2 /
          (n (d + (j + 1) + 1) : ℂ) ^ 2)) :=
      multipliable_one_add_of_summable hnorm
    simpa only [p, sub_eq_add_neg] using hc.norm
  have hle : ∀ d, s d ≤ p d := by
    intro d
    have hgapNat := hn.add_le_nat (d + 1) (j + 1)
    have hgap : n (j + 1) + d + 1 ≤ n (d + (j + 1) + 1) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hgapNat
    dsimp [s, p]
    exact canonicalFactor_norm_ge_integerTail hgap
  have hsnonneg : ∀ d, 0 ≤ s d := by
    intro d
    dsimp [s]
    rw [sub_nonneg, div_le_one (by positivity)]
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 (by
      exact_mod_cast (show n (j + 1) ≤ n (j + 1) + d + 1 by omega))
  exact le_of_tendsto_of_tendsto' hs.hasProd.tendsto_prod_nat hp.hasProd.tendsto_prod_nat
    (fun N ↦ Finset.prod_le_prod (fun d hd ↦ hsnonneg d) (fun d hd ↦ hle d))

private noncomputable abbrev exponentCanonicalProductAwayNormFactor
    (n : ℕ → ℕ) (j k : ℕ) : ℝ :=
  ‖1 + (if k = j then 0 else
    -((n (j + 1) : ℂ) ^ 2 / (n (k + 1) : ℂ) ^ 2))‖

private lemma exponentCanonicalProductAwayNormFactor_multipliable {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) :
    Multipliable (exponentCanonicalProductAwayNormFactor n j) := by
  simpa only [exponentCanonicalProductAwayNormFactor] using
    (exponentCanonicalProductAway_multipliable hn j (n (j + 1) : ℂ)).norm

private lemma exponentCanonicalProductAway_norm_eq_tprod {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) :
    ‖exponentCanonicalProductAway n j (n (j + 1) : ℂ)‖ =
      ∏' k : ℕ, exponentCanonicalProductAwayNormFactor n j k := by
  rw [exponentCanonicalProductAway]
  exact (exponentCanonicalProductAway_multipliable hn j
    (n (j + 1) : ℂ)).norm_tprod

private lemma exponentCanonicalProductAwayNormFactor_head_lower {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) :
    Real.exp (-(n (j + 1) : ℝ)) ≤
      ∏ k ∈ Finset.range (j + 1), exponentCanonicalProductAwayNormFactor n j k := by
  rw [Finset.prod_range_succ]
  have hlast : exponentCanonicalProductAwayNormFactor n j j = 1 := by
    simp [exponentCanonicalProductAwayNormFactor]
  rw [hlast, mul_one]
  have hbase := exponentCanonicalProduct_head_lower_bound hn j
  convert hbase using 1
  apply Finset.prod_congr rfl
  intro k hk
  have hkj : k ≠ j := ne_of_lt (Finset.mem_range.1 hk)
  change ‖1 + (if k = j then 0 else
    -((n (j + 1) : ℂ) ^ 2 / (n (k + 1) : ℂ) ^ 2))‖ = _
  rw [if_neg hkj]
  rfl

private lemma exponentCanonicalProductAwayNormFactor_tail_lower {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) :
    (2 : ℝ) ^ (-(2 * n (j + 1) : ℤ)) ≤
      ∏' d : ℕ, exponentCanonicalProductAwayNormFactor n j (d + (j + 1)) := by
  calc
    (2 : ℝ) ^ (-(2 * n (j + 1) : ℤ)) ≤ integerTailProduct (n (j + 1)) :=
      integerTailProduct_lower_bound (n (j + 1))
    _ ≤ ∏' d : ℕ, ‖1 - (n (j + 1) : ℂ) ^ 2 /
        (n (d + (j + 1) + 1) : ℂ) ^ 2‖ :=
      exponentCanonicalProduct_tail_lower_bound hn j
    _ = ∏' d : ℕ, exponentCanonicalProductAwayNormFactor n j (d + (j + 1)) := by
      apply tprod_congr
      intro d
      simp [exponentCanonicalProductAwayNormFactor, sub_eq_add_neg,
        show d + (j + 1) ≠ j by omega]

private lemma integerTailProduct_le_partial (m N : ℕ) :
    integerTailProduct m ≤
      ∏ d ∈ Finset.range N, (1 - (m : ℝ) ^ 2 / (m + d + 1 : ℝ) ^ 2) := by
  let s : ℕ → ℝ := fun d ↦ 1 - (m : ℝ) ^ 2 / (m + d + 1 : ℝ) ^ 2
  have hs : Multipliable s := integerTailProduct_multipliable m
  have hsnonneg : ∀ d, 0 ≤ s d := by
    intro d
    dsimp [s]
    rw [sub_nonneg, div_le_one (by positivity)]
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 (by
      exact_mod_cast (show m ≤ m + d + 1 by omega))
  have hsleone : ∀ d, s d ≤ 1 := by
    intro d
    dsimp [s]
    exact sub_le_self _ (by positivity)
  apply le_of_tendsto hs.hasProd.tendsto_prod_nat
  filter_upwards [eventually_ge_atTop N] with K hK
  rw [← Nat.add_sub_of_le hK, Finset.prod_range_add]
  have htail : (∏ d ∈ Finset.range (K - N), s (N + d)) ≤ 1 :=
    Finset.prod_le_one (fun d hd ↦ hsnonneg (N + d)) (fun d hd ↦ hsleone (N + d))
  have hheadnonneg : 0 ≤ ∏ d ∈ Finset.range N, s d :=
    Finset.prod_nonneg fun d hd ↦ hsnonneg d
  calc
    (∏ d ∈ Finset.range N, s d) * ∏ d ∈ Finset.range (K - N), s (N + d) ≤
        (∏ d ∈ Finset.range N, s d) * 1 :=
      mul_le_mul_of_nonneg_left htail hheadnonneg
    _ = ∏ d ∈ Finset.range N, s d := mul_one _

private lemma exponentCanonicalProductAwayNormFactor_finite_lower {n : ℕ → ℕ}
    (hn : StrictMono n) (j N : ℕ) :
    Real.exp (-(n (j + 1) : ℝ)) *
        (2 : ℝ) ^ (-(2 * n (j + 1) : ℤ)) ≤
      ∏ k ∈ Finset.range ((j + 1) + N),
        exponentCanonicalProductAwayNormFactor n j k := by
  rw [Finset.prod_range_add]
  have hhead := exponentCanonicalProductAwayNormFactor_head_lower hn j
  have hsnonneg : ∀ d : ℕ, 0 ≤
      1 - (n (j + 1) : ℝ) ^ 2 / (n (j + 1) + d + 1 : ℝ) ^ 2 := by
    intro d
    rw [sub_nonneg, div_le_one (by positivity)]
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 (by
      exact_mod_cast (show n (j + 1) ≤ n (j + 1) + d + 1 by omega))
  have hpoint : ∀ d : ℕ, 1 - (n (j + 1) : ℝ) ^ 2 /
      (n (j + 1) + d + 1 : ℝ) ^ 2 ≤
        exponentCanonicalProductAwayNormFactor n j (j + 1 + d) := by
    intro d
    have hgapNat := hn.add_le_nat (d + 1) (j + 1)
    have hgap : n (j + 1) + d + 1 ≤ n (j + 1 + d + 1) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hgapNat
    have h := canonicalFactor_norm_ge_integerTail hgap
    simpa [exponentCanonicalProductAwayNormFactor, sub_eq_add_neg,
      show j + 1 + d ≠ j by omega, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have htail : (2 : ℝ) ^ (-(2 * n (j + 1) : ℤ)) ≤
      ∏ d ∈ Finset.range N, exponentCanonicalProductAwayNormFactor n j (j + 1 + d) := by
    calc
      (2 : ℝ) ^ (-(2 * n (j + 1) : ℤ)) ≤ integerTailProduct (n (j + 1)) :=
        integerTailProduct_lower_bound (n (j + 1))
      _ ≤ ∏ d ∈ Finset.range N,
          (1 - (n (j + 1) : ℝ) ^ 2 / (n (j + 1) + d + 1 : ℝ) ^ 2) :=
        integerTailProduct_le_partial (n (j + 1)) N
      _ ≤ ∏ d ∈ Finset.range N,
          exponentCanonicalProductAwayNormFactor n j (j + 1 + d) :=
        Finset.prod_le_prod (fun d hd ↦ hsnonneg d) (fun d hd ↦ hpoint d)
  have hheadnonneg : 0 ≤ ∏ k ∈ Finset.range (j + 1),
      exponentCanonicalProductAwayNormFactor n j k :=
    Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  exact mul_le_mul hhead htail (by positivity) hheadnonneg

private lemma exponentCanonicalProductAway_norm_lower_bound {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) :
    Real.exp (-(n (j + 1) : ℝ)) *
        (2 : ℝ) ^ (-(2 * n (j + 1) : ℤ)) ≤
      ‖exponentCanonicalProductAway n j (n (j + 1) : ℂ)‖ := by
  rw [exponentCanonicalProductAway_norm_eq_tprod hn j]
  have hp := exponentCanonicalProductAwayNormFactor_multipliable hn j
  apply ge_of_tendsto (hp.hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat (j + 1)))
  filter_upwards with N
  change Real.exp (-(n (j + 1) : ℝ)) *
      (2 : ℝ) ^ (-(2 * n (j + 1) : ℤ)) ≤
    ∏ k ∈ Finset.range (N + (j + 1)), exponentCanonicalProductAwayNormFactor n j k
  simpa only [Nat.add_comm] using exponentCanonicalProductAwayNormFactor_finite_lower hn j N

/-- Quantitative separated-zero estimate.  This is the exact derivative bound from which
the finite condensation index of the integer exponent sequence is read off. -/
private lemma deriv_exponentCanonicalProduct_at_exponent_lower {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) :
    (2 / (n (j + 1) : ℝ)) *
        (Real.exp (-(n (j + 1) : ℝ)) *
          (2 : ℝ) ^ (-(2 * n (j + 1) : ℤ))) ≤
      ‖deriv (exponentCanonicalProduct n) (n (j + 1) : ℂ)‖ := by
  have hm : 0 < n (j + 1) := lt_of_lt_of_le (Nat.zero_lt_succ j)
    (StrictMono.id_le hn (j + 1))
  have haway := exponentCanonicalProductAway_norm_lower_bound hn j
  rw [deriv_exponentCanonicalProduct_at_exponent hn j, norm_mul]
  have hfactor : ‖(-2 : ℂ) / (n (j + 1) : ℂ)‖ =
      2 / (n (j + 1) : ℝ) := by
    simp [norm_div, Real.norm_of_nonneg]
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left haway (by positivity)

/-- The separated integer zeros give the exponential derivative estimate used in the
finite-condensation argument.  The deliberately coarse constant `4` is uniform in the
strictly increasing exponent sequence. -/
private lemma deriv_exponentCanonicalProduct_at_exponent_exp_lower {n : ℕ → ℕ}
    (hn : StrictMono n) (j : ℕ) :
    Real.exp (-(4 * (n (j + 1) : ℝ))) ≤
      ‖deriv (exponentCanonicalProduct n) (n (j + 1) : ℂ)‖ := by
  have hm : 0 < n (j + 1) := lt_of_lt_of_le (Nat.zero_lt_succ j)
    (StrictMono.id_le hn (j + 1))
  have hmR : 0 < (n (j + 1) : ℝ) := by exact_mod_cast hm
  let q : ℝ :=
    (2 / (n (j + 1) : ℝ)) *
      (Real.exp (-(n (j + 1) : ℝ)) *
        (2 : ℝ) ^ (-(2 * n (j + 1) : ℤ)))
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hlogm : Real.log (n (j + 1) : ℝ) ≤ (n (j + 1) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hmR
  have hlog2upper : Real.log 2 ≤ (1 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢
    exact this
  have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogq : -(4 * (n (j + 1) : ℝ)) ≤ Real.log q := by
    dsimp [q]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by norm_num) hmR.ne',
      Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_zpow]
    push_cast
    nlinarith
  calc
    Real.exp (-(4 * (n (j + 1) : ℝ))) ≤ Real.exp (Real.log q) :=
      Real.exp_le_exp.mpr hlogq
    _ = q := Real.exp_log hqpos
    _ ≤ ‖deriv (exponentCanonicalProduct n) (n (j + 1) : ℂ)‖ :=
      deriv_exponentCanonicalProduct_at_exponent_lower hn j

/-- A concrete, limsup-free interface for the finite condensation index.  It is stronger
than the eventual bound needed in Leontiev's interpolation theorem. -/
private def HasFiniteCondensation (n : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, ∀ j : ℕ,
    Real.log (1 / ‖deriv (exponentCanonicalProduct n) (n (j + 1) : ℂ)‖) /
      (n (j + 1) : ℝ) ≤ C

private lemma hasFiniteCondensation_of_strictMono {n : ℕ → ℕ} (hn : StrictMono n) :
    HasFiniteCondensation n := by
  refine ⟨4, fun j ↦ ?_⟩
  have hm : 0 < n (j + 1) := lt_of_lt_of_le (Nat.zero_lt_succ j)
    (StrictMono.id_le hn (j + 1))
  have hmR : 0 < (n (j + 1) : ℝ) := by exact_mod_cast hm
  have hderiv := deriv_exponentCanonicalProduct_at_exponent_exp_lower hn j
  have hderivpos : 0 < ‖deriv (exponentCanonicalProduct n) (n (j + 1) : ℂ)‖ :=
    (Real.exp_pos _).trans_le hderiv
  have hlog : -(4 * (n (j + 1) : ℝ)) ≤
      Real.log ‖deriv (exponentCanonicalProduct n) (n (j + 1) : ℂ)‖ := by
    calc
      -(4 * (n (j + 1) : ℝ)) =
          Real.log (Real.exp (-(4 * (n (j + 1) : ℝ)))) := (Real.log_exp _).symm
      _ ≤ Real.log ‖deriv (exponentCanonicalProduct n) (n (j + 1) : ℂ)‖ :=
        Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hderivpos hderiv
  rw [div_le_iff₀ hmR]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hderivpos.ne', Real.log_one]
  linarith

private noncomputable def standardSquareProduct (x : ℝ) : ℝ :=
  ∏' k : ℕ, (1 + x ^ 2 / (k + 1 : ℝ) ^ 2)

private lemma standardSquareProduct_multipliable (x : ℝ) :
    Multipliable (fun k : ℕ ↦ 1 + x ^ 2 / (k + 1 : ℝ) ^ 2) := by
  have hs : Summable (fun k : ℕ ↦ ‖x ^ 2 / (k + 1 : ℝ) ^ 2‖) := by
    have hbase : Summable (fun k : ℕ ↦ 1 / (k + 1 : ℝ) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    have hmul := hbase.mul_left ‖x ^ 2‖
    refine hmul.congr fun k ↦ ?_
    simp [abs_of_nonneg, div_eq_mul_inv]
  exact multipliable_one_add_of_summable hs

private lemma standardSquareProduct_formula (x : ℝ) :
    Real.pi * x * standardSquareProduct x = Real.sinh (Real.pi * x) := by
  let p : ℕ → ℝ := fun N ↦
    ∏ k ∈ Finset.range N, (1 + x ^ 2 / (k + 1 : ℝ) ^ 2)
  have hp : Tendsto p atTop (𝓝 (standardSquareProduct x)) := by
    exact (standardSquareProduct_multipliable x).hasProd.tendsto_prod_nat
  have hpC : Tendsto (fun N ↦ (p N : ℂ)) atTop
      (𝓝 (standardSquareProduct x : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hp
  let d : ℂ := (Real.pi : ℂ) * (x : ℂ) * Complex.I
  have hmul : Tendsto (fun N ↦ d * (p N : ℂ)) atTop
      (𝓝 (d * (standardSquareProduct x : ℂ))) := tendsto_const_nhds.mul hpC
  have heq : ∀ N, (Real.pi : ℂ) * ((x : ℂ) * Complex.I) *
      ∏ k ∈ Finset.range N,
        (1 - ((x : ℂ) * Complex.I) ^ 2 / ((k : ℂ) + 1) ^ 2) = d * (p N : ℂ) := by
    intro N
    simp only [p, d]
    push_cast
    rw [mul_assoc (Real.pi : ℂ) (x : ℂ) Complex.I]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [mul_pow, Complex.I_sq]
    ring
  have heuler : Tendsto (fun N ↦ d * (p N : ℂ)) atTop
      (𝓝 (Complex.sin ((Real.pi : ℂ) * ((x : ℂ) * Complex.I)))) := by
    exact (Complex.tendsto_euler_sin_prod ((x : ℂ) * Complex.I)).congr'
      (Filter.Eventually.of_forall fun N ↦ heq N)
  have hlimit : d * (standardSquareProduct x : ℂ) =
      Complex.sin ((Real.pi : ℂ) * ((x : ℂ) * Complex.I)) :=
    tendsto_nhds_unique hmul heuler
  have hI : (((Real.pi * x * standardSquareProduct x : ℝ) : ℂ) * Complex.I) =
      (((Real.sinh (Real.pi * x) : ℝ) : ℂ) * Complex.I) := by
    calc
      (((Real.pi * x * standardSquareProduct x : ℝ) : ℂ) * Complex.I)
          = d * (standardSquareProduct x : ℂ) := by simp [d]; ring
      _ = Complex.sin ((Real.pi : ℂ) * ((x : ℂ) * Complex.I)) := hlimit
      _ = (((Real.sinh (Real.pi * x) : ℝ) : ℂ) * Complex.I) := by
        rw [show (Real.pi : ℂ) * ((x : ℂ) * Complex.I) =
          ((Real.pi * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [Complex.sin_mul_I, ← Complex.ofReal_sinh]
  exact_mod_cast (mul_right_cancel₀ Complex.I_ne_zero hI)

private lemma standardSquareProduct_le_exp {x : ℝ} (hx : 1 ≤ x) :
    standardSquareProduct x ≤ Real.exp (Real.pi * x) := by
  have hpix : 0 < Real.pi * x := mul_pos Real.pi_pos (lt_of_lt_of_le zero_lt_one hx)
  rw [← (mul_le_mul_iff_of_pos_left hpix)]
  rw [standardSquareProduct_formula]
  have hsinh : Real.sinh (Real.pi * x) ≤ Real.exp (Real.pi * x) := by
    rw [Real.sinh_eq]
    nlinarith [Real.exp_pos (Real.pi * x), Real.exp_pos (-(Real.pi * x))]
  calc
    Real.sinh (Real.pi * x) ≤ Real.exp (Real.pi * x) := hsinh
    _ ≤ (Real.pi * x) * Real.exp (Real.pi * x) := by
      have h₁ : 1 ≤ Real.pi * x := by nlinarith [Real.pi_gt_three]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right h₁ (Real.exp_pos (Real.pi * x)).le

private lemma fabry_eventually_linear {n : ℕ → ℕ} (hn : HasFabryGaps n) (C : ℝ) :
    ∃ K : ℕ, ∀ k ≥ K, C * (k : ℝ) ≤ (n k : ℝ) := by
  obtain ⟨K, hK⟩ := (eventually_atTop.1 (hn.2.eventually_ge_atTop C))
  refine ⟨K, fun k hk ↦ ?_⟩
  have hratio : C ≤ (n k : ℝ) / (k : ℝ) := hK k hk
  by_cases hk0 : k = 0
  · simp [hk0]
  · exact (le_div_iff₀ (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk0))).1 hratio

/-- Equivalent zero-density form of the Fabry condition: the index of an exponent is
eventually an arbitrarily small multiple of that exponent. -/
private lemma fabry_eventually_index_le {n : ℕ → ℕ} (hn : HasFabryGaps n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (k : ℝ) ≤ ε * (n k : ℝ) := by
  obtain ⟨K, hK⟩ := fabry_eventually_linear hn (1 / ε)
  filter_upwards [eventually_ge_atTop K] with k hk
  have hlin := hK k hk
  have hε0 : ε ≠ 0 := hε.ne'
  calc
    (k : ℝ) = ε * ((1 / ε) * (k : ℝ)) := by field_simp
    _ ≤ ε * (n k : ℝ) := mul_le_mul_of_nonneg_left hlin hε.le

/-- The number of displayed exponents below `N` is `o(N)`, the counting
form of the Fabry hypothesis used in every finite localization. -/
private lemma gapHead_card_div_tendsto_zero {n : ℕ → ℕ} (hn : HasFabryGaps n) :
    Tendsto (fun N : ℕ ↦ ((gapHead n N).card : ℝ) / (N : ℝ)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (fabry_eventually_index_le hn hε4)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((4 * (K₀ + 1 : ℕ) : ℝ) / ε)
  refine ⟨max 1 N₀, fun N hN ↦ ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left _ _) hN)
  have hN₀' : N₀ ≤ N := (le_max_right 1 N₀).trans hN
  have hlargeR : (4 : ℝ) * (K₀ + 1 : ℕ) / ε < N := by
    exact hN₀.trans_le (by exact_mod_cast hN₀')
  have hhead := gapHead_card_le_add hn.1 hε4 (fun k hk ↦ hK₀ k hk) N
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hconst : (K₀ : ℝ) + 1 < (ε / 4) * (N : ℝ) := by
    rw [div_lt_iff₀ hε] at hlargeR
    simp only [Nat.cast_add, Nat.cast_one] at hlargeR
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hNposR.le)]
  rw [div_lt_iff₀ hNposR]
  have hhead' : ((gapHead n N).card : ℝ) ≤
      (K₀ : ℝ) + (ε / 4) * (N : ℝ) + 1 := hhead
  nlinarith

private lemma canonicalFactor_norm_le {ζ : ℂ} {m : ℕ} (hm : 0 < m) :
    ‖1 - ζ ^ 2 / (m : ℂ) ^ 2‖ ≤ 1 + ‖ζ‖ ^ 2 / (m : ℝ) ^ 2 := by
  calc
    ‖1 - ζ ^ 2 / (m : ℂ) ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖ζ ^ 2 / (m : ℂ) ^ 2‖ := norm_sub_le _ _
    _ = 1 + ‖ζ‖ ^ 2 / (m : ℝ) ^ 2 := by
      simp [norm_div, norm_pow, Real.norm_of_nonneg]

private lemma canonicalFactor_majorized_by_standard {R C : ℝ} {m k : ℕ}
    (hR : 0 ≤ R) (hC : 0 < C) (hk : 0 < k) (hm : 0 < m)
    (hlinear : C * (k : ℝ) ≤ (m : ℝ)) :
    1 + R ^ 2 / (m : ℝ) ^ 2 ≤ 1 + (R / C) ^ 2 / (k : ℝ) ^ 2 := by
  have hden : C ^ 2 * (k : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
    have hx : 0 ≤ C * (k : ℝ) := mul_nonneg hC.le (Nat.cast_nonneg k)
    have hy : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hprod : 0 ≤ ((m : ℝ) - C * (k : ℝ)) * ((m : ℝ) + C * (k : ℝ)) :=
      mul_nonneg (sub_nonneg.2 hlinear) (add_nonneg hy hx)
    nlinarith
  have hdenpos : 0 < C ^ 2 * (k : ℝ) ^ 2 := mul_pos (sq_pos_of_pos hC) (sq_pos_of_pos (by exact_mod_cast hk))
  have hdiv : R ^ 2 / (m : ℝ) ^ 2 ≤ R ^ 2 / (C ^ 2 * (k : ℝ) ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg R) hdenpos hden
  calc
    1 + R ^ 2 / (m : ℝ) ^ 2 ≤ 1 + R ^ 2 / (C ^ 2 * (k : ℝ) ^ 2) := by linarith
    _ = 1 + (R / C) ^ 2 / (k : ℝ) ^ 2 := by field_simp

/-- Every fixed polynomial in the radius is eventually dominated by an arbitrarily small
exponential.  This is the elementary finite-head estimate in the canonical-product argument. -/
private lemma eventually_one_add_sq_pow_le_exp (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, (1 + R ^ 2) ^ K ≤ Real.exp (ε * R) := by
  have hlog := Real.isLittleO_log_id_atTop
  have hscaled : (fun R : ℝ ↦ (4 * K : ℝ) * Real.log R) =o[atTop]
      (fun R : ℝ ↦ ε * R) := by
    simpa only [id_eq] using
      (hlog.const_mul_left (4 * K : ℝ)).const_mul_right hε.ne'
  have hevent : ∀ᶠ R : ℝ in atTop, (4 * K : ℝ) * Real.log R ≤ ε * R := by
    filter_upwards [eventually_ge_atTop 1, hscaled.bound one_pos] with R hR hbound
    have hlognonneg : 0 ≤ Real.log R := Real.log_nonneg hR
    have hleft : 0 ≤ (4 * K : ℝ) * Real.log R :=
      mul_nonneg (by positivity) hlognonneg
    have hright : 0 ≤ ε * R := mul_nonneg hε.le (zero_le_one.trans hR)
    simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using hbound
  filter_upwards [eventually_ge_atTop 2, hevent] with R hR hlogR
  have hbase : 1 + R ^ 2 ≤ R ^ 2 * R ^ 2 := by
    nlinarith [sq_nonneg R, sq_nonneg (R ^ 2 - 1)]
  have hnonneg : 0 ≤ 1 + R ^ 2 := by positivity
  calc
    (1 + R ^ 2) ^ K ≤ (R ^ 2 * R ^ 2) ^ K := pow_le_pow_left₀ hnonneg hbase K
    _ = Real.exp ((4 * K : ℝ) * Real.log R) := by
      rw [show R ^ 2 * R ^ 2 = R ^ 4 by ring, ← pow_mul]
      rw [← Real.exp_log (by positivity : 0 < R), ← Real.exp_nat_mul]
      congr 2
      · simp
      · norm_num
    _ ≤ Real.exp (ε * R) := Real.exp_le_exp.mpr hlogR

/-- Comparison of the exponent product with a finite polynomial head and Euler's square
product.  The only information used on the tail is the linear lower bound on the exponents. -/
private lemma exponentCanonicalProduct_norm_le_head_mul_standard {n : ℕ → ℕ}
    (hn : StrictMono n) {C R : ℝ} (hC : 0 < C) (hR : 0 ≤ R) {K : ℕ}
    (hlinear : ∀ j ≥ K, C * (j : ℝ) ≤ (n j : ℝ)) {ζ : ℂ} (hζ : ‖ζ‖ ≤ R) :
    ‖exponentCanonicalProduct n ζ‖ ≤
      (1 + R ^ 2) ^ K * standardSquareProduct (R / C) := by
  classical
  let q : ℕ → ℝ := fun k ↦ ‖1 - ζ ^ 2 / (n (k + 1) : ℂ) ^ 2‖
  let e : ℕ → ℝ := fun k ↦ 1 + (R / C) ^ 2 / (k + 1 : ℝ) ^ 2
  have hqm : Multipliable q := (exponentCanonicalProduct_multipliable hn ζ).norm
  have hem : Multipliable e := standardSquareProduct_multipliable (R / C)
  have hq : ∀ k, q k ≤ if k + 1 < K then 1 + R ^ 2 else e k := by
    intro k
    have hnkpos : 0 < n (k + 1) := lt_of_lt_of_le (Nat.zero_lt_succ k)
      (StrictMono.id_le hn (k + 1))
    split_ifs with hk
    · calc
        q k ≤ 1 + ‖ζ‖ ^ 2 / (n (k + 1) : ℝ) ^ 2 :=
          canonicalFactor_norm_le hnkpos
        _ ≤ 1 + R ^ 2 := by
          have hncast : (1 : ℝ) ≤ n (k + 1) := by exact_mod_cast hnkpos
          have hden : (1 : ℝ) ≤ (n (k + 1) : ℝ) ^ 2 := by nlinarith
          have hnum : ‖ζ‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg ζ]
          have hdiv : ‖ζ‖ ^ 2 / (n (k + 1) : ℝ) ^ 2 ≤ R ^ 2 := by
            calc
              ‖ζ‖ ^ 2 / (n (k + 1) : ℝ) ^ 2 ≤ R ^ 2 / 1 := by
                exact div_le_div₀ (sq_nonneg R) hnum zero_lt_one hden
              _ = R ^ 2 := div_one _
          linarith
    · calc
        q k ≤ 1 + ‖ζ‖ ^ 2 / (n (k + 1) : ℝ) ^ 2 :=
          canonicalFactor_norm_le hnkpos
        _ ≤ 1 + R ^ 2 / (n (k + 1) : ℝ) ^ 2 := by
          gcongr
        _ ≤ e k := by
          simpa only [e, Nat.cast_succ] using
            canonicalFactor_majorized_by_standard hR hC (Nat.zero_lt_succ k) hnkpos
              (hlinear (k + 1) (Nat.le_of_not_gt hk))
  rw [exponentCanonicalProduct, (exponentCanonicalProduct_multipliable hn ζ).norm_tprod]
  refine hqm.tprod_le_of_prod_le fun s ↦ ?_
  let head := s.filter fun k ↦ k + 1 < K
  let tail := s.filter fun k ↦ ¬ k + 1 < K
  have hsplit : (∏ k ∈ head, q k) * (∏ k ∈ tail, q k) = ∏ k ∈ s, q k := by
    exact Finset.prod_filter_mul_prod_filter_not s (fun k ↦ k + 1 < K) q
  rw [← hsplit]
  have hhead : ∏ k ∈ head, q k ≤ (1 + R ^ 2) ^ K := by
    calc
      ∏ k ∈ head, q k ≤ ∏ _k ∈ head, (1 + R ^ 2) := by
        apply Finset.prod_le_prod
        · exact fun _ _ ↦ norm_nonneg _
        · intro k hk
          exact (hq k).trans_eq (if_pos (Finset.mem_filter.1 hk).2)
      _ = (1 + R ^ 2) ^ head.card := by simp
      _ ≤ (1 + R ^ 2) ^ K := by
        apply pow_le_pow_right₀ (by nlinarith [sq_nonneg R])
        have hcard : head.card ≤ (Finset.range K).card := Finset.card_le_card (by
          intro k hk
          apply Finset.mem_range.2
          have hklt := (Finset.mem_filter.1 hk).2
          omega)
        simpa using hcard
  have htail : ∏ k ∈ tail, q k ≤ standardSquareProduct (R / C) := by
    calc
      ∏ k ∈ tail, q k ≤ ∏ k ∈ tail, e k := by
        apply Finset.prod_le_prod
        · exact fun _ _ ↦ norm_nonneg _
        · intro k hk
          exact (hq k).trans_eq (if_neg (Finset.mem_filter.1 hk).2)
      _ ≤ ∏' k : ℕ, e k := by
        obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range tail
        apply ge_of_tendsto hem.hasProd.tendsto_prod_nat
        filter_upwards [eventually_ge_atTop N] with j hj
        apply Finset.prod_le_prod_of_subset_of_one_le
        · exact hN.trans (Finset.range_mono hj)
        · intro k hk
          dsimp [e]
          positivity
        · intro k hk hktail
          dsimp [e]
          have hdiv : 0 ≤ (R / C) ^ 2 / (k + 1 : ℝ) ^ 2 := by positivity
          linarith
      _ = standardSquareProduct (R / C) := rfl
  exact mul_le_mul hhead htail (by positivity) (by positivity)

/-- The canonical product belonging to a Fabry sequence has exponential type zero.  The
estimate is uniform on every disk and is the quantitative form used by the interpolation
argument. -/
private lemma exponentCanonicalProduct_eventually_le_exp {n : ℕ → ℕ}
    (hn : HasFabryGaps n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ ζ : ℂ, ‖ζ‖ ≤ R →
      ‖exponentCanonicalProduct n ζ‖ ≤ Real.exp (ε * R) := by
  let C : ℝ := 2 * Real.pi / ε
  have hC : 0 < C := div_pos (mul_pos two_pos Real.pi_pos) hε
  obtain ⟨K, hlinear⟩ := fabry_eventually_linear hn C
  have hhead := eventually_one_add_sq_pow_le_exp K (half_pos hε)
  filter_upwards [eventually_ge_atTop C, hhead] with R hRC hheadR
  intro ζ hζ
  have hR : 0 ≤ R := hC.le.trans hRC
  have hx : 1 ≤ R / C := (le_div_iff₀ hC).2 (by simpa using hRC)
  have hstandard := standardSquareProduct_le_exp hx
  have hstandard_nonneg : 0 ≤ standardSquareProduct (R / C) := by
    apply ge_of_tendsto' (standardSquareProduct_multipliable (R / C)).hasProd.tendsto_prod_nat
    intro N
    apply Finset.prod_nonneg
    intro k hk
    positivity
  calc
    ‖exponentCanonicalProduct n ζ‖ ≤
        (1 + R ^ 2) ^ K * standardSquareProduct (R / C) :=
      exponentCanonicalProduct_norm_le_head_mul_standard hn.1 hC hR hlinear hζ
    _ ≤ Real.exp ((ε / 2) * R) * Real.exp (Real.pi * (R / C)) :=
      mul_le_mul hheadR hstandard hstandard_nonneg (by positivity)
    _ = Real.exp (ε * R) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [C]
      field_simp
      ring

/-- A nonconstant entire function eventually has maximum modulus bigger than one. -/
private lemma eventually_one_lt_maxModulus {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconst : ¬ ∃ c, f = Function.const ℂ c) {c : ℝ} {a : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * rexp (‖z‖ ^ a)) :
    ∀ᶠ r : ℝ in atTop, 1 < maxModulus r f := by
  obtain ⟨z₀, hz₀⟩ : ∃ z, 1 < ‖f z‖ := by
    by_contra h
    push_neg at h
    have hb : Bornology.IsBounded (Set.range f) := by
      rw [isBounded_iff_forall_norm_le]
      exact ⟨1, by rintro _ ⟨z, rfl⟩; exact h z⟩
    exact hconst (hf.exists_eq_const_of_bounded hb)
  filter_upwards [eventually_ge_atTop (‖z₀‖ + 1)] with r hr
  have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg z₀) (by linarith)
  obtain ⟨w, hwfront, hwmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm
    Metric.isBounded_ball ⟨0, Metric.mem_ball_self hrpos⟩ hf.diffContOnCl
  have hwsphere : w ∈ Metric.sphere (0 : ℂ) r := by
    rw [← frontier_ball 0 hrpos.ne']
    exact hwfront
  have hwnorm : ‖w‖ = r := by
    simpa [Metric.mem_sphere] using hwsphere
  have hzball : z₀ ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.mem_ball] using (show ‖z₀‖ < r by linarith)
  have hzw : ‖f z₀‖ ≤ ‖f w‖ := hwmax (subset_closure hzball)
  calc
    1 < ‖f z₀‖ := hz₀
    _ ≤ ‖f w‖ := hzw
    _ ≤ maxModulus r f :=
      le_ciSup (maxModulus_bddAbove hbound) (⟨w, hwnorm⟩ : {z : ℂ // ‖z‖ = r})

private lemma maxModulus_exp_le_growth {f : ℂ → ℂ} {c : ℝ} {A : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * Real.exp (‖z‖ ^ A)) (σ : ℝ) :
    maxModulus (Real.exp σ) f ≤ c * Real.exp ((Real.exp σ) ^ A) := by
  let := circle_nonempty (Real.exp_nonneg σ)
  rw [maxModulus]
  apply ciSup_le
  intro z
  simpa only [z.property] using hbound z

/-- Finite order becomes an affine upper bound after applying `log ∘ log` to the
maximum modulus in logarithmic radius.  This is the exact input of the frequent-point
Borel growth lemma above. -/
private lemma eventually_log_log_maxModulus_le_affine {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hconst : ¬ ∃ d, f = Function.const ℂ d)
    {c : ℝ} (hc : 0 ≤ c) {A : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * Real.exp (‖z‖ ^ A)) :
    ∀ᶠ σ : ℝ in atTop,
      Real.log (Real.log (maxModulus (Real.exp σ) f)) ≤
        (A : ℝ) * σ + Real.log (|Real.log c| + 1) := by
  have hcpos : 0 < c := by
    refine lt_of_le_of_ne hc (Ne.symm fun hc0 ↦ ?_)
    apply hconst
    refine ⟨0, funext fun z ↦ ?_⟩
    have hz : ‖f z‖ = 0 := le_antisymm (by simpa [hc0] using hbound z) (norm_nonneg _)
    exact norm_eq_zero.mp hz
  have hApos : 0 < A := by
    refine Nat.pos_of_ne_zero fun hA0 ↦ ?_
    apply hconst
    have hb : Bornology.IsBounded (Set.range f) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨c * Real.exp 1, ?_⟩
      rintro _ ⟨z, rfl⟩
      simpa [hA0] using hbound z
    exact hf.exists_eq_const_of_bounded hb
  have hmax := eventually_one_lt_maxModulus hf hconst hbound
  filter_upwards [eventually_ge_atTop 0, Real.tendsto_exp_atTop.eventually hmax]
    with σ hσ hmaxσ
  let D : ℝ := |Real.log c| + 1
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hmaxpos : 0 < maxModulus (Real.exp σ) f :=
    lt_trans zero_lt_one hmaxσ
  have hgrowth := maxModulus_exp_le_growth hbound σ
  have hrhspos : 0 < c * Real.exp ((Real.exp σ) ^ A) := by positivity
  have hloggrowth : Real.log (maxModulus (Real.exp σ) f) ≤
      Real.log c + Real.exp ((A : ℝ) * σ) := by
    calc
      Real.log (maxModulus (Real.exp σ) f) ≤
          Real.log (c * Real.exp ((Real.exp σ) ^ A)) :=
        Real.strictMonoOn_log.monotoneOn hmaxpos hrhspos hgrowth
      _ = Real.log c + (Real.exp σ) ^ A := by
        rw [Real.log_mul hcpos.ne' (Real.exp_ne_zero _), Real.log_exp]
      _ = Real.log c + Real.exp ((A : ℝ) * σ) := by
        rw [Real.exp_nat_mul]
  have hexpone : 1 ≤ Real.exp ((A : ℝ) * σ) :=
    Real.one_le_exp (mul_nonneg (by positivity) hσ)
  have habsmul : |Real.log c| ≤ |Real.log c| * Real.exp ((A : ℝ) * σ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexpone (abs_nonneg (Real.log c))
  have hlogupper : Real.log (maxModulus (Real.exp σ) f) ≤
      D * Real.exp ((A : ℝ) * σ) := by
    calc
      Real.log (maxModulus (Real.exp σ) f) ≤
          Real.log c + Real.exp ((A : ℝ) * σ) := hloggrowth
      _ ≤ |Real.log c| + Real.exp ((A : ℝ) * σ) :=
        by simpa only [add_comm] using
          add_le_add_right (le_abs_self (Real.log c)) (Real.exp ((A : ℝ) * σ))
      _ ≤ |Real.log c| * Real.exp ((A : ℝ) * σ) +
          Real.exp ((A : ℝ) * σ) := by
        simpa only [add_comm] using
          add_le_add_right habsmul (Real.exp ((A : ℝ) * σ))
      _ = D * Real.exp ((A : ℝ) * σ) := by dsimp [D]; ring
  have hlogmaxpos : 0 < Real.log (maxModulus (Real.exp σ) f) :=
    Real.log_pos hmaxσ
  calc
    Real.log (Real.log (maxModulus (Real.exp σ) f)) ≤
        Real.log (D * Real.exp ((A : ℝ) * σ)) :=
      Real.strictMonoOn_log.monotoneOn hlogmaxpos (mul_pos hDpos (Real.exp_pos _)) hlogupper
    _ = (A : ℝ) * σ + Real.log D := by
      rw [Real.log_mul hDpos.ne' (Real.exp_ne_zero _), Real.log_exp]
      ring
    _ = (A : ℝ) * σ + Real.log (|Real.log c| + 1) := rfl

/-- At arbitrarily large logarithmic radii, the logarithm of the maximum modulus grows by
at most a prescribed multiplicative factor over one fixed positive step. -/
private lemma frequently_log_maxModulus_shift_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hconst : ¬ ∃ d, f = Function.const ℂ d)
    {c : ℝ} (hc : 0 ≤ c) {A : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * Real.exp (‖z‖ ^ A))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h > 0, ∃ᶠ σ : ℝ in atTop,
      Real.log (maxModulus (Real.exp (σ + h)) f) ≤
        (1 + ε) * Real.log (maxModulus (Real.exp σ) f) := by
  have hApos : 0 < A := by
    refine Nat.pos_of_ne_zero fun hA0 ↦ ?_
    apply hconst
    have hb : Bornology.IsBounded (Set.range f) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨c * Real.exp 1, ?_⟩
      rintro _ ⟨z, rfl⟩
      simpa [hA0] using hbound z
    exact hf.exists_eq_const_of_bounded hb
  let γ : ℝ := Real.log (1 + ε)
  have hγ : 0 < γ := Real.log_pos (by linarith)
  let h : ℝ := γ / (2 * (A : ℝ))
  have hh : 0 < h := by dsimp [h]; positivity
  have hslope : (A : ℝ) * h < γ := by
    dsimp [h]
    field_simp
    linarith
  let u : ℝ → ℝ := fun σ ↦ Real.log (Real.log (maxModulus (Real.exp σ) f))
  have huaffine : ∀ᶠ σ : ℝ in atTop,
      u σ ≤ (A : ℝ) * σ + Real.log (|Real.log c| + 1) :=
    eventually_log_log_maxModulus_le_affine hf hconst hc hbound
  have hselect : ∃ᶠ σ : ℝ in atTop, u (σ + h) ≤ u σ + γ :=
    frequently_increment_le_of_eventually_le_affine u hh hslope huaffine
  have hmaxR := eventually_one_lt_maxModulus hf hconst hbound
  have hmaxσ : ∀ᶠ σ : ℝ in atTop, 1 < maxModulus (Real.exp σ) f :=
    Real.tendsto_exp_atTop.eventually hmaxR
  have hmaxshift : ∀ᶠ σ : ℝ in atTop, 1 < maxModulus (Real.exp (σ + h)) f :=
    (tendsto_atTop_add_const_right atTop h tendsto_id).eventually hmaxσ
  refine ⟨h, hh, (hselect.and_eventually (hmaxσ.and hmaxshift)).mono ?_⟩
  rintro σ ⟨hinc, hM, hMshift⟩
  have hexp := Real.exp_le_exp.mpr hinc
  dsimp [u] at hexp
  rw [Real.exp_log (Real.log_pos hMshift),
    Real.exp_add (Real.log (Real.log (maxModulus (Real.exp σ) f))) γ,
    Real.exp_log (Real.log_pos hM)] at hexp
  have hγexp : Real.exp γ = 1 + ε := by
    dsimp [γ]
    rw [Real.exp_log]
    linarith
  simpa only [hγexp, mul_comm] using hexp

/-- Arbitrary-step version of the preceding Borel selection lemma.  Its
multiplicative loss is explicit, which lets the final proof choose the disk
scale first and then balance the common-shift loss. -/
private lemma frequently_log_maxModulus_shift_le_exp {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hconst : ¬ ∃ d, f = Function.const ℂ d)
    {c : ℝ} (hc : 0 ≤ c) {A : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * Real.exp (‖z‖ ^ A))
    {h : ℝ} (hh : 0 < h) :
    ∃ᶠ σ : ℝ in atTop,
      Real.log (maxModulus (Real.exp (σ + h)) f) ≤
        Real.exp (2 * (A : ℝ) * h) *
          Real.log (maxModulus (Real.exp σ) f) := by
  have hApos : 0 < A := by
    refine Nat.pos_of_ne_zero fun hA0 ↦ ?_
    apply hconst
    have hb : Bornology.IsBounded (Set.range f) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨c * Real.exp 1, ?_⟩
      rintro _ ⟨z, rfl⟩
      simpa [hA0] using hbound z
    exact hf.exists_eq_const_of_bounded hb
  let γ : ℝ := 2 * (A : ℝ) * h
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hslope : (A : ℝ) * h < γ := by dsimp [γ]; nlinarith
  let u : ℝ → ℝ := fun σ ↦ Real.log (Real.log (maxModulus (Real.exp σ) f))
  have huaffine : ∀ᶠ σ : ℝ in atTop,
      u σ ≤ (A : ℝ) * σ + Real.log (|Real.log c| + 1) :=
    eventually_log_log_maxModulus_le_affine hf hconst hc hbound
  have hselect : ∃ᶠ σ : ℝ in atTop, u (σ + h) ≤ u σ + γ :=
    frequently_increment_le_of_eventually_le_affine u hh hslope huaffine
  have hmaxR := eventually_one_lt_maxModulus hf hconst hbound
  have hmaxσ : ∀ᶠ σ : ℝ in atTop, 1 < maxModulus (Real.exp σ) f :=
    Real.tendsto_exp_atTop.eventually hmaxR
  have hmaxshift : ∀ᶠ σ : ℝ in atTop, 1 < maxModulus (Real.exp (σ + h)) f :=
    (tendsto_atTop_add_const_right atTop h tendsto_id).eventually hmaxσ
  exact (hselect.and_eventually (hmaxσ.and hmaxshift)).mono fun σ hσ ↦ by
    rcases hσ with ⟨hinc, hM, hMshift⟩
    have hexp := Real.exp_le_exp.mpr hinc
    dsimp [u] at hexp
    rw [Real.exp_log (Real.log_pos hMshift),
      Real.exp_add (Real.log (Real.log (maxModulus (Real.exp σ) f))) γ,
      Real.exp_log (Real.log_pos hM)] at hexp
    simpa only [γ, mul_comm] using hexp

/-! ### Assembly of the finite-frequency and disk estimates -/

private lemma localization_tail_norm_le_half {E B q L G r x : ℝ}
    (hG : 0 < G) (_hB0 : 0 ≤ B) (hE : E ≤ B * Real.exp x * G)
    (hB : B ≤ Real.exp (q * L)) (hx : Real.exp x ≤ Real.exp (-(q + 4) * L))
    (hlogG : Real.log (2 * G) ≤ (5 - r / 2) * L) :
    E ≤ (1 / 2 : ℝ) * Real.exp ((1 - r / 2) * L) := by
  have hprod : B * Real.exp x ≤
      Real.exp (q * L) * Real.exp (-(q + 4) * L) :=
    mul_le_mul hB hx (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hcoarse : E ≤ Real.exp (-4 * L) * G := by
    calc
      E ≤ B * Real.exp x * G := hE
      _ ≤ (Real.exp (q * L) * Real.exp (-(q + 4) * L)) * G :=
        mul_le_mul_of_nonneg_right hprod hG.le
      _ = Real.exp (-4 * L) * G := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
  have htwoG : 2 * G ≤ Real.exp ((5 - r / 2) * L) := by
    calc
      2 * G = Real.exp (Real.log (2 * G)) :=
        (Real.exp_log (mul_pos (by norm_num) hG)).symm
      _ ≤ Real.exp ((5 - r / 2) * L) := Real.exp_le_exp.mpr hlogG
  calc
    E ≤ Real.exp (-4 * L) * G := hcoarse
    _ = (Real.exp (-4 * L) * (2 * G)) / 2 := by ring
    _ ≤ (Real.exp (-4 * L) * Real.exp ((5 - r / 2) * L)) / 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htwoG (Real.exp_nonneg _)) (by norm_num)
    _ = (1 / 2 : ℝ) * Real.exp ((1 - r / 2) * L) := by
      rw [← Real.exp_add]
      ring_nf

private lemma log_norm_center_of_head_tail {H F : ℂ} {r L : ℝ}
    (hHpos : 0 < ‖H‖)
    (hHlog : (1 - r / 2) * L ≤ Real.log ‖H‖)
    (htail : ‖F - H‖ ≤ (1 / 2 : ℝ) * Real.exp ((1 - r / 2) * L))
    (hlog2 : Real.log 2 ≤ r * L / 2) :
    (1 - r) * L ≤ Real.log ‖F‖ := by
  have hHexp : Real.exp ((1 - r / 2) * L) ≤ ‖H‖ := by
    calc
      Real.exp ((1 - r / 2) * L) ≤ Real.exp (Real.log ‖H‖) :=
        Real.exp_le_exp.mpr hHlog
      _ = ‖H‖ := Real.exp_log hHpos
  have htriangle : ‖H‖ ≤ ‖F‖ + ‖F - H‖ := by
    calc
      ‖H‖ = ‖F - (F - H)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  have hFnorm : (1 / 2 : ℝ) * Real.exp ((1 - r / 2) * L) ≤ ‖F‖ := by
    linarith
  have hFpos : 0 < ‖F‖ :=
    (mul_pos (by norm_num) (Real.exp_pos _)).trans_le hFnorm
  have hlog := Real.strictMonoOn_log.monotoneOn
    (mul_pos (by norm_num) (Real.exp_pos _)) hFpos hFnorm
  rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hloghalf] at hlog
  linarith

private lemma head_log_lower_of_turan {μ H P G r L : ℝ}
    (hμ : 0 < μ) (hH : 0 < H) (hP : 0 < P)
    (hlarge : μ ≤ H * P) (hμlog : L - Real.log G ≤ Real.log μ)
    (hGlog : Real.log G ≤ r * L / 4)
    (hPlog : Real.log P ≤ r * L / 4) :
    (1 - r / 2) * L ≤ Real.log H := by
  have hlogLarge := Real.strictMonoOn_log.monotoneOn hμ
    (mul_pos hH hP) hlarge
  rw [Real.log_mul hH.ne' hP.ne'] at hlogLarge
  linarith

private lemma cutoff_exp_decay {N : ℕ} {D q L h d : ℝ}
    (hhd : 0 < h - d) (hD : D = (4 * q + 16) / (h - d))
    (hN : D * L ≤ (N : ℝ)) :
    Real.exp (-(N : ℝ) * ((h - d) / 2) / 2) ≤
      Real.exp (-(q + 4) * L) := by
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hN hhd.le
  have hDcancel : D * L * (h - d) = (4 * q + 16) * L := by
    rw [hD]
    field_simp
  have hmul' : (4 * q + 16) * L ≤ (N : ℝ) * (h - d) := by
    rw [← hDcancel]
    exact hmul
  calc
    -(N : ℝ) * ((h - d) / 2) / 2 =
        (-((N : ℝ) * (h - d))) * (1 / 4 : ℝ) := by ring
    _ ≤ (-((4 * q + 16) * L)) * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (neg_le_neg hmul') (by norm_num)
    _ = -(q + 4) * L := by ring

private lemma family_center_log_lower {κ : Type*} (F H : κ → ℂ) (P : κ → ℝ)
    {μ G Gtail B q L r x : ℝ}
    (hμ : 0 < μ) (hμlog : L - Real.log G ≤ Real.log μ)
    (hGlog : Real.log G ≤ r * L / 4)
    (hPpos : ∀ i, 0 < P i) (hlarge : ∀ i, μ ≤ ‖H i‖ * P i)
    (hPlog : ∀ i, Real.log (P i) ≤ r * L / 4)
    (hGtail : 0 < Gtail) (hB0 : 0 ≤ B)
    (htail : ∀ i, ‖F i - H i‖ ≤ B * Real.exp x * Gtail)
    (hB : B ≤ Real.exp (q * L))
    (hx : Real.exp x ≤ Real.exp (-(q + 4) * L))
    (hlogGtail : Real.log (2 * Gtail) ≤ (5 - r / 2) * L)
    (hlog2 : Real.log 2 ≤ r * L / 2) :
    ∀ i, (1 - r) * L ≤ Real.log ‖F i‖ := by
  intro i
  have hHpos : 0 < ‖H i‖ := by
    by_contra hnpos
    have hzero : ‖H i‖ = 0 := le_antisymm (le_of_not_gt hnpos) (norm_nonneg _)
    have hli := hlarge i
    rw [hzero, zero_mul] at hli
    exact (not_lt_of_ge hli) hμ
  have hHlog := head_log_lower_of_turan hμ hHpos (hPpos i)
    (hlarge i) hμlog hGlog (hPlog i)
  have htailHalf := localization_tail_norm_le_half hGtail hB0 (htail i)
    hB hx hlogGtail
  exact log_norm_center_of_head_tail hHpos hHlog htailHalf hlog2

/-- The finite head, Turán localization, and exponentially small tail produce
a complete family of phase centers with a uniform logarithmic lower bound. -/
private lemma exists_phase_centers_with_log_lower {f : ℂ → ℂ} {n : ℕ → ℕ}
    (hn : HasFabryGaps n) {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    (hfdiff : Differentiable ℂ f) {c : ℝ} {A : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * Real.exp (‖z‖ ^ A))
    {σ L B q D T η G Gtail r h d : ℝ} (K₀ : ℕ)
    (hLdef : L = Real.log (maxModulus (Real.exp σ) f))
    (hBdef : B = maxModulus (Real.exp (σ + h)) f)
    (hDdef : D = (4 * q + 16) / (h - d))
    (hTdef : T = 64 * Real.pi / d + 10)
    (hηdef : η = r / (16 * T * D))
    (hGdef : G = geometricExpSum d)
    (hGtdef : Gtail = ∑' k : ℕ, Real.exp (-(k : ℝ) * ((h - d) / 2) / 2))
    (hindex : ∀ k ≥ K₀, (k : ℝ) ≤ η * (n k : ℝ))
    (hr : 0 < r) (hr1 : r < 1) (hd : 0 < d) (hhd : 0 < h - d)
    (hqpos : 0 < q)
    (hMbase : 1 < maxModulus (Real.exp σ) f) (hBpos : 0 < B)
    (hLpos : 0 < L) (hBlog : Real.log B ≤ q * L)
    (hGlog : Real.log G ≤ r * L / 4)
    (hTconst : T * ((K₀ : ℝ) + η + 2) ≤ 3 * r * L / 16)
    (hGtpos : 0 < Gtail)
    (hGtlog : Real.log (2 * Gtail) ≤ (5 - r / 2) * L)
    (hlog2 : Real.log 2 ≤ r * L / 2) :
    ∃ phaseCenter : {q : ℕ // q ∈ phaseGrid d} → ℝ,
      (∀ t : ℝ, ∃ q : {q : ℕ // q ∈ phaseGrid d}, ∃ u : ℝ,
        Complex.exp ((u : ℂ) * Complex.I) =
          Complex.exp ((t : ℂ) * Complex.I) ∧
        |(u + 2 * Real.pi) - phaseCenter q| < 9 * d / 16) ∧
      ∀ q : {q : ℕ // q ∈ phaseGrid d},
        (1 - r) * L ≤ Real.log ‖logLift f
          (((σ + d : ℝ) : ℂ) + (phaseCenter q : ℂ) * Complex.I)‖ := by
  classical
  have hGpos : 0 < G := by rw [hGdef]; exact geometricExpSum_pos hd
  obtain ⟨j, hjmax⟩ := exists_term_eq_maximalTerm ha hfn (σ + d)
  let μ : ℝ := ‖a j‖ * Real.exp ((n j : ℝ) * (σ + d))
  have hμeq : μ = maximalTerm a n (σ + d) := by simpa [μ] using hjmax
  have hμpos : 0 < μ := by
    dsimp [μ]
    exact mul_pos (norm_pos_iff.mpr (ha j)) (Real.exp_pos _)
  have hlogμ : L - Real.log G ≤ Real.log μ := by
    rw [hLdef, hGdef]
    simpa only [hμeq] using log_maximalTerm_shift_lower hn.1 hfn hd hMbase
  have htermOuter : μ * Real.exp ((n j : ℝ) * (h - d)) ≤ B := by
    have hjterm := gapTerm_le_maxModulus hn.1 hfn hfdiff hbound
      (Real.exp_pos (σ + h)) j
    have heq : ‖a j‖ * (Real.exp (σ + h)) ^ n j =
        μ * Real.exp ((n j : ℝ) * (h - d)) := by
      dsimp [μ]
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    rw [hBdef]
    simpa only [heq] using hjterm
  have hnBound : (n j : ℝ) * (h - d) ≤ (q - 1) * L + Real.log G := by
    have hprodpos : 0 < μ * Real.exp ((n j : ℝ) * (h - d)) := by positivity
    have hlogterm := Real.strictMonoOn_log.monotoneOn hprodpos hBpos htermOuter
    rw [Real.log_mul hμpos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlogterm
    linarith
  have hnjD : (n j : ℝ) < D * L := by
    have hnSimple : (n j : ℝ) * (h - d) ≤ q * L := by
      have hrL : r * L ≤ L := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1.le hLpos.le
      linarith
    have hqD : q < 4 * q + 16 := by linarith
    rw [hDdef, show ((4 * q + 16) / (h - d)) * L =
      (4 * q + 16) * L / (h - d) by ring]
    apply (lt_div_iff₀ hhd).2
    exact hnSimple.trans_lt (mul_lt_mul_of_pos_right hqD hLpos)
  let N : ℕ := Nat.ceil (D * L)
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hNnonneg : 0 ≤ D * L := by
    positivity
  have hjN : n j < N := Nat.lt_ceil.2 hnjD
  let s : Finset ℕ := gapHead n N
  have hjs : j ∈ s := (mem_gapHead_iff hn.1).2 hjN
  have hsne : s.Nonempty := ⟨j, hjs⟩
  have hNupper : (N : ℝ) < D * L + 1 := by
    simpa [N] using Nat.ceil_lt_add_one hNnonneg
  have hcardRaw := gapHead_card_le_add hn.1 hηpos hindex N
  have hcardBound : ((s.card : ℕ) : ℝ) + 1 ≤
      η * D * L + ((K₀ : ℝ) + η + 2) := by
    have hcast : ((s.card : ℕ) : ℝ) ≤
        (K₀ : ℝ) + η * (N : ℝ) + 1 := by simpa [s] using hcardRaw
    have hηN : η * (N : ℝ) ≤ η * (D * L + 1) :=
      mul_le_mul_of_nonneg_left hNupper.le hηpos.le
    nlinarith
  have hfactorBudget : T * ((s.card : ℕ) + 1 : ℝ) ≤ r * L / 4 := by
    have hηidentity : T * (η * D * L) = r * L / 16 := by
      rw [hηdef]
      field_simp [hTpos.ne', hDpos.ne']
    calc
      T * ((s.card : ℕ) + 1 : ℝ) ≤
          T * (η * D * L + ((K₀ : ℝ) + η + 2)) :=
        mul_le_mul_of_nonneg_left hcardBound hTpos.le
      _ = r * L / 16 + T * ((K₀ : ℝ) + η + 2) := by
        rw [mul_add, hηidentity]
      _ ≤ r * L / 16 + 3 * r * L / 16 := add_le_add_right hTconst _
      _ = r * L / 4 := by ring
  obtain ⟨phaseCenter, phaseM, phaseν, hphase, hcover⟩ :=
    exists_turan_phase_cover hn.1 a hjs (σ := σ + d) (d := d) hd
  let κ := {q : ℕ // q ∈ phaseGrid d}
  let center : κ → ℂ := fun q =>
    ((σ + d : ℝ) : ℂ) + (phaseCenter q : ℂ) * Complex.I
  have hheadFormula : ∀ q : κ,
      (∑ k ∈ s, (a k * Complex.exp ((n k : ℂ) * ((σ + d : ℝ) : ℂ))) *
          Complex.exp ((n k : ℂ) * ((phaseCenter q : ℂ) * Complex.I))) =
        ∑ k ∈ s, a k * Complex.exp ((n k : ℂ) * center q) := by
    intro q
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [center]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    ring_nf
  let H : κ → ℂ := fun q =>
    ∑ k ∈ s, a k * Complex.exp ((n k : ℂ) * center q)
  let P : κ → ℝ := fun q => turanFactor s.card (phaseM q)
  let Fc : κ → ℂ := fun q => logLift f (center q)
  have hKpos : 0 < s.card := Finset.card_pos.mpr hsne
  have hPpos : ∀ q : κ, 0 < P q := by
    intro q
    dsimp [P, turanFactor]
    positivity
  have hPlog : ∀ q : κ, Real.log (P q) ≤ r * L / 4 := by
    intro q
    have hMcast : (phaseM q : ℝ) ≤ 64 * Real.pi * (s.card : ℝ) / d + 1 := by
      have hMq := (hphase q).1
      have hcast : (phaseM q : ℝ) ≤
          (Nat.ceil (64 * Real.pi * (s.card : ℝ) / d) : ℕ) := by
        exact_mod_cast hMq
      have hx0 : 0 ≤ 64 * Real.pi * (s.card : ℝ) / d := by positivity
      exact hcast.trans (Nat.ceil_lt_add_one hx0).le
    exact (log_turanFactor_le hKpos hd hMcast).trans
      (by simpa only [hTdef] using hfactorBudget)
  have hphaseLarge : ∀ q : κ, μ ≤ ‖H q‖ * P q := by
    intro q
    have hq := (hphase q).2.2.2.2
    rw [hheadFormula q] at hq
    simpa [μ, H, P] using hq
  have htailAll : ∀ q : κ,
      ‖Fc q - H q‖ ≤ B * Real.exp (-(N : ℝ) * ((h - d) / 2) / 2) * Gtail := by
    intro q
    have ht := logLift_sub_gapHead_norm_le hn.1 hfn hfdiff hbound
      (τ := σ + h) (d := (h - d) / 2) (by positivity) N (center q) (by
        dsimp [center]
        simp only [Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
        linarith)
    rw [hBdef, hGtdef]
    simpa only [Fc, H, s] using ht
  have hNlower : D * L ≤ (N : ℝ) := Nat.le_ceil _
  have hBexp : B ≤ Real.exp (q * L) := by
    calc
      B = Real.exp (Real.log B) := (Real.exp_log hBpos).symm
      _ ≤ Real.exp (q * L) := Real.exp_le_exp.mpr hBlog
  have hdecay := cutoff_exp_decay hhd hDdef hNlower
  have hcenterLog : ∀ q : κ, (1 - r) * L ≤ Real.log ‖Fc q‖ :=
    family_center_log_lower Fc H P hμpos hlogμ hGlog hPpos hphaseLarge hPlog
      hGtpos hBpos.le htailAll hBexp hdecay hGtlog hlog2
  refine ⟨phaseCenter, hcover, ?_⟩
  intro q
  simpa only [Fc, center] using hcenterLog q

/-- The error generated by the final one-parameter choice of localization
scales vanishes.  The exponential increment is bounded by its argument near
zero, while a linear factor is dominated by `exp (x / 4)`. -/
private lemma tendsto_scale_weighted_gap (A : ℕ) :
    Tendsto (fun x : ℝ => x *
      ((Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) - 1) + Real.exp (-x / 4)))
      atTop (𝓝 0) := by
  have hH : Tendsto (fun x : ℝ => Real.exp (-x / 4)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℝ) < 1 / 4))
    exact h.congr' (by
      filter_upwards with x
      simp only [Function.comp_apply, id_eq]
      congr 1
      ring)
  have hxH : Tendsto (fun x : ℝ => x * Real.exp (-x / 4)) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 : ℝ) (1 / 4 : ℝ) (by norm_num)
    exact h.congr' (by
      filter_upwards with x
      simp only [Real.rpow_one]
      congr 1
      ring_nf)
  have harg : Tendsto (fun x : ℝ => 2 * (A : ℝ) * Real.exp (-x / 4))
      atTop (𝓝 0) := by
    simpa using hH.const_mul (2 * (A : ℝ))
  have hargSmall : ∀ᶠ x : ℝ in atTop,
      |2 * (A : ℝ) * Real.exp (-x / 4)| ≤ 1 :=
    by
      have habs : Tendsto
          (fun x : ℝ => |2 * (A : ℝ) * Real.exp (-x / 4)|) atTop (𝓝 0) := by
        simpa using harg.abs
      exact habs.eventually_le_const (by norm_num)
  have hnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ x *
      ((Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) - 1) +
        Real.exp (-x / 4)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hargNonneg : 0 ≤ 2 * (A : ℝ) * Real.exp (-x / 4) := by positivity
    have hexpOne : 1 ≤ Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) :=
      Real.one_le_exp hargNonneg
    positivity
  have hupper : ∀ᶠ x : ℝ in atTop, x *
      ((Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) - 1) +
        Real.exp (-x / 4)) ≤
      (4 * (A : ℝ) + 1) * (x * Real.exp (-x / 4)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), hargSmall] with x hx hsmall
    have hargNonneg : 0 ≤ 2 * (A : ℝ) * Real.exp (-x / 4) := by positivity
    have hexpNonneg : 0 ≤
        Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp hargNonneg)
    have hinc := Real.abs_exp_sub_one_le hsmall
    rw [abs_of_nonneg hexpNonneg, abs_of_nonneg hargNonneg] at hinc
    have hsum :
        (Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) - 1) +
            Real.exp (-x / 4) ≤
          (4 * (A : ℝ) + 1) * Real.exp (-x / 4) := by
      linarith
    calc
      x * ((Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) - 1) +
          Real.exp (-x / 4)) ≤
          x * ((4 * (A : ℝ) + 1) * Real.exp (-x / 4)) :=
        mul_le_mul_of_nonneg_left hsum hx
      _ = (4 * (A : ℝ) + 1) * (x * Real.exp (-x / 4)) := by ring
  exact squeeze_zero' hnonneg hupper (by
    simpa using hxH.const_mul (4 * (A : ℝ) + 1))

/-- For every target coefficient below one, the asymptotic scale used in the
localization proof eventually satisfies all of its numerical side conditions. -/
private lemma exists_admissible_scale (A : ℕ) {y₀ : ℝ} (hy₀one : y₀ < 1) :
    ∃ r h d β : ℝ,
      0 < r ∧ r < 1 ∧ 0 < h ∧ 0 < d ∧ 4 * d < h ∧ 0 ≤ β ∧
      Real.exp (2 * (A : ℝ) * h) < 2 ∧
      16 * ((Nat.ceil (4 * Real.pi / d) + 1 : ℕ) : ℝ) < Real.exp (β / 2) ∧
      y₀ * Real.exp (2 * (A : ℝ) * h) <
        (1 - r) - 2 * (Real.exp (2 * (A : ℝ) * h) - (1 - r)) -
          β * ((Real.exp (2 * (A : ℝ) * h) - (1 - r)) /
            Real.log (6 / 5)) := by
  have hH : Tendsto (fun x : ℝ => Real.exp (-x / 4)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℝ) < 1 / 4))
    exact h.congr' (by
      filter_upwards with x
      simp only [Function.comp_apply, id_eq]
      congr 1
      ring)
  have harg : Tendsto (fun x : ℝ => 2 * (A : ℝ) * Real.exp (-x / 4))
      atTop (𝓝 0) := by
    simpa using hH.const_mul (2 * (A : ℝ))
  have hQ : Tendsto
      (fun x : ℝ => Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)))
      atTop (𝓝 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp harg
    simpa only [Function.comp_def, Real.exp_zero] using h
  have hgap : Tendsto (fun x : ℝ =>
      (Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) - 1) +
        Real.exp (-x / 4)) atTop (𝓝 0) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using (hQ.sub hone).add hH
  have hweighted := tendsto_scale_weighted_gap A
  have hlog65 : Real.log (6 / 5) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 6 / 5)).ne'
  have hweightedDiv : Tendsto (fun x : ℝ =>
      x * (((Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) - 1) +
        Real.exp (-x / 4)) / Real.log (6 / 5))) atTop (𝓝 0) := by
    have h := hweighted.div_const (Real.log (6 / 5))
    simpa only [zero_div, mul_div_assoc] using h
  have hcoeffLimit : Tendsto (fun x : ℝ =>
      (1 - Real.exp (-x / 4)) -
        2 * ((Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) - 1) +
          Real.exp (-x / 4)) -
        x * (((Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) - 1) +
          Real.exp (-x / 4)) / Real.log (6 / 5)) -
        y₀ * Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)))
      atTop (𝓝 (1 - y₀)) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hbase := (hone.sub hH).sub (hgap.const_mul 2)
    have hall := (hbase.sub hweightedDiv).sub (hQ.const_mul y₀)
    simpa using hall
  have hcoeff : ∀ᶠ x : ℝ in atTop,
      y₀ * Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) <
        (1 - Real.exp (-x / 4)) -
          2 * (Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) -
            (1 - Real.exp (-x / 4))) -
          x * ((Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) -
            (1 - Real.exp (-x / 4))) / Real.log (6 / 5)) := by
    have hpos := Filter.Tendsto.eventually_const_lt (sub_pos.mpr hy₀one) hcoeffLimit
    filter_upwards [hpos] with x hx
    rw [show Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) -
        (1 - Real.exp (-x / 4)) =
      (Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) - 1) +
        Real.exp (-x / 4) by ring]
    linarith
  have hq2 : ∀ᶠ x : ℝ in atTop,
      Real.exp (2 * (A : ℝ) * Real.exp (-x / 4)) < 2 :=
    hQ.eventually_lt_const one_lt_two
  have hEtop : Tendsto (fun x : ℝ => Real.exp (x / 4)) atTop atTop := by
    have h := Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℝ) < 1 / 4))
    exact h.congr' (by
      filter_upwards with x
      simp only [Function.comp_apply, id_eq]
      congr 1
      ring)
  have hgrid : ∀ᶠ x : ℝ in atTop,
      16 * ((Nat.ceil (4 * Real.pi / (Real.exp (-x / 4) / 8)) + 1 : ℕ) : ℝ) <
        Real.exp (x / 2) := by
    have hlargeE : ∀ᶠ x : ℝ in atTop,
        512 * Real.pi + 32 < Real.exp (x / 4) :=
      hEtop.eventually (eventually_gt_atTop (512 * Real.pi + 32))
    filter_upwards [hlargeE] with x hx
    have hEpos : 0 < Real.exp (x / 4) := Real.exp_pos _
    have hEone : 1 < Real.exp (x / 4) := by
      have hpi : 3 < Real.pi := Real.pi_gt_three
      linarith
    have hform : 4 * Real.pi / (Real.exp (-x / 4) / 8) =
        32 * Real.pi * Real.exp (x / 4) := by
      rw [show -x / 4 = -(x / 4) by ring, Real.exp_neg]
      field_simp
      <;> ring
    have hformNonneg : 0 ≤ 4 * Real.pi / (Real.exp (-x / 4) / 8) := by positivity
    have hceil := Nat.ceil_lt_add_one hformNonneg
    have hceilBound :
        (((Nat.ceil (4 * Real.pi / (Real.exp (-x / 4) / 8)) + 1 : ℕ) : ℝ)) <
          32 * Real.pi * Real.exp (x / 4) + 2 := by
      rw [hform] at hceil ⊢
      simp only [Nat.cast_add, Nat.cast_one]
      linarith
    calc
      16 * ((Nat.ceil (4 * Real.pi / (Real.exp (-x / 4) / 8)) + 1 : ℕ) : ℝ) <
          16 * (32 * Real.pi * Real.exp (x / 4) + 2) :=
        mul_lt_mul_of_pos_left hceilBound (by norm_num)
      _ ≤ (512 * Real.pi + 32) * Real.exp (x / 4) := by
        nlinarith
      _ < Real.exp (x / 4) * Real.exp (x / 4) :=
        mul_lt_mul_of_pos_right hx hEpos
      _ = Real.exp (x / 2) := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨x, hxpos, hxq2, hxgrid, hxcoeff⟩ :=
    (eventually_gt_atTop (0 : ℝ) |>.and (hq2.and (hgrid.and hcoeff))).exists
  refine ⟨Real.exp (-x / 4), Real.exp (-x / 4), Real.exp (-x / 4) / 8, x,
    Real.exp_pos _, ?_, Real.exp_pos _, by positivity, ?_, hxpos.le, hxq2, hxgrid, hxcoeff⟩
  · rw [Real.exp_lt_one_iff]
    nlinarith
  · have := Real.exp_pos (-x / 4)
    nlinarith

/-- At any fixed scale satisfying the displayed numerical inequalities, the
finite-frequency localization and the simultaneous disk estimate produce
arbitrarily large good vertical lines.  Keeping this lemma parameterized
separates the analytic argument from the elementary final choice of scale. -/
private lemma frequently_verticalRatio_gt_of_scale {f : ℂ → ℂ} {n : ℕ → ℕ}
    (hn : HasFabryGaps n) {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    (hfdiff : Differentiable ℂ f) {c : ℝ} (hc : 0 ≤ c) {A : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ c * Real.exp (‖z‖ ^ A))
    (hconst : ¬ ∃ e, f = Function.const ℂ e)
    {y y₀ r h d β : ℝ} (hyy₀ : y < y₀) (hy₀ : 0 < y₀)
    (hr : 0 < r) (hr1 : r < 1) (hh : 0 < h) (hd : 0 < d)
    (hdh : 4 * d < h) (hβ : 0 ≤ β)
    (hq2 : Real.exp (2 * (A : ℝ) * h) < 2)
    (hgrid : 16 * ((Nat.ceil (4 * Real.pi / d) + 1 : ℕ) : ℝ) <
      Real.exp (β / 2))
    (hcoeff : y₀ * Real.exp (2 * (A : ℝ) * h) <
      (1 - r) -
        2 * (Real.exp (2 * (A : ℝ) * h) - (1 - r)) -
        β * ((Real.exp (2 * (A : ℝ) * h) - (1 - r)) /
          Real.log (6 / 5))) :
    ∃ᶠ σ' : ℝ in atTop, y < verticalRatio (logLift f) σ' := by
  classical
  let q : ℝ := Real.exp (2 * (A : ℝ) * h)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hh.le)
  have hhd : 0 < h - d := by linarith
  let D : ℝ := (4 * q + 16) / (h - d)
  have hD : 0 < D := by dsimp [D]; positivity
  let T : ℝ := 64 * Real.pi / d + 10
  have hT : 0 < T := by dsimp [T]; positivity
  let η : ℝ := r / (16 * T * D)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K₀, hindex⟩ := eventually_atTop.1 (fabry_eventually_index_le hn hη)
  let G : ℝ := geometricExpSum d
  let Gtail : ℝ := ∑' k : ℕ, Real.exp (-(k : ℝ) * ((h - d) / 2) / 2)
  have hG : 0 < G := geometricExpSum_pos hd
  have hGtail : 0 < Gtail := by
    have hpos := geometricExpSum_pos (show 0 < (h - d) / 4 by linarith)
    have heq : Gtail = geometricExpSum ((h - d) / 4) := by
      dsimp [Gtail, geometricExpSum]
      congr 1
      funext k
      congr 1
      ring
    rwa [heq]
  let margin : ℝ :=
    (1 - r) - 2 * (q - (1 - r)) -
      β * ((q - (1 - r)) / Real.log (6 / 5)) - y₀ * q
  have hmargin : 0 < margin := by
    dsimp [margin, q]
    linarith
  have hL := tendsto_log_maxModulus_exp_atTop hn.1 ha hfn hfdiff hbound
  have hselect := frequently_log_maxModulus_shift_le_exp hfdiff hconst hc hbound hh
  have hmaxBase : ∀ᶠ σ : ℝ in atTop, 1 < maxModulus (Real.exp σ) f :=
    Real.tendsto_exp_atTop.eventually
      (eventually_one_lt_maxModulus hfdiff hconst hbound)
  have hmaxOuter : ∀ᶠ σ : ℝ in atTop,
      1 < maxModulus (Real.exp (σ + h)) f :=
    (tendsto_atTop_add_const_right atTop h tendsto_id).eventually hmaxBase
  have hlarge : ∀ᶠ σ : ℝ in atTop,
      let L := Real.log (maxModulus (Real.exp σ) f)
      1 ≤ L ∧ Real.log G ≤ r * L / 4 ∧
        T * ((K₀ : ℝ) + η + 2) ≤ 3 * r * L / 16 ∧
        Real.log (2 * Gtail) ≤ (5 - r / 2) * L ∧
        Real.log 2 ≤ r * L / 2 ∧
        2 ≤ margin * L := by
    filter_upwards [hL.eventually_ge_atTop 1,
      hL.eventually_ge_atTop (4 * Real.log G / r),
      hL.eventually_ge_atTop (16 * T * ((K₀ : ℝ) + η + 2) / (3 * r)),
      hL.eventually_ge_atTop (Real.log (2 * Gtail) / (5 - r / 2)),
      hL.eventually_ge_atTop (2 * Real.log 2 / r),
      hL.eventually_ge_atTop (2 / margin)] with σ hL1 hLG hLT hLtail hLtwo hLmargin
    dsimp only
    refine ⟨hL1, ?_, ?_, ?_, ?_, ?_⟩
    · have := (div_le_iff₀ hr).1 hLG
      nlinarith
    · have := (div_le_iff₀ (by positivity : 0 < 3 * r)).1 hLT
      nlinarith
    · have hcoefTail : 0 < 5 - r / 2 := by linarith
      simpa [mul_comm] using (div_le_iff₀ hcoefTail).1 hLtail
    · have := (div_le_iff₀ hr).1 hLtwo
      nlinarith
    · simpa [mul_comm] using (div_le_iff₀ hmargin).1 hLmargin
  have hgoodBase := hselect.and_eventually (hmaxBase.and (hmaxOuter.and hlarge))
  rw [frequently_atTop] at hgoodBase ⊢
  intro X
  obtain ⟨σ, hσX, hshift, hMbase, hMouter, hlargeσ⟩ :=
    hgoodBase X
  let L : ℝ := Real.log (maxModulus (Real.exp σ) f)
  let B : ℝ := maxModulus (Real.exp (σ + h)) f
  rcases hlargeσ with ⟨hL1, hLG, hLTconst, hLtail, hLtwo, hLmargin⟩
  change 1 ≤ L at hL1
  change Real.log G ≤ r * L / 4 at hLG
  change T * ((K₀ : ℝ) + η + 2) ≤ 3 * r * L / 16 at hLTconst
  change Real.log (2 * Gtail) ≤ (5 - r / 2) * L at hLtail
  change Real.log 2 ≤ r * L / 2 at hLtwo
  change 2 ≤ margin * L at hLmargin
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  have hBlog : Real.log B ≤ q * L := by
    simpa only [B, L, q] using hshift
  have hBpos : 0 < B := lt_trans zero_lt_one hMouter
  obtain ⟨phaseCenter, hcover, hcenterLogRaw⟩ :=
    exists_phase_centers_with_log_lower hn ha hfn hfdiff hbound K₀
      (L := L) (B := B) (q := q) (D := D) (T := T) (η := η)
      (G := G) (Gtail := Gtail) (r := r) (σ := σ) (h := h) (d := d)
      rfl rfl rfl rfl rfl rfl rfl hindex hr hr1 hd hhd hqpos hMbase hBpos hLpos hBlog
      hLG hLTconst hGtail hLtail hLtwo
  let κ := {q : ℕ // q ∈ phaseGrid d}
  let center : κ → ℂ := fun q =>
    ((σ + d : ℝ) : ℂ) + (phaseCenter q : ℂ) * Complex.I
  have hcenterLog : ∀ q : κ,
      (1 - r) * L ≤ Real.log ‖logLift f (center q)‖ := by
    intro q
    simpa only [center] using hcenterLogRaw q
  /- The inlined construction below is the proof extracted into
  `exists_phase_centers_with_log_lower`; it is retained as a nearby derivation note. 
  obtain ⟨j, hjmax⟩ := exists_term_eq_maximalTerm ha hfn (σ + d)
  let μ : ℝ := ‖a j‖ * Real.exp ((n j : ℝ) * (σ + d))
  have hμeq : μ = maximalTerm a n (σ + d) := by simpa [μ] using hjmax
  have hμpos : 0 < μ := by
    dsimp [μ]
    exact mul_pos (norm_pos_iff.mpr (ha j)) (Real.exp_pos _)
  have hlogμ : L - Real.log G ≤ Real.log μ := by
    simpa only [L, G, hμeq] using
      log_maximalTerm_shift_lower hn.1 hfn hd hMbase
  have htermOuter :
      μ * Real.exp ((n j : ℝ) * (h - d)) ≤ B := by
    have hjterm := gapTerm_le_maxModulus hn.1 hfn hfdiff hbound
      (Real.exp_pos (σ + h)) j
    have heq : ‖a j‖ * (Real.exp (σ + h)) ^ n j =
        μ * Real.exp ((n j : ℝ) * (h - d)) := by
      dsimp [μ]
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 1
      ring
    simpa only [B, heq] using hjterm
  have hnBound : (n j : ℝ) * (h - d) ≤ (q - 1) * L + Real.log G := by
    have hprodpos : 0 < μ * Real.exp ((n j : ℝ) * (h - d)) := by positivity
    have hlogterm := Real.strictMonoOn_log.monotoneOn hprodpos hBpos htermOuter
    rw [Real.log_mul hμpos.ne' (Real.exp_ne_zero _), Real.log_exp] at hlogterm
    linarith
  have hnjD : (n j : ℝ) < D * L := by
    have hnSimple : (n j : ℝ) * (h - d) ≤ q * L := by
      have hrL : r * L ≤ L := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1.le hLpos.le
      linarith
    have hqD : q < 4 * q + 16 := by linarith [hqpos]
    rw [show D * L = (4 * q + 16) * L / (h - d) by
      dsimp [D]; ring]
    apply (lt_div_iff₀ hhd).2
    exact hnSimple.trans_lt (mul_lt_mul_of_pos_right hqD hLpos)
  let N : ℕ := Nat.ceil (D * L)
  have hNnonneg : 0 ≤ D * L := mul_nonneg hD.le hLpos.le
  have hjN : n j < N := by
    exact Nat.lt_ceil.2 hnjD
  let s : Finset ℕ := gapHead n N
  have hjs : j ∈ s := (mem_gapHead_iff hn.1).2 hjN
  have hsne : s.Nonempty := ⟨j, hjs⟩
  have hNupper : (N : ℝ) < D * L + 1 := by
    simpa [N] using Nat.ceil_lt_add_one hNnonneg
  have hcardRaw := gapHead_card_le_add hn.1 hη hindex N
  have hcardBound : ((s.card : ℕ) : ℝ) + 1 ≤
      η * D * L + ((K₀ : ℝ) + η + 2) := by
    have hcast : ((s.card : ℕ) : ℝ) ≤
        (K₀ : ℝ) + η * (N : ℝ) + 1 := by
      simpa [s] using hcardRaw
    have hηN : η * (N : ℝ) ≤ η * (D * L + 1) :=
      mul_le_mul_of_nonneg_left hNupper.le hη.le
    nlinarith
  have hfactorBudget : T * ((s.card : ℕ) + 1 : ℝ) ≤ r * L / 4 := by
    have hηidentity : T * (η * D * L) = r * L / 16 := by
      dsimp [η]
      field_simp
    calc
      T * ((s.card : ℕ) + 1 : ℝ) ≤
          T * (η * D * L + ((K₀ : ℝ) + η + 2)) :=
        mul_le_mul_of_nonneg_left hcardBound hT.le
      _ = r * L / 16 + T * ((K₀ : ℝ) + η + 2) := by
        rw [mul_add, hηidentity]
      _ ≤ r * L / 16 + 3 * r * L / 16 := add_le_add_right hLTconst _
      _ = r * L / 4 := by ring
  obtain ⟨phaseCenter, phaseM, phaseν, hphase, hcover⟩ :=
    exists_turan_phase_cover hn.1 a hjs (σ := σ + d) (d := d) hd
  let κ := {q : ℕ // q ∈ phaseGrid d}
  let center : κ → ℂ := fun q =>
    ((σ + d : ℝ) : ℂ) + (phaseCenter q : ℂ) * Complex.I
  have hheadFormula : ∀ q : κ,
      (∑ k ∈ s, (a k * Complex.exp ((n k : ℂ) * ((σ + d : ℝ) : ℂ))) *
          Complex.exp ((n k : ℂ) * ((phaseCenter q : ℂ) * Complex.I))) =
        ∑ k ∈ s, a k * Complex.exp ((n k : ℂ) * center q) := by
    intro q
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [center]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    ring
  let H : κ → ℂ := fun q =>
    ∑ k ∈ s, a k * Complex.exp ((n k : ℂ) * center q)
  let P : κ → ℝ := fun q => turanFactor s.card (phaseM q)
  let Fc : κ → ℂ := fun q => logLift f (center q)
  have hKpos : 0 < s.card := Finset.card_pos.mpr hsne
  have hPpos : ∀ q : κ, 0 < P q := by
    intro q
    dsimp [P, turanFactor]
    positivity
  have hPlog : ∀ q : κ, Real.log (P q) ≤ r * L / 4 := by
    intro q
    have hMcast : (phaseM q : ℝ) ≤ 64 * Real.pi * (s.card : ℝ) / d + 1 := by
      have hMq := (hphase q).1
      have hcast : (phaseM q : ℝ) ≤
          (Nat.ceil (64 * Real.pi * (s.card : ℝ) / d) : ℕ) := by
        exact_mod_cast hMq
      have hx0 : 0 ≤ 64 * Real.pi * (s.card : ℝ) / d := by positivity
      exact hcast.trans (Nat.ceil_lt_add_one hx0).le
    exact (log_turanFactor_le hKpos hd hMcast).trans
      (by simpa [T, P] using hfactorBudget)
  have hphaseLarge : ∀ q : κ, μ ≤ ‖H q‖ * P q := by
    intro q
    have hq := (hphase q).2.2.2.2
    rw [hheadFormula q] at hq
    simpa [μ, H, P] using hq
  have htailAll : ∀ q : κ,
      ‖Fc q - H q‖ ≤ B * Real.exp (-(N : ℝ) * ((h - d) / 2) / 2) * Gtail := by
    intro q
    have ht := logLift_sub_gapHead_norm_le hn.1 hfn hfdiff hbound
      (τ := σ + h) (d := (h - d) / 2) (by positivity) N (center q) (by
        dsimp [center]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
          add_zero]
        linarith)
    simpa only [Fc, H, s, B, Gtail] using ht
  have hNlower : D * L ≤ (N : ℝ) := Nat.le_ceil _
  have hBexp : B ≤ Real.exp (q * L) := by
    calc
      B = Real.exp (Real.log B) := (Real.exp_log hBpos).symm
      _ ≤ Real.exp (q * L) := Real.exp_le_exp.mpr hBlog
  have hdecay := cutoff_exp_decay hhd
    (show D = (4 * q + 16) / (h - d) by rfl) hNlower
  have hcenterLog : ∀ q : κ,
      (1 - r) * L ≤ Real.log ‖logLift f (center q)‖ := by
    simpa only [Fc] using family_center_log_lower Fc H P hμpos hlogμ hLG
      hPpos hphaseLarge hPlog hGtail hBpos.le htailAll hBexp hdecay hLtail hLtwo
  -/
  have hboundary : ∀ q : κ, ∀ z : ℂ, ‖z‖ = 3 →
      ‖logLift f (center q + d * z)‖ ≤ B := by
    intro q z hz
    apply norm_le_maxModulus_of_norm_le hfdiff hbound (Real.exp_pos (σ + h))
    rw [show ‖Complex.exp (center q + d * z)‖ =
      Real.exp ((center q + d * z).re) by rw [Complex.norm_exp]]
    apply Real.exp_le_exp.mpr
    have hzre : z.re ≤ 3 :=
      (le_abs_self z.re).trans (Complex.abs_re_le_norm z) |>.trans_eq hz
    dsimp [center]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
      add_zero]
    nlinarith
  have hcardκ : 16 * (Fintype.card κ : ℝ) < Real.exp (β / 2) := by
    have hcardNat : Fintype.card κ ≤ Nat.ceil (4 * Real.pi / d) + 1 := by
      simpa [κ] using phaseGrid_card_le d
    have hcardReal : (Fintype.card κ : ℝ) ≤
        ((Nat.ceil (4 * Real.pi / d) + 1 : ℕ) : ℝ) := by exact_mod_cast hcardNat
    exact (mul_le_mul_of_nonneg_left hcardReal (by norm_num)).trans_lt hgrid
  have hCpos : 0 < (1 - r) * L := mul_pos (sub_pos.mpr hr1) hLpos
  obtain ⟨α, hαleft, hαright, hcommon⟩ :=
    exists_common_scaled_disk_shift (logLift f) (logLift_differentiable hfdiff)
      center hd (show 1 ≤ B by linarith) hCpos hβ hboundary hcenterLog hcardκ
  let σ' : ℝ := σ + d + d * α
  have hσ'X : X ≤ σ' := by
    have hdαlower : d * (-(1 / 2 : ℝ)) ≤ d * α :=
      mul_le_mul_of_nonneg_left hαleft.le hd.le
    dsimp [σ']
    linarith
  refine ⟨σ', hσ'X, ?_⟩
  have hσ'outer : σ' ≤ σ + h := by
    have hdαupper : d * α ≤ d * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hαright hd.le
    dsimp [σ']
    linarith
  have hupper : ∀ t : ℝ, ‖logLift f (σ' + t * Complex.I)‖ ≤ B := by
    intro t
    apply norm_le_maxModulus_of_norm_le hfdiff hbound (Real.exp_pos (σ + h))
    rw [show ‖Complex.exp (σ' + t * Complex.I)‖ = Real.exp σ' by
      rw [Complex.norm_exp]
      simp]
    exact Real.exp_le_exp.mpr hσ'outer
  have hDelta : 0 ≤ q - (1 - r) := by linarith
  have hlogGap : Real.log B - (1 - r) * L ≤ (q - (1 - r)) * L := by
    linarith
  have hlog65 : 0 < Real.log (6 / 5) := Real.log_pos (by norm_num)
  have hcommonToY : y₀ * Real.log B ≤
      (1 - r) * L - 2 * (Real.log B - (1 - r) * L + 1) -
        β * ((Real.log B - (1 - r) * L) / Real.log (6 / 5)) := by
    have hdivGap : (Real.log B - (1 - r) * L) / Real.log (6 / 5) ≤
        ((q - (1 - r)) * L) / Real.log (6 / 5) :=
      div_le_div_of_nonneg_right hlogGap hlog65.le
    have hβdiv := mul_le_mul_of_nonneg_left hdivGap hβ
    have hyBlog : y₀ * Real.log B ≤ y₀ * q * L :=
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hBlog hy₀.le
    have hmarginUse : 2 ≤
        ((1 - r) - 2 * (q - (1 - r)) -
          β * ((q - (1 - r)) / Real.log (6 / 5)) - y₀ * q) * L := by
      simpa only [margin] using hLmargin
    have hbudget :
        y₀ * q * L + 2 * ((q - (1 - r)) * L + 1) +
            β * (((q - (1 - r)) * L) / Real.log (6 / 5)) ≤
          (1 - r) * L := by
      calc
        y₀ * q * L + 2 * ((q - (1 - r)) * L + 1) +
              β * (((q - (1 - r)) * L) / Real.log (6 / 5)) ≤
            (y₀ * q * L + 2 * ((q - (1 - r)) * L + 1) +
              β * (((q - (1 - r)) * L) / Real.log (6 / 5))) +
              (((1 - r) - 2 * (q - (1 - r)) -
                β * ((q - (1 - r)) / Real.log (6 / 5)) - y₀ * q) * L - 2) :=
          le_add_of_nonneg_right (sub_nonneg.mpr hmarginUse)
        _ = (1 - r) * L := by ring
    have hsum :
        y₀ * Real.log B + 2 * (Real.log B - (1 - r) * L + 1) +
            β * ((Real.log B - (1 - r) * L) / Real.log (6 / 5)) ≤
          (1 - r) * L := by
      calc
        y₀ * Real.log B + 2 * (Real.log B - (1 - r) * L + 1) +
              β * ((Real.log B - (1 - r) * L) / Real.log (6 / 5)) ≤
            y₀ * q * L + 2 * ((q - (1 - r)) * L + 1) +
              β * (((q - (1 - r)) * L) / Real.log (6 / 5)) := by
          exact add_le_add
            (add_le_add hyBlog
              (mul_le_mul_of_nonneg_left (by linarith [hlogGap]) (by norm_num)))
            hβdiv
        _ ≤ (1 - r) * L := hbudget
    linarith
  have hlower : ∀ t : ℝ,
      y₀ * Real.log B ≤ Real.log ‖logLift f (σ' + t * Complex.I)‖ := by
    intro t
    obtain ⟨q₀, u, hexp, hdist⟩ := hcover t
    let v : ℝ := ((u + 2 * Real.pi) - phaseCenter q₀) / d
    have hv : |v| < 9 / 16 := by
      dsimp [v]
      rw [abs_div, abs_of_pos hd]
      calc
        |u + 2 * Real.pi - phaseCenter q₀| / d < (9 * d / 16) / d :=
          div_lt_div_of_pos_right hdist hd
        _ = 9 / 16 := by field_simp
    have hαabs : |α| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    have hnormDisk : ‖(α : ℂ) + (v : ℂ) * Complex.I‖ ≤ 1 := by
      rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1),
        Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, zero_add]
      rw [← pow_two α, ← pow_two v]
      have hαsq : |α| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by gcongr
      have hvsq : |v| ^ 2 ≤ (9 / 16 : ℝ) ^ 2 := by gcongr
      rw [← sq_abs α, ← sq_abs v]
      calc
        |α| ^ 2 + |v| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 + (9 / 16 : ℝ) ^ 2 :=
          add_le_add hαsq hvsq
        _ ≤ (1 : ℝ) ^ 2 := by norm_num
    have hc := hcommon q₀ v hnormDisk
    have hpoint : center q₀ + d * ((α : ℂ) + (v : ℂ) * Complex.I) =
        (σ' : ℂ) + ((u + 2 * Real.pi : ℝ) : ℂ) * Complex.I := by
      dsimp [center, σ', v]
      push_cast
      field_simp [hd.ne']
      ring
    rw [hpoint] at hc
    have heqLift : logLift f ((σ' : ℂ) + ((u + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        logLift f ((σ' : ℂ) + (t : ℂ) * Complex.I) := by
      dsimp [logLift]
      congr 1
      rw [Complex.exp_add, Complex.exp_add]
      congr 1
      rw [show ((u + 2 * Real.pi : ℝ) : ℂ) * Complex.I =
          (u : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, hexp]
    rw [heqLift] at hc
    exact hcommonToY.trans hc
  exact verticalRatio_gt_of_log_bounds hyy₀ hy₀ hMouter hupper hlower

/-- The quantitative fixed-scale theorem, with the asymptotic choice of scales
made above, gives arbitrarily large good logarithmic radii for every target
strictly below one. -/
private lemma hasVerticalGoodLines_of_fabry_series {f : ℂ → ℂ} {n : ℕ → ℕ}
    (hn : HasFabryGaps n) {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    (hf : OfFiniteOrder f) : HasVerticalGoodLines (logLift f) := by
  obtain ⟨hfdiff, c, hc, A, _hA, hbound⟩ := hf
  have hconst := not_constant_of_gap_series hn.1 ha hfn
  intro y hy
  let y₀ : ℝ := (max y 0 + 1) / 2
  have hmaxOne : max y 0 < 1 := max_lt hy zero_lt_one
  have hyy₀ : y < y₀ := by
    have hym : y ≤ max y 0 := le_max_left _ _
    dsimp [y₀]
    linarith
  have hy₀ : 0 < y₀ := by
    have hm0 : 0 ≤ max y 0 := le_max_right _ _
    dsimp [y₀]
    linarith
  have hy₀one : y₀ < 1 := by
    dsimp [y₀]
    linarith
  obtain ⟨r, h, d, β, hr, hr1, hh, hd, hdh, hβ, hq2, hgrid, hcoeff⟩ :=
    exists_admissible_scale A hy₀one
  exact frequently_verticalRatio_gt_of_scale hn ha hfn hfdiff hc hbound hconst
    hyy₀ hy₀ hr hr1 hh hd hdh hβ hq2 hgrid hcoeff

private lemma eventually_ratio_le_one {f : ℂ → ℂ} {n : ℕ → ℕ}
    (hn : StrictMono n) {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    (hf : OfFiniteOrder f) : ∀ᶠ r : ℝ in atTop, ratio r f ≤ 1 := by
  obtain ⟨hfdiff, c, hc, A, hA, hbound⟩ := hf
  have hnonconst := not_constant_of_gap_series hn ha hfn
  filter_upwards [eventually_ge_atTop 0,
    eventually_one_lt_maxModulus hfdiff hnonconst (c := c) (a := A) hbound] with r hr hmax
  exact ratio_le_one_of_one_lt_maxModulus hr hbound hmax

/-- Filter-level form of the substantive lower half of Fuchs' theorem. -/
private def HasFuchsGoodRadii (f : ℂ → ℂ) : Prop :=
  ∀ y < (1 : ℝ), ∃ᶠ r : ℝ in atTop, y < ratio r f

private lemma hasFuchsGoodRadii_of_hasVerticalGoodLines (f : ℂ → ℂ)
    (h : HasVerticalGoodLines (logLift f)) : HasFuchsGoodRadii f := by
  intro y hy
  apply Real.tendsto_exp_atTop.frequently
  simpa only [ratio_exp_eq_verticalRatio] using h y hy

/-- A convenient order-theoretic interface for the final limsup argument. -/
private lemma limsup_eq_one_of_eventually_le_of_frequently_gt
    {α : Type*} {l : Filter α} [NeBot l] (u : α → ℝ)
    (hupper : ∀ᶠ x in l, u x ≤ 1)
    (hlower : ∀ y < (1 : ℝ), ∃ᶠ x in l, y < u x) :
    limsup u l = 1 := by
  have hbounded : IsBoundedUnder (· ≤ ·) l u := ⟨1, hupper⟩
  have hcobounded : IsCoboundedUnder (· ≤ ·) l u := by
    unfold IsCoboundedUnder IsCobounded
    refine ⟨0, fun b hb ↦ ?_⟩
    change ∀ᶠ x in l, u x ≤ b at hb
    obtain ⟨x, hx0, hxb⟩ := ((hlower 0 zero_lt_one).and_eventually hb).exists
    exact hx0.le.trans hxb
  exact le_antisymm (limsup_le_of_le hcobounded hupper)
    ((le_limsup_iff hcobounded hbounded).2 hlower)

private lemma limsup_ratio_eq_one_of_hasFuchsGoodRadii {f : ℂ → ℂ} {n : ℕ → ℕ}
    (hn : StrictMono n) {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z))
    (hf : OfFiniteOrder f) (hgood : HasFuchsGoodRadii f) :
    limsup (fun r ↦ ratio r f) atTop = 1 :=
  limsup_eq_one_of_eventually_le_of_frequently_gt _
    (eventually_ratio_le_one hn ha hfn hf) hgood

/-- Let `f = ∑ aₖzⁿᵏ` be an entire function of finite order whose exponent
sequence has Fabry gaps.  Then the upper limit of the logarithmic
minimum-to-maximum modulus ratio is one.  This is the affirmative resolution
of Erdős Problem 516, due to Fuchs. -/
theorem erdos_516 {f : ℂ → ℂ} {n : ℕ → ℕ}
    (hn : HasFabryGaps n) {a : ℕ → ℂ} (ha : ∀ n, a n ≠ 0)
    (hfn : ∀ z, HasSum (fun k ↦ a k * z ^ n k) (f z)) (hf : OfFiniteOrder f) :
    limsup (fun r ↦ ratio r f) atTop = 1 := by
  apply limsup_ratio_eq_one_of_hasFuchsGoodRadii hn.1 ha hfn hf
  exact hasFuchsGoodRadii_of_hasVerticalGoodLines f
    (hasVerticalGoodLines_of_fabry_series hn ha hfn hf)

#print axioms erdos_516

end Erdos516
