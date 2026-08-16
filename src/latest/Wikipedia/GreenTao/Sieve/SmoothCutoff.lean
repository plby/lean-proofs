import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Smooth sieve cutoffs

This file packages the smooth cutoff used by the Goldston--Yıldırım
divisor sum.  It also constructs a concrete cutoff from Mathlib's smooth
bump-function infrastructure and proves that its derivative-square
normalizer is positive.
-/

namespace Wikipedia.SzemeredisTheorem

open Function Set MeasureTheory
open scoped ContDiff

/-- A smooth real cutoff taking values in `[0, 1]`, equal to one at zero,
and supported in `[-1, 1]`. -/
structure SmoothSieveCutoff where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  nonneg : ∀ x, 0 ≤ toFun x
  le_one : ∀ x, toFun x ≤ 1
  support_subset : Function.support toFun ⊆ Set.Icc (-1) 1
  zero_of_one_le : ∀ x, 1 ≤ x → toFun x = 0
  value_zero : toFun 0 = 1

namespace SmoothSieveCutoff

instance : CoeFun SmoothSieveCutoff fun _ ↦ ℝ → ℝ :=
  ⟨SmoothSieveCutoff.toFun⟩

@[simp]
theorem coe_apply (χ : SmoothSieveCutoff) (x : ℝ) :
    χ x = χ.toFun x :=
  rfl

/-- Pointwise range formulation of the two bound fields. -/
theorem mem_Icc (χ : SmoothSieveCutoff) (x : ℝ) :
    χ x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨χ.nonneg x, χ.le_one x⟩

/-- A smooth sieve cutoff has compact support. -/
theorem hasCompactSupport (χ : SmoothSieveCutoff) :
    HasCompactSupport χ.toFun :=
  HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc χ.support_subset

/-- The cutoff vanishes outside its prescribed compact interval. -/
theorem eq_zero_of_not_mem_Icc (χ : SmoothSieveCutoff) {x : ℝ}
    (hx : x ∉ Set.Icc (-1) 1) :
    χ x = 0 := by
  by_contra hχ
  exact hx (χ.support_subset hχ)

/-- The derivative-square energy normalizing the Selberg majorant. -/
noncomputable def normalizer (χ : SmoothSieveCutoff) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), |deriv χ.toFun x| ^ 2

theorem normalizer_nonneg (χ : SmoothSieveCutoff) :
    0 ≤ χ.normalizer := by
  rw [normalizer]
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro x _
  exact sq_nonneg _

/-- The derivative-square integrand is continuous. -/
theorem continuous_deriv_sq (χ : SmoothSieveCutoff) :
    Continuous (fun x : ℝ ↦ |deriv χ.toFun x| ^ 2) := by
  exact (χ.smooth.continuous_deriv (by simp)).abs.pow 2

/-- The derivative-square integrand also has compact support. -/
theorem hasCompactSupport_deriv_sq (χ : SmoothSieveCutoff) :
    HasCompactSupport (fun x : ℝ ↦ |deriv χ.toFun x| ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  have htsupport :
      tsupport χ.toFun ⊆ Set.Icc (-1) 1 :=
    closure_minimal χ.support_subset isClosed_Icc
  intro x hx
  apply htsupport
  apply support_deriv_subset
  intro hderiv
  apply hx
  simp [hderiv]

/-- Every object satisfying the cutoff axioms has positive derivative
energy: it changes from `1` at zero to `0` at one. -/
theorem normalizer_pos (χ : SmoothSieveCutoff) :
    0 < χ.normalizer := by
  have hcont :
      ContinuousOn χ.toFun (Set.Icc (0 : ℝ) 1) :=
    χ.smooth.continuous.continuousOn
  have hdiff :
      DifferentiableOn ℝ χ.toFun (Set.Ioo (0 : ℝ) 1) :=
    (χ.smooth.differentiable (by simp)).differentiableOn
  obtain ⟨c, hc, hcderiv⟩ :=
    exists_deriv_eq_slope χ.toFun
      (by norm_num : (0 : ℝ) < 1) hcont hdiff
  have hcderiv_ne : deriv χ.toFun c ≠ 0 := by
    rw [hcderiv, χ.zero_of_one_le 1 le_rfl, χ.value_zero]
    norm_num
  have henergy_cont :
      Continuous (fun x : ℝ ↦ |deriv χ.toFun x| ^ 2) :=
    χ.continuous_deriv_sq
  have henergy_int :
      IntegrableOn (fun x : ℝ ↦ |deriv χ.toFun x| ^ 2)
        (Set.Ioi (0 : ℝ)) :=
    (henergy_cont.integrable_of_hasCompactSupport
      χ.hasCompactSupport_deriv_sq).integrableOn
  have henergy_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun x : ℝ ↦ |deriv χ.toFun x| ^ 2) :=
    Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  rw [normalizer]
  apply
    (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      henergy_nonneg henergy_int).2
  apply
    (henergy_cont.isOpen_support.inter isOpen_Ioi).measure_pos volume
  exact
    ⟨c, pow_ne_zero 2 (abs_ne_zero.mpr hcderiv_ne), hc.1⟩

end SmoothSieveCutoff

/-- A concrete bump with inner radius `1/2` and outer radius `1`. -/
noncomputable def standardSmoothSieveBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The standard smooth sieve cutoff obtained from Mathlib's bump
function on `ℝ`. -/
noncomputable def standardSmoothSieveCutoff : SmoothSieveCutoff where
  toFun := standardSmoothSieveBump
  smooth := ContDiffBump.contDiff standardSmoothSieveBump
  nonneg := fun x ↦ ContDiffBump.nonneg' standardSmoothSieveBump x
  le_one := fun _ ↦ ContDiffBump.le_one standardSmoothSieveBump
  support_subset := by
    rw [ContDiffBump.support_eq]
    intro x hx
    have habs : |x| < 1 := by
      simpa [standardSmoothSieveBump, Metric.mem_ball, Real.dist_eq] using hx
    exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
  zero_of_one_le := by
    intro x hx
    apply ContDiffBump.zero_of_le_dist standardSmoothSieveBump
    change (1 : ℝ) ≤ dist x 0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (zero_le_one.trans hx)]
    exact hx
  value_zero := by
    apply ContDiffBump.one_of_mem_closedBall standardSmoothSieveBump
    simp [standardSmoothSieveBump]

@[simp]
theorem standardSmoothSieveCutoff_apply_zero :
    standardSmoothSieveCutoff 0 = 1 :=
  standardSmoothSieveCutoff.value_zero

theorem standardSmoothSieveCutoff_normalizer_pos :
    0 < standardSmoothSieveCutoff.normalizer :=
  standardSmoothSieveCutoff.normalizer_pos

/-- Existence of a smooth cutoff with positive derivative-square
normalizer. -/
theorem exists_smoothSieveCutoff :
    ∃ χ : SmoothSieveCutoff, 0 < χ.normalizer :=
  ⟨standardSmoothSieveCutoff,
    standardSmoothSieveCutoff_normalizer_pos⟩

end Wikipedia.SzemeredisTheorem
