import Wikipedia.HopfProblem.CuspCircleNormalTrivializationAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual real-linear normal-frame equivalences and joint regularity

The two explicit fibre maps are continuous real-linear equivalences with
the denominators and inverses proved in the algebra file. Both the maps
and their inverses depend jointly real analytically on the complex base
coordinate and the two normal coordinates. The regularity statements
are given for arbitrary differentiability order, including `ω` and `∞`.
-/

noncomputable section

open scoped ComplexConjugate ContDiff

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

variable {n : WithTop ℕ∞}

/-- The denominator is a real polynomial in the actual complex coordinate. -/
theorem contDiff_denominator : ContDiff ℝ n denominator := by
  have hre : ContDiff ℝ n (fun a : ℂ => a.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ n (fun a : ℂ => a.im) := Complex.imCLM.contDiff
  exact contDiff_const.add ((hre.mul hre).add (him.mul him))

/-- The inverse denominator is globally real analytic because it is positive. -/
theorem contDiff_inverseDenominator :
    ContDiff ℝ n (fun a : ℂ => (denominator a)⁻¹) :=
  contDiff_denominator.inv denominator_ne_zero

/-- Joint regularity of the lower frame in the base and both fibre coordinates. -/
theorem contDiff_lowerMap :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => lowerMap q.1 q.2) := by
  have ha : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.1) := contDiff_fst
  have hz : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hw : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hc : ContDiff ℝ n (fun z : ℂ => conj z) := Complex.conjCLE.contDiff
  exact (hw.sub ((hc.comp ha).mul (hc.comp hz))).prodMk
    ((ha.mul hw).add (hc.comp hz))

/-- Joint regularity of the upper frame in the base and both fibre coordinates. -/
theorem contDiff_upperMap :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => upperMap q.1 q.2) := by
  have hb : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.1) := contDiff_fst
  have hz : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hw : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hc : ContDiff ℝ n (fun z : ℂ => conj z) := Complex.conjCLE.contDiff
  exact ((hb.mul hw).sub (hc.comp hz)).prodMk
    (hw.add ((hc.comp hb).mul (hc.comp hz)))

theorem contDiff_lowerInverseNumerator :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => lowerInverseNumerator q.1 q.2) := by
  have ha : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.1) := contDiff_fst
  have hz : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hw : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hc : ContDiff ℝ n (fun z : ℂ => conj z) := Complex.conjCLE.contDiff
  exact (hc.comp (hw.sub (ha.mul hz))).prodMk (hz.add ((hc.comp ha).mul hw))

theorem contDiff_upperInverseNumerator :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => upperInverseNumerator q.1 q.2) := by
  have hb : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.1) := contDiff_fst
  have hz : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hw : ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => q.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hc : ContDiff ℝ n (fun z : ℂ => conj z) := Complex.conjCLE.contDiff
  exact (hc.comp ((hb.mul hw).sub hz)).prodMk (hw.add ((hc.comp hb).mul hz))

/-- Joint real analyticity of the actual lower inverse, including its denominator. -/
theorem contDiff_lowerInverse :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => lowerInverse q.1 q.2) :=
  (contDiff_inverseDenominator.comp contDiff_fst).smul contDiff_lowerInverseNumerator

/-- Joint real analyticity of the actual upper inverse, including its denominator. -/
theorem contDiff_upperInverse :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => upperInverse q.1 q.2) :=
  (contDiff_inverseDenominator.comp contDiff_fst).smul contDiff_upperInverseNumerator

/-- The original lower frame as an actual continuous real-linear equivalence. -/
def lowerEquiv (a : ℂ) : (ℂ × ℂ) ≃L[ℝ] (ℂ × ℂ) where
  toFun := lowerMap a
  invFun := lowerInverse a
  left_inv := lowerInverse_lowerMap a
  right_inv := lowerMap_lowerInverse a
  map_add' := lowerMap_add a
  map_smul' := lowerMap_real_smul a
  continuous_toFun := (contDiff_lowerMap (n := ω)).continuous.comp
    (continuous_const.prodMk continuous_id)
  continuous_invFun := (contDiff_lowerInverse (n := ω)).continuous.comp
    (continuous_const.prodMk continuous_id)

/-- The original upper frame as an actual continuous real-linear equivalence. -/
def upperEquiv (b : ℂ) : (ℂ × ℂ) ≃L[ℝ] (ℂ × ℂ) where
  toFun := upperMap b
  invFun := upperInverse b
  left_inv := upperInverse_upperMap b
  right_inv := upperMap_upperInverse b
  map_add' := upperMap_add b
  map_smul' := upperMap_real_smul b
  continuous_toFun := (contDiff_upperMap (n := ω)).continuous.comp
    (continuous_const.prodMk continuous_id)
  continuous_invFun := (contDiff_upperInverse (n := ω)).continuous.comp
    (continuous_const.prodMk continuous_id)

@[simp] theorem lowerEquiv_apply (a : ℂ) (p : ℂ × ℂ) :
    lowerEquiv a p = lowerMap a p := rfl

@[simp] theorem upperEquiv_apply (b : ℂ) (p : ℂ × ℂ) :
    upperEquiv b p = upperMap b p := rfl

@[simp] theorem lowerEquiv_symm_apply (a : ℂ) (p : ℂ × ℂ) :
    (lowerEquiv a).symm p = lowerInverse a p := rfl

@[simp] theorem upperEquiv_symm_apply (b : ℂ) (p : ℂ × ℂ) :
    (upperEquiv b).symm p = upperInverse b p := rfl

theorem contDiff_lowerEquiv :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => lowerEquiv q.1 q.2) :=
  contDiff_lowerMap

theorem contDiff_upperEquiv :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => upperEquiv q.1 q.2) :=
  contDiff_upperMap

theorem contDiff_lowerEquiv_symm :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => (lowerEquiv q.1).symm q.2) :=
  contDiff_lowerInverse

theorem contDiff_upperEquiv_symm :
    ContDiff ℝ n (fun q : ℂ × (ℂ × ℂ) => (upperEquiv q.1).symm q.2) :=
  contDiff_upperInverse

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
