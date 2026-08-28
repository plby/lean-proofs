import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The actual antiholomorphic part of a real cotangent vector

The model used below is the original complex model `ℂ × ComplexPlane₂`.
The operator is the anti-complex-linear part of the real Fréchet
derivative.  No choice of a real-product atlas enters this definition.
-/

noncomputable section

open Complex Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree

abbrev Model := ℂ × ComplexPlane₂

section Covectors

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The usual complex structure, regarded as a real continuous linear map. -/
def complexStructure : E →L[ℝ] E := I • ContinuousLinearMap.id ℝ E

@[simp] theorem complexStructure_apply (v : E) :
    complexStructure v = I • v := rfl

/-- The continuous real-linear projection onto antiholomorphic covectors. -/
def antiPartLinear : (E →L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] ℂ) :=
  (1 / (2 : ℂ)) • (ContinuousLinearMap.id ℝ (E →L[ℝ] ℂ) +
    I • (ContinuousLinearMap.compL ℝ E E ℂ).flip complexStructure)

/-- The antiholomorphic part of an actual real cotangent vector. -/
def antiPart (L : E →L[ℝ] ℂ) : E →L[ℝ] ℂ := antiPartLinear L

@[simp] theorem antiPart_apply (L : E →L[ℝ] ℂ) (v : E) :
    antiPart L v = (L v + I * L (I • v)) / 2 := by
  simp only [antiPart, antiPartLinear, smul_apply,
    add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, complexStructure_apply, smul_eq_mul]
  ring

@[simp] theorem antiPart_zero : antiPart (0 : E →L[ℝ] ℂ) = 0 := map_zero _

theorem antiPart_add (L K : E →L[ℝ] ℂ) :
    antiPart (L + K) = antiPart L + antiPart K := map_add _ _ _

theorem antiPart_complex_smul (c : ℂ) (L : E →L[ℝ] ℂ) :
    antiPart (c • L) = c • antiPart L := by
  ext v
  simp only [antiPart_apply, smul_apply, smul_eq_mul]
  ring

/-- Antiholomorphic covectors are anti-linear for the original complex structure. -/
theorem antiPart_I (L : E →L[ℝ] ℂ) (v : E) :
    antiPart L (I • v) = -I * antiPart L v := by
  simp only [antiPart_apply, smul_smul, I_mul_I, neg_one_smul, map_neg]
  calc
    (L (I • v) + I * -L v) / 2 =
        -I * ((L v + I * L (I • v)) / 2) := by
      linear_combination (L (I • v) / 2) * I_mul_I

theorem antiPart_eq_self {L : E →L[ℝ] ℂ}
    (hL : ∀ v, L (I • v) = -I * L v) : antiPart L = L := by
  ext v
  rw [antiPart_apply, hL]
  calc
    (L v + I * (-I * L v)) / 2 = (L v - (I * I) * L v) / 2 := by ring
    _ = L v := by rw [I_mul_I]; ring

@[simp] theorem antiPart_idempotent (L : E →L[ℝ] ℂ) :
    antiPart (antiPart L) = antiPart L := antiPart_eq_self (antiPart_I L)

/-- The actual anti-complex-linear covectors, as a complex subspace. -/
def antiCovectors : Submodule ℂ (E →L[ℝ] ℂ) where
  carrier := {L | ∀ v, L (I • v) = -I * L v}
  zero_mem' := by simp
  add_mem' := by
    intro L K hL hK v
    simp only [add_apply, hL v, hK v, mul_add]
  smul_mem' := by
    intro c L hL v
    simp only [smul_apply, smul_eq_mul, hL v]
    ring

abbrev AntiCovector (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] := ↥(antiCovectors (E := E))

theorem antiPart_mem (L : E →L[ℝ] ℂ) : antiPart L ∈ antiCovectors := antiPart_I L

/-- A genuinely complex-linear covector has zero antiholomorphic part. -/
theorem antiPart_restrictScalars (L : E →L[ℂ] ℂ) :
    antiPart (L.restrictScalars ℝ) = 0 := by
  ext v
  rw [antiPart_apply]
  change (L v + I * L (I • v)) / 2 = 0
  rw [map_smul, smul_eq_mul]
  calc
    (L v + I * (I * L v)) / 2 = (L v + (I * I) * L v) / 2 := by ring
    _ = 0 := by rw [I_mul_I]; ring

end Covectors

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The full actual `(0,1)` differential in the original complex model. -/
def dbar (f : E → ℂ) (q : E) : E →L[ℝ] ℂ := antiPart (fderiv ℝ f q)

@[simp] theorem dbar_apply (f : E → ℂ) (q v : E) :
    dbar f q v = (fderiv ℝ f q v + I * fderiv ℝ f q (I • v)) / 2 :=
  antiPart_apply _ _

theorem dbar_I (f : E → ℂ) (q v : E) :
    dbar f q (I • v) = -I * dbar f q v := antiPart_I _ _

theorem dbar_mem (f : E → ℂ) (q : E) : dbar f q ∈ antiCovectors := antiPart_mem _

theorem dbar_congr {f g : E → ℂ} {q : E} (h : f =ᶠ[𝓝 q] g) :
    dbar f q = dbar g q := by
  unfold dbar
  rw [h.fderiv_eq]

theorem dbar_add {f g : E → ℂ} {q : E}
    (hf : DifferentiableAt ℝ f q) (hg : DifferentiableAt ℝ g q) :
    dbar (f + g) q = dbar f q + dbar g q := by
  rw [dbar, fderiv_add hf hg, antiPart_add]
  rfl

theorem dbar_const_mul (c : ℂ) {f : E → ℂ} {q : E}
    (hf : DifferentiableAt ℝ f q) :
    dbar (fun x => c * f x) q = c • dbar f q := by
  change antiPart (fderiv ℝ (c • f) q) = c • dbar f q
  rw [fderiv_const_smul hf, antiPart_complex_smul]
  rfl

theorem dbar_zero_of_differentiableAt {f : E → ℂ} {q : E}
    (hf : DifferentiableAt ℂ f q) : dbar f q = 0 := by
  rw [dbar, hf.fderiv_restrictScalars ℝ]
  exact antiPart_restrictScalars _

/-- Smoothness of the actual operator-valued antiholomorphic differential. -/
theorem contDiff_dbar {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dbar f) :=
  antiPartLinear.contDiff.comp (contDiff_infty_iff_fderiv.mp hf).2

end Derivatives

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree
