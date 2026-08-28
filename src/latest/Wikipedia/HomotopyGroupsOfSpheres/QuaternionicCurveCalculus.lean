import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPair
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Derivatives used by the quaternionic first-column formula

The complex embedding is a real continuous linear map. Inversion is
differentiated in the quaternion division algebra, preserving multiplication
order. The Schur formula below is therefore an actual curve derivative.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPlane

local notation "ℍ" => Quaternion ℝ

def coeComplexCLM : ℂ →L[ℝ] ℍ where
  toLinearMap := Quaternion.ofComplex.toLinearMap
  cont := continuous_coeComplex

theorem hasDerivAt_coeComplex (f : ℝ → ℂ) (v : ℂ) (x : ℝ)
    (hf : HasDerivAt f v x) : HasDerivAt (fun t ↦ (f t : ℍ)) (v : ℍ) x :=
  coeComplexCLM.hasFDerivAt.comp_hasDerivAt x hf

theorem hasDerivAt_embed (f : ℝ → ℂ) (v : ℂ) (x : ℝ)
    (hf : HasDerivAt f v x) : HasDerivAt (fun t ↦ embed (f t)) (embed v) x :=
  (hasDerivAt_coeComplex f v x hf).mul_const QuaternionicScalars.j

end QuaternionicComplexPlane

namespace QuaternionicBottMatrix

local notation "ℍ" => Quaternion ℝ

theorem hasDerivAt_inverse_at_one (f : ℝ → ℍ) (v : ℍ) (x : ℝ)
    (hf : HasDerivAt f v x) (hx : f x = 1) :
    HasDerivAt (fun t ↦ (f t)⁻¹) (-v) x := by
  have hn : f x ≠ 0 := by rw [hx]; exact one_ne_zero
  have he := (hasFDerivAt_inv' (𝕜 := ℝ) hn).comp_hasDerivAt x hf
  simpa [hx, Function.comp_def, ContinuousLinearMap.mulLeftRight_apply] using he

theorem hasDerivAt_one_add_inverse_at_zero (f : ℝ → ℍ) (v : ℍ) (x : ℝ)
    (hf : HasDerivAt f v x) (hx : f x = 0) :
    HasDerivAt (fun t ↦ (1 + f t)⁻¹) (-v) x :=
  hasDerivAt_inverse_at_one _ _ _ (hf.const_add 1) (by rw [hx, add_zero])

def normalizedSchurVariation (p q y dp dq dz dy dt : ℍ) : ℍ :=
  dp - dq * y + q * dz * y - q * dy + (p - q * y) * dt

theorem hasDerivAt_normalizedSchur (p q z y t : ℝ → ℍ)
    (dp dq dz dy dt : ℍ) (x : ℝ)
    (hp : HasDerivAt p dp x) (hq : HasDerivAt q dq x)
    (hz : HasDerivAt z dz x) (hy : HasDerivAt y dy x) (ht : HasDerivAt t dt x)
    (hz0 : z x = 0) (ht1 : t x = 1) :
    HasDerivAt (fun a ↦ (p a - q a * (1 + z a)⁻¹ * y a) * t a)
      (normalizedSchurVariation (p x) (q x) (y x) dp dq dz dy dt) x := by
  have hi := hasDerivAt_one_add_inverse_at_zero z dz x hz hz0
  have he := (hp.sub ((hq.mul hi).mul hy)).mul ht
  convert he using 1 <;> try rfl
  simp only [Pi.mul_apply, Pi.sub_apply, hz0, ht1, add_zero, inv_one, mul_one,
    normalizedSchurVariation]
  noncomm_ring

end QuaternionicBottMatrix
end Wikipedia.HomotopyGroupsOfSpheres
