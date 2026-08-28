import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic

/-!
# Actual antiholomorphic covectors on the original three-dimensional model

Equality is detected on the three original complex coordinate directions by
real linearity and the proved antiholomorphic complex-structure relation.
The base covector is the actual differential of complex conjugation of the
original base coordinate.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms

open Complex HolomorphicDolbeaultThree
open scoped BigOperators ComplexConjugate

private theorem model_complex_smul_decomposition (c : ℂ) (v : Model) :
    c • v = c.re • v + c.im • (I • v) := by
  apply Prod.ext
  · apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, sub_eq_add_neg]
  · ext j
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, sub_eq_add_neg]

private theorem antiCovector_smul_congr (L K : AntiCovector Model)
    (c : ℂ) (v : Model) (hv : L.val v = K.val v) :
    L.val (c • v) = K.val (c • v) := by
  rw [model_complex_smul_decomposition]
  simp only [map_add, L.val.map_smul, K.val.map_smul, L.property v, K.property v, hv]

/-- Actual anti-complex-linear covectors on the unchanged product model are
determined by their values on its three original complex coordinate vectors. -/
theorem antiCovector_ext (L K : AntiCovector Model)
    (hbase : L.val (1, 0) = K.val (1, 0))
    (hvertical : ∀ i : Fin 2,
      L.val (0, Pi.single i 1) = K.val (0, Pi.single i 1)) : L = K := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  have he : v = v.1 • (1, (0 : ComplexPlane₂)) +
      v.2 0 • (0, Pi.single (0 : Fin 2) (1 : ℂ)) +
      v.2 1 • (0, Pi.single (1 : Fin 2) (1 : ℂ)) := by
    apply Prod.ext
    · simp
    · ext i
      fin_cases i <;> simp
  calc
    L.val v = L.val (v.1 • (1, (0 : ComplexPlane₂))) +
        L.val (v.2 0 • (0, Pi.single (0 : Fin 2) (1 : ℂ))) +
        L.val (v.2 1 • (0, Pi.single (1 : Fin 2) (1 : ℂ))) := by
      conv_lhs => rw [he]
      rw [map_add, map_add]
    _ = K.val (v.1 • (1, (0 : ComplexPlane₂))) +
        K.val (v.2 0 • (0, Pi.single (0 : Fin 2) (1 : ℂ))) +
        K.val (v.2 1 • (0, Pi.single (1 : Fin 2) (1 : ℂ))) := by
      rw [antiCovector_smul_congr L K _ _ hbase,
        antiCovector_smul_congr L K _ _ (hvertical 0),
        antiCovector_smul_congr L K _ _ (hvertical 1)]
    _ = K.val v := by
      conv_rhs => rw [he]
      rw [map_add, map_add]

/-- The antiholomorphic base covector on the original covering model. -/
def baseCovector : AntiCovector Model :=
  ⟨Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ ℂ ComplexPlane₂),
    by
      intro v
      change conj (I * v.1) = -I * conj v.1
      rw [map_mul, Complex.conj_I]⟩

@[simp] theorem baseCovector_apply (v : Model) :
    baseCovector.val v = conj v.1 := rfl

@[simp] theorem baseCovector_base : baseCovector.val (1, 0) = 1 := by
  simp only [baseCovector_apply, map_one]

@[simp] theorem baseCovector_vertical (w : ComplexPlane₂) :
    baseCovector.val (0, w) = 0 := by
  simp only [baseCovector_apply, map_zero]

/-- This covector is the literal full antiholomorphic differential of
the conjugate original base coordinate, not of the holomorphic base coordinate. -/
theorem dbar_conjugate_base (q : Model) :
    dbar (fun w : Model => conj w.1) q = baseCovector.val := by
  change antiPart (fderiv ℝ baseCovector.val q) = baseCovector.val
  rw [ContinuousLinearMap.fderiv]
  exact antiPart_eq_self baseCovector.property

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms
