import Wikipedia.HopfProblem.CanonicalBundleAlternating
import Mathlib.Analysis.Normed.Module.Alternating.Curry

/-!
# Alternating-covector evaluations of the reference cusp Jacobian

These identities concern genuine continuous alternating covectors on the toric
coordinate space `Fin 3 → ℂ`. The reference Jacobian has columns
`(K*q)e₀`, `-(K*q)e₀ + Ke₁`, and `-(K*q)e₀ + Ke₂`. Alternation removes the
repeated `e₀` terms, leaving the positive factors `K^2*q` and `K^3*q`.
The identification of these columns with the analytic derivative is separate.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open ToricCharts

local notation "E₃" => CoordinateSpace 3
local notation "e₀" => (Pi.single (0 : Fin 3) (1 : ℂ) : E₃)
local notation "e₁" => (Pi.single (1 : Fin 3) (1 : ℂ) : E₃)
local notation "e₂" => (Pi.single (2 : Fin 3) (1 : ℂ) : E₃)

/-- A genuine one-covector is complex linear in its single vector argument. -/
theorem oneCovector_smul (ω : E₃ [⋀^Fin 1]→L[ℂ] ℂ) (a : ℂ) (v : E₃) :
    ω ![a • v] = a * ω ![v] :=
  ω.toAlternatingMap.map_vecCons_smul ![] a v

/-- The scaled coordinate-vector evaluation used in the one-form cusp calculation. -/
theorem oneCovector_scaled_basis (ω : E₃ [⋀^Fin 1]→L[ℂ] ℂ)
    (K q : ℂ) (k : Fin 3) :
    ω ![(K * q) • (Pi.single k 1 : E₃)] =
      (K * q) * ω ![(Pi.single k 1 : E₃)] :=
  oneCovector_smul ω (K * q) (Pi.single k 1)

private theorem twoCovector_shear (ω : E₃ [⋀^Fin 2]→L[ℂ] ℂ)
    (a b c : ℂ) (x y : E₃) :
    ω ![a • x, b • x + c • y] = (a * c) * ω ![x, y] := by
  have hxx : ω ![x, x] = 0 :=
    ω.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have hsecond : ω ![x, b • x + c • y] =
      b * ω ![x, x] + c * ω ![x, y] := by
    change (ω.curryLeft x).toAlternatingMap ![b • x + c • y] =
      b * (ω.curryLeft x).toAlternatingMap ![x] +
        c * (ω.curryLeft x).toAlternatingMap ![y]
    rw [AlternatingMap.map_vecCons_add, AlternatingMap.map_vecCons_smul,
      AlternatingMap.map_vecCons_smul]
    simp only [smul_eq_mul]
  calc
    ω ![a • x, b • x + c • y] = a * ω ![x, b • x + c • y] :=
      ω.toAlternatingMap.map_vecCons_smul ![b • x + c • y] a x
    _ = (a * c) * ω ![x, y] := by
      rw [hsecond, hxx, mul_zero, zero_add]
      ring

/-- The reference Jacobian's first column and either fibre column have factor `K^2*q`.
Taking `k = 1` and `k = 2` gives the two mixed coefficients, with positive sign. -/
theorem twoCovector_referenceJacobian (ω : E₃ [⋀^Fin 2]→L[ℂ] ℂ)
    (K q : ℂ) (k : Fin 3) :
    ω ![(K * q) • e₀, -(K * q) • e₀ + K • (Pi.single k 1 : E₃)] =
      (K ^ 2 * q) * ω ![e₀, (Pi.single k 1 : E₃)] := by
  rw [twoCovector_shear]
  ring

private theorem threeCovector_shear (ω : E₃ [⋀^Fin 3]→L[ℂ] ℂ)
    (a b c d e : ℂ) (x y z : E₃) :
    ω ![a • x, b • x + c • y, d • x + e • z] =
      (a * c * e) * ω ![x, y, z] := by
  have hxx (w : E₃) : ω ![x, x, w] = 0 :=
    ω.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have hxyx : ω ![x, y, x] = 0 :=
    ω.map_eq_zero_of_eq _ (i := 0) (j := 2) rfl (by decide)
  have hmiddle : ω ![x, b • x + c • y, d • x + e • z] =
      b * ω ![x, x, d • x + e • z] + c * ω ![x, y, d • x + e • z] := by
    change (ω.curryLeft x).toAlternatingMap ![b • x + c • y, d • x + e • z] =
      b * (ω.curryLeft x).toAlternatingMap ![x, d • x + e • z] +
        c * (ω.curryLeft x).toAlternatingMap ![y, d • x + e • z]
    rw [AlternatingMap.map_vecCons_add, AlternatingMap.map_vecCons_smul,
      AlternatingMap.map_vecCons_smul]
    simp only [smul_eq_mul]
  have hlast : ω ![x, y, d • x + e • z] =
      d * ω ![x, y, x] + e * ω ![x, y, z] := by
    change ((ω.curryLeft x).curryLeft y).toAlternatingMap ![d • x + e • z] =
      d * ((ω.curryLeft x).curryLeft y).toAlternatingMap ![x] +
        e * ((ω.curryLeft x).curryLeft y).toAlternatingMap ![z]
    rw [AlternatingMap.map_vecCons_add, AlternatingMap.map_vecCons_smul,
      AlternatingMap.map_vecCons_smul]
    simp only [smul_eq_mul]
  calc
    ω ![a • x, b • x + c • y, d • x + e • z] =
        a * ω ![x, b • x + c • y, d • x + e • z] :=
      ω.toAlternatingMap.map_vecCons_smul ![b • x + c • y, d • x + e • z] a x
    _ = (a * c * e) * ω ![x, y, z] := by
      rw [hmiddle, hxx, mul_zero, zero_add, hlast, hxyx, mul_zero, zero_add]
      ring

/-- The full reference Jacobian has the positive top-covector factor `K^3*q`. -/
theorem threeCovector_referenceJacobian (ω : E₃ [⋀^Fin 3]→L[ℂ] ℂ) (K q : ℂ) :
    ω ![(K * q) • e₀, -(K * q) • e₀ + K • e₁, -(K * q) • e₀ + K • e₂] =
      (K ^ 3 * q) * ω ![e₀, e₁, e₂] := by
  rw [threeCovector_shear]
  ring

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
