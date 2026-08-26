import Mathlib

/-!
# Erdős problem 1038: exact definitions

This file fixes the objects in the manuscript
`erdos_1038_complete_proof.tex`.  In particular, `L` is defined through the
one-cut equations; it is not defined to be the polynomial infimum.

The admissibility predicate follows the public Formal Conjectures statement.
The extra results in the manuscript (the exact value of the infimum, the
unique minimizer, numerical enclosures, nonattainment, and the equality case
for the supremum) are recorded separately in `Statement.lean`.
-/

open scoped ENNReal Real
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- A nonconstant monic real polynomial, all of whose roots (with
multiplicity) are real and lie in `[-1, 1]`. -/
def IsAdmissible (f : Polynomial ℝ) : Prop :=
  f.Monic ∧ f ≠ 1 ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree

/-- The class `𝒫` in the manuscript. -/
abbrev AdmissiblePolynomial := {f : Polynomial ℝ // IsAdmissible f}

/-- The strict unit sublevel set `E_f`. -/
def sublevelSet (f : Polynomial ℝ) : Set ℝ := {x | |f.eval x| < 1}

/-- Lebesgue measure of `E_f`. -/
def sublevelVolume (f : Polynomial ℝ) : ℝ≥0∞ := volume (sublevelSet f)

/-- The infimum appearing in Erdős problem 1038. -/
def infimumLength : ℝ≥0∞ :=
  ⨅ f : AdmissiblePolynomial, sublevelVolume f.1

/-- The supremum appearing in Erdős problem 1038. -/
def supremumLength : ℝ≥0∞ :=
  ⨆ f : AdmissiblePolynomial, sublevelVolume f.1

/-- Right endpoint of the `q`-domain used by the one-cut parametrization. -/
def qCeiling : ℝ := 3 - 2 * Real.sqrt 2

/-- `H(q) = 2q/(1+q)^2`. -/
def H (q : ℝ) : ℝ := 2 * q / (1 + q) ^ 2

/-- `s(q) = (1-q)/(1+q)`. -/
def s (q : ℝ) : ℝ := (1 - q) / (1 + q)

/-- Endpoint-atom mass in the one-cut parametrization. -/
def A (q : ℝ) : ℝ := Real.log (H q) / Real.log q

/-- Characterizing predicate for the soft-edge parameter `q_s`. -/
def IsSoftRoot (q : ℝ) : Prop :=
  q ∈ Set.Ioo 0 qCeiling ∧ A q = s q

/-- The soft-edge parameter.  The proof shows that `IsSoftRoot` has exactly
one member, so this infimum is that member. -/
def qSoft : ℝ := sInf {q : ℝ | IsSoftRoot q}

/-- Exterior crossing equation for the one-cut potential. -/
def exteriorEquation (q u : ℝ) : Prop :=
  A q * Real.log ((u - q) / |1 - q * u|) = Real.log u

/-- The unique exterior root in `u > q⁻¹`. -/
def uMinus (q : ℝ) : ℝ :=
  sInf {u : ℝ | q⁻¹ < u ∧ exteriorEquation q u}

/-- The nontrivial root in `1 < u < q⁻¹`, continuously set to `1` at
`q = qSoft`. -/
def uPlus (q : ℝ) : ℝ :=
  if q = qSoft then 1 else
    sInf {u : ℝ | 1 < u ∧ u < q⁻¹ ∧ exteriorEquation q u}

/-- Exact one-cut length function from equation (1.3) of the manuscript. -/
def Lambda (q : ℝ) : ℝ :=
  H q * (uMinus q + (uMinus q)⁻¹ - uPlus q - (uPlus q)⁻¹)

/-- A global minimizer of `Lambda` on `(0, qSoft]`. -/
def IsLambdaMinimizer (q : ℝ) : Prop :=
  q ∈ Set.Ioc 0 qSoft ∧
    ∀ r ∈ Set.Ioc 0 qSoft, Lambda q ≤ Lambda r

/-- The unique minimizer characterized in the manuscript. -/
def qStar : ℝ := sInf {q : ℝ | IsLambdaMinimizer q}

/-- The exact proposed value of the infimum. -/
def L : ℝ := Lambda qStar

end

end Erdos1038
