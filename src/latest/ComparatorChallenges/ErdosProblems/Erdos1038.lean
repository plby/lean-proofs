/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped ENNReal
open MeasureTheory

namespace Erdos1038

def IsAdmissible (f : Polynomial ℝ) : Prop :=
  f.Monic ∧ f ≠ 1 ∧
    (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree

abbrev AdmissiblePolynomial := {f : Polynomial ℝ // IsAdmissible f}

def sublevelSet (f : Polynomial ℝ) : Set ℝ := {x | |f.eval x| < 1}

noncomputable def sublevelVolume (f : Polynomial ℝ) : ℝ≥0∞ := volume (sublevelSet f)

noncomputable def infimumLength : ℝ≥0∞ :=
  ⨅ f : AdmissiblePolynomial, sublevelVolume f.1

noncomputable def supremumLength : ℝ≥0∞ :=
  ⨆ f : AdmissiblePolynomial, sublevelVolume f.1

noncomputable def qCeiling : ℝ := 3 - 2 * Real.sqrt 2

noncomputable def H (q : ℝ) : ℝ := 2 * q / (1 + q) ^ 2

noncomputable def s (q : ℝ) : ℝ := (1 - q) / (1 + q)

noncomputable def A (q : ℝ) : ℝ := Real.log (H q) / Real.log q

def IsSoftRoot (q : ℝ) : Prop :=
  q ∈ Set.Ioo 0 qCeiling ∧ A q = s q

noncomputable def qSoft : ℝ := sInf {q : ℝ | IsSoftRoot q}

def exteriorEquation (q u : ℝ) : Prop :=
  A q * Real.log ((u - q) / |1 - q * u|) = Real.log u

noncomputable def uMinus (q : ℝ) : ℝ :=
  sInf {u : ℝ | q⁻¹ < u ∧ exteriorEquation q u}

noncomputable def uPlus (q : ℝ) : ℝ :=
  if q = qSoft then 1 else
    sInf {u : ℝ | 1 < u ∧ u < q⁻¹ ∧ exteriorEquation q u}

noncomputable def Lambda (q : ℝ) : ℝ :=
  H q * (uMinus q + (uMinus q)⁻¹ - uPlus q - (uPlus q)⁻¹)

def IsLambdaMinimizer (q : ℝ) : Prop :=
  q ∈ Set.Ioc 0 qSoft ∧
    ∀ r ∈ Set.Ioc 0 qSoft, Lambda q ≤ Lambda r

noncomputable def qStar : ℝ := sInf {q : ℝ | IsLambdaMinimizer q}

noncomputable def L : ℝ := Lambda qStar

theorem erdos_1038 :
    infimumLength = ENNReal.ofReal L ∧
    supremumLength = ENNReal.ofReal (2 * Real.sqrt 2) := by
  sorry

end Erdos1038
