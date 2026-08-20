module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic

/-!
## Definitions related to Schwarz's lemma
-/

open scoped ComplexConjugate
noncomputable section

variable {w z a : ℂ} {r : ℝ}

/-- The particular Möbius transform we need for Schwarz-Pick -/
@[expose] public def mobius (w z : ℂ) : ℂ :=
  (w - z) / (1 - conj w * z)

/-- As a definition, for simp convenience -/
public lemma mobius_def (w z : ℂ) : mobius w z = (w - z) / (1 - conj w * z) := by rfl
