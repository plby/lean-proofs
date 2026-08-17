/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 755

The mathematical proof and the correspondence between its lemmas and the
formal development are documented in `tex/755.tex`.
-/

open Filter Metric
open scoped BigOperators EuclideanGeometry Asymptotics RealInnerProductSpace SimpleGraph

namespace Erdos755

/-- A three-point set whose pairwise distances are all equal to `side`. -/
def IsEquilateralTriangle {d : ℕ} (side : ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  T.card = 3 ∧ ∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q = side

/-- A unit equilateral triangle in Euclidean `d`-space. -/
def IsUnitEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsEquilateralTriangle 1 T

/-- Number of unit equilateral triangles spanned by a finite point set. -/
noncomputable def unitEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsUnitEquilateralTriangle T).card

/-- Maximum number of unit equilateral triangles spanned by `n` points in Euclidean `d`-space. -/
noncomputable def TUnit (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ unitEquilateralTriangleCount d P = m}

theorem erdos_755 :
    ∃ o : ℕ → ℝ,
      o =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ∧
        ∀ᶠ n in atTop,
          (TUnit 6 n : ℝ) ≤ ((1 / 27 : ℝ) + o n) * (n : ℝ) ^ 3 := by
  sorry
