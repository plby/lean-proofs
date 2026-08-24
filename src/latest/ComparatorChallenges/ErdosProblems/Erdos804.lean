/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos804

noncomputable def resolutionScale (n : ℕ) : ℝ :=
  (Real.log (n : ℝ)) ^ 2 / Real.log (Real.log (n : ℝ))

def HasLocalIndependence {n : ℕ} (G : SimpleGraph (Fin n))
    (s t : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = s →
    ∃ I : Finset (Fin n), I ⊆ S ∧ G.IsNIndepSet t I

def GuaranteesIndependence (n s t q : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), HasLocalIndependence G s t → q ≤ G.indepNum

noncomputable def localIndependenceNumber (n s t : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (GuaranteesIndependence n s t) n

noncomputable def logWindow (j n : ℕ) : ℕ := ⌊(Real.log (n : ℝ)) ^ j⌋₊

noncomputable def logThreshold (n : ℕ) : ℕ := ⌈Real.log (n : ℝ)⌉₊

noncomputable def squareValue (n : ℕ) : ℕ :=
  localIndependenceNumber n (logWindow 2 n) (logThreshold n)

noncomputable def cubicValue (n : ℕ) : ℕ :=
  localIndependenceNumber n (logWindow 3 n) (logThreshold n)

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem erdos_804 :
    ∃ c₂ C₂ c₃ C₃ : ℝ,
      0 < c₂ ∧ 0 < C₂ ∧ 0 < c₃ ∧ 0 < C₃ ∧
      ∀ᶠ n : ℕ in atTop,
        c₂ * resolutionScale n ≤ (squareValue n : ℝ) ∧
        (squareValue n : ℝ) ≤ C₂ * Real.log (n : ℝ) ^ 2 ∧
        c₃ * resolutionScale n ≤ (cubicValue n : ℝ) ∧
        (cubicValue n : ℝ) ≤ C₃ * resolutionScale n := by
  sorry

end Erdos804
