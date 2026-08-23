/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset Real
open scoped Topology

noncomputable section

namespace Erdos804

open scoped Classical in
def resolutionScale (n : ℕ) : ℝ :=
  (Real.log (n : ℝ)) ^ 2 / Real.log (Real.log (n : ℝ))

end Erdos804

namespace Erdos804

open scoped Classical in
def HasLocalIndependence {n : ℕ} (G : SimpleGraph (Fin n))
    (s t : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = s →
    ∃ I : Finset (Fin n), I ⊆ S ∧ G.IsNIndepSet t I

end Erdos804

namespace Erdos804

open scoped Classical in
def GuaranteesIndependence (n s t q : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), HasLocalIndependence G s t → q ≤ G.indepNum

end Erdos804

namespace Erdos804

open scoped Classical in
noncomputable def localIndependenceNumber (n s t : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (GuaranteesIndependence n s t) n

end Erdos804

namespace Erdos804

open scoped Classical in
def logWindow (j n : ℕ) : ℕ := ⌊(Real.log (n : ℝ)) ^ j⌋₊

end Erdos804

namespace Erdos804

open scoped Classical in
def logThreshold (n : ℕ) : ℕ := ⌈Real.log (n : ℝ)⌉₊

end Erdos804

namespace Erdos804

open scoped Classical in
def squareValue (n : ℕ) : ℕ :=
  localIndependenceNumber n (logWindow 2 n) (logThreshold n)

end Erdos804

namespace Erdos804

open scoped Classical in
def cubicValue (n : ℕ) : ℕ :=
  localIndependenceNumber n (logWindow 3 n) (logThreshold n)

/-! ## Finite double counting for the lower bound -/

variable {V : Type*} [Fintype V] [DecidableEq V]

end Erdos804

namespace Erdos804

open scoped Classical in
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

end
