/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos505

noncomputable def diam {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  sSup {dist x y | (x ∈ E) (y ∈ E)}
def BorsukProperty (d m : ℕ) : Prop :=
  ∀ (E : Set (EuclideanSpace ℝ (Fin d))), Bornology.IsBounded E → diam E = 1 →
    ∃ (c : E → Fin m), ∀ (i : Fin m),
      diam {x : EuclideanSpace ℝ (Fin d) |
        ∃ (h : x ∈ E), c ⟨x, h⟩ = i} < 1
noncomputable def BorsukNumber (d : ℕ) : ℕ :=
  sInf {m | BorsukProperty d m}

variable {σ : Type*} {R : Type*} [CommRing R] (c : R) (p : MvPolynomial σ R)

end Erdos505

theorem Erdos505.not_erdos_505 :
    Not (∀ (d : ℕ), d ≥ 1 → Erdos505.BorsukNumber d = d + 1) := by
  sorry
