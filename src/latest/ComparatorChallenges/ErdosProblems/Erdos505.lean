/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos505

open scoped Pointwise


open scoped Classical in
noncomputable def diam {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  sSup {dist x y | (x ∈ E) (y ∈ E)}
open scoped Classical in
def BorsukProperty (d m : ℕ) : Prop :=
  ∀ (E : Set (EuclideanSpace ℝ (Fin d))), Bornology.IsBounded E → diam E = 1 →
    ∃ (c : E → Fin m), ∀ (i : Fin m),
      diam {x : EuclideanSpace ℝ (Fin d) |
        ∃ (h : x ∈ E), c ⟨x, h⟩ = i} < 1
open scoped Classical in
noncomputable def BorsukNumber (d : ℕ) : ℕ :=
  sInf {m | BorsukProperty d m}
open scoped Classical in
def BorsukConjecture : Prop :=
  ∀ (d : ℕ), d ≥ 1 → BorsukNumber d = d + 1
variable {σ : Type*} {R : Type*} [CommRing R] (c : R) (p : MvPolynomial σ R)

end Erdos505


open scoped Classical in
theorem Erdos505.not_erdos_505 :
    Not Erdos505.BorsukConjecture
  := by
  sorry
