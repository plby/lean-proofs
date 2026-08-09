import Mathlib.Analysis.InnerProductSpace.PiL2
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos505

open scoped Pointwise

attribute [local instance] Classical.propDecidable

noncomputable def diam {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  sSup {dist x y | (x ∈ E) (y ∈ E)}
def BorsukProperty (d m : ℕ) : Prop :=
  ∀ (E : Set (EuclideanSpace ℝ (Fin d))), Bornology.IsBounded E → diam E = 1 →
    ∃ (c : E → Fin m), ∀ (i : Fin m),
      diam {x : EuclideanSpace ℝ (Fin d) |
        ∃ (h : x ∈ E), c ⟨x, h⟩ = i} < 1
noncomputable def BorsukNumber (d : ℕ) : ℕ :=
  sInf {m | BorsukProperty d m}
def BorsukConjecture : Prop :=
  ∀ (d : ℕ), d ≥ 1 → BorsukNumber d = d + 1
variable {σ : Type*} {R : Type*} [CommRing R] (c : R) (p : MvPolynomial σ R)

end Erdos505

attribute [local instance] Classical.propDecidable

theorem Erdos505.not_erdos_505 :
    Not Erdos505.BorsukConjecture
  := by
  sorry
