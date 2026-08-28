import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenDolbeaultCohomology
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOne
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarTwo
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionCohomology

/-!
# Unconditional genuine holomorphic cohomology vanishing on `(ℂ*)²`

Both actual global antiholomorphic differential equations on the literal
double-punctured product have been solved by constructed integrals and
exhaustions. Applying the proved open Dolbeault resolution now gives
actual Mathlib Ext-defined cohomology vanishing in every positive degree.
There is no Stein, acyclicity, or comparison premise at this endpoint.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault

def doublePuncturedOpen : Opens (ℂ × ℂ) :=
  ⟨DoublePuncturedDbarOne.domain, DoublePuncturedDbarOne.isOpen_domain⟩

@[simp] theorem mem_doublePuncturedOpen (q : ℂ × ℂ) :
    q ∈ doublePuncturedOpen ↔ q.1 ≠ 0 ∧ q.2 ≠ 0 := Iff.rfl

theorem doublePunctured_closedOneSolvable : ClosedOneSolvable doublePuncturedOpen := by
  intro f g hf hg hclosed
  exact DoublePuncturedDbarOne.exists_smooth_global_dbar_primitive hf hg hclosed

theorem doublePunctured_topSolvable : TopSolvable doublePuncturedOpen := by
  intro w hw
  exact DoublePuncturedDbarTwo.exists_smooth_top_primitive hw

/-- Genuine higher holomorphic cohomology of the actual double-punctured
affine plane is zero, with no additional assumptions. -/
theorem doublePunctured_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) doublePuncturedOpen) (n + 1)) :=
  holomorphic_higher_subsingleton_of_solvable doublePuncturedOpen
    doublePunctured_closedOneSolvable doublePunctured_topSolvable n

theorem doublePunctured_higher_eq_zero (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) doublePuncturedOpen) (n + 1)) :
    a = 0 := (doublePunctured_higher_subsingleton n).elim a 0

/-- The same assertion in the actual ambient cohomology presheaf. -/
theorem doublePunctured_open_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ))
        (n + 1) doublePuncturedOpen) := by
  let e := HolomorphicRestriction.cohomologyEquiv 𝓘(ℂ, ℂ × ℂ) doublePuncturedOpen (n + 1)
  exact ⟨fun a b => e.injective ((doublePunctured_higher_subsingleton n).elim (e a) (e b))⟩

theorem doublePunctured_open_higher_eq_zero (n : ℕ)
    (a : CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ))
        (n + 1) doublePuncturedOpen) : a = 0 :=
  (doublePunctured_open_higher_subsingleton n).elim a 0

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault
