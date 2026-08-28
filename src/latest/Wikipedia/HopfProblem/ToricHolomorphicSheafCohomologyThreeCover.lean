import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverLow

/-!
# Actual cohomology vanishing from an actual three-open cover

The hypotheses below are only genuine term/intersection acyclicity and
literal section equations. The comparison to the original Ext-defined
cohomology is proved using native Mayer--Vietoris twice, its actual
connecting-map naturality, and actual section representatives.

This is a generic gluing theorem. Analytic applications must separately
prove its term-acyclicity and section-equation hypotheses for their
actual sheaf and actual opens.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
  (U : Fin 3 → Opens X)

/-- Actual positive-degree acyclicity from a genuine three-open cover,
proved without a Čech-to-derived comparison assumption. -/
theorem sheaf_higher_subsingleton (hcover : coverOpen U = ⊤)
    (hU : ∀ (i : Fin 3) (n : ℕ),
      Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (U i)))
    (h01 : ∀ n, Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (U 0 ⊓ U 1)))
    (h02 : ∀ n, Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (U 0 ⊓ U 2)))
    (h12 : ∀ n, Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (U 1 ⊓ U 2)))
    (h012 : ∀ n, Subsingleton (CategoryTheory.Sheaf.H'.{0} F (n + 1) (tripleOpen U)))
    (hOne : CechOneExact F U) (hTwo : CechTwoSurjective F U) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F (n + 1)) := by
  cases n with
  | zero =>
      have := hU 0 0
      have := hU 1 0
      have := hU 2 0
      exact sheaf_one_subsingleton F U hcover hOne
  | succ n =>
      cases n with
      | zero =>
          have := hU 0 1
          have := hU 1 1
          have := hU 2 1
          have := h01 0
          have := h02 0
          have := h12 0
          exact sheaf_two_subsingleton F U hcover hTwo
      | succ n =>
          have := hU 0 (n + 2)
          have := hU 1 (n + 2)
          have := hU 2 (n + 2)
          have := h01 (n + 1)
          have := h02 (n + 1)
          have := h12 (n + 1)
          have := h012 n
          exact sheaf_above_two_subsingleton F U hcover n

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover
