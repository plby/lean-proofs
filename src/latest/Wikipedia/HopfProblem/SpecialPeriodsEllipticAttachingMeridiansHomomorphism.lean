import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansHomotopyOperations
import Mathlib.Algebra.Group.Commute.Basic

/-!
# Images of genuine peripheral conjugacies in a commuting group

An actual conjugacy of based loops has equal images under a homomorphism
to a group whose elements commute. No commutative-group instance is
required. Applying this to a loop square retains the supplied external
path and uses the conjugacy already proved from the continuous square.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians

variable {X : Type*} [TopologicalSpace X] {a b : X}
variable {G : Type*} [Group G]

/-- The reversed path-composition convention for the fundamental group
still cancels the actual conjugating loop after mapping to a commuting group. -/
theorem homotopic_conjugate_map_eq {p q : Path b b} (K : Path b b)
    (h : p.Homotopic (K.trans (q.trans K.symm)))
    (φ : FundamentalGroup X b →* G) (hcomm : ∀ g h : G, Commute g h) :
    φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
      φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) := by
  have hclass : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk K))⁻¹ *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q) *
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk K) :=
    Path.Homotopic.Quotient.eq.mpr h
  rw [hclass, map_mul, map_mul, map_inv]
  exact (hcomm _ _).inv_mul_cancel

namespace LoopSquare

/-- A literal continuous loop square gives equal images for the loop
based using any external path and its final loop in a commuting target. -/
theorem map_whisker_eq {p : Path a a} {q : Path b b} (S : LoopSquare p q)
    (τ : Path b a) (φ : FundamentalGroup X b →* G)
    (hcomm : ∀ g h : G, Commute g h) :
    φ (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (τ.trans (p.trans τ.symm)))) =
        φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) :=
  homotopic_conjugate_map_eq (τ.trans S.tail) (S.homotopic_whisker_conjugate τ) φ hcomm

end LoopSquare

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians
