import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarLocalBasic

/-!
# Local principal presentations of genuine meromorphic functions

These local data retain the original meromorphic section and its full
denominator ideals. The existence theorem is proved separately using
actual analytic preparation and isolated common zeros. This file records
the exact transition compatibility forced by those ideals.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarLocal

open PolarAlgebra

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- A local fraction whose denominator generates the full actual polar
denominator ideal at every point of its original open domain. -/
structure Presentation (s : Section I M ⊤) where
  domain : Opens M
  numerator : HolomorphicFunctionSheaf.Section I M domain
  denominator : HolomorphicFunctionSheaf.Section I M domain
  denominator_ne_zero : ∀ x : domain, holomorphicGerm I M domain x denominator ≠ 0
  fraction_eq : ∀ x : domain, s ⟨x.val, Set.mem_univ x.val⟩ =
    fraction I M domain numerator denominator x
  generates : ∀ x : domain,
    denominatorIdeal (HolomorphicStalk I M x.val) (s ⟨x.val, Set.mem_univ x.val⟩) =
      Ideal.span ({holomorphicGerm I M domain x denominator} : Set _)

namespace Presentation

variable {I M} {s : Section I M ⊤} (A B : Presentation I M s)

/-- The literal intersection of the two presentation domains. -/
abbrev overlap : Opens M := A.domain ⊓ B.domain

/-- First denominator restricted to the actual overlap. -/
def denominatorLeft : HolomorphicFunctionSheaf.Section I M (A.overlap B) :=
  HolomorphicFunctionSheaf.restrictionAlgHom I M inf_le_left A.denominator

/-- Second denominator restricted to the actual overlap. -/
def denominatorRight : HolomorphicFunctionSheaf.Section I M (A.overlap B) :=
  HolomorphicFunctionSheaf.restrictionAlgHom I M inf_le_right B.denominator

theorem denominatorLeft_ne_zero (x : A.overlap B) :
    holomorphicGerm I M (A.overlap B) x (A.denominatorLeft B) ≠ 0 := by
  rw [denominatorLeft, holomorphicGerm_restrict]
  exact A.denominator_ne_zero (Set.inclusion inf_le_left x)

theorem denominatorRight_ne_zero (x : A.overlap B) :
    holomorphicGerm I M (A.overlap B) x (A.denominatorRight B) ≠ 0 := by
  rw [denominatorRight, holomorphicGerm_restrict]
  exact B.denominator_ne_zero (Set.inclusion inf_le_right x)

/-- Two genuine local polar denominators are associated on every overlap
because they generate the same actual denominator ideal. -/
theorem denominators_associated (x : A.overlap B) :
    Associated (holomorphicGerm I M (A.overlap B) x (A.denominatorRight B))
      (holomorphicGerm I M (A.overlap B) x (A.denominatorLeft B)) := by
  apply Ideal.span_singleton_eq_span_singleton.mp
  rw [denominatorRight, denominatorLeft, holomorphicGerm_restrict, holomorphicGerm_restrict]
  exact (B.generates (Set.inclusion inf_le_right x)).symm.trans
    (A.generates (Set.inclusion inf_le_left x))

end Presentation

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarLocal
