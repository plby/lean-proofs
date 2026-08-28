import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesBasic

/-!
# Genuine period classes on every original base neighborhood

Holomorphic coefficients on a base open define the already constructed
genuine extension class of the original restricted period family. The
proved actual neighborhood equivalence returns this class to the
original total sheaf's native cohomology-presheaf group on the literal
base preimage. Its comparison formula, additive structure, and actual
holomorphic-linear-period vanishing are proved in those native groups.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The four literal holomorphic coefficient functions on the actual
base-open subtype, with its inherited original base atlas. -/
abbrev Coefficients (U : Opens B) := Cocycle.Coefficients V U

/-- Constant period characters are actual holomorphic coefficients on
each base open. -/
def constantCoefficients (U : Opens B) (a : Fin 4 → ℂ) : Coefficients (V := V) U :=
  fun j => ContMDiffMap.const (a j)

@[simp] theorem constantCoefficients_apply (U : Opens B) (a : Fin 4 → ℂ)
    (j : Fin 4) (b : U) : constantCoefficients (V := V) U a j b = a j := rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- A genuine native neighborhood class, defined using the inverse of
the proved comparison, not by redefining the neighborhood cohomology. -/
def periodClass (P : HolomorphicPeriodMap V B) (U : Opens B) (a : Coefficients (V := V) U) :
    neighborhoodCohomology P U 1 :=
  (neighborhoodCohomologyEquiv P U 1).symm
    (Cocycle.periodClass (Restriction.restrictedPeriods P U) a)

/-- The actual native neighborhood class has exactly the genuine
extension class of the restricted period family as its comparison. -/
@[simp] theorem periodClass_comparison (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : Coefficients (V := V) U) :
    neighborhoodCohomologyEquiv P U 1 (periodClass P U a) =
      Cocycle.periodClass (Restriction.restrictedPeriods P U) a :=
  (neighborhoodCohomologyEquiv P U 1).apply_symm_apply _

/-- The same formula explicitly names the actual extension class of
the literal restricted-family holomorphic cocycle. -/
theorem periodClass_comparison_classOf (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : Coefficients (V := V) U) :
    neighborhoodCohomologyEquiv P U 1 (periodClass P U a) =
      HolomorphicPicard.CechExtension.classOf
        (Cocycle.cocycle (Restriction.restrictedPeriods P U) a)
        (Cocycle.coverOpen_covers (Restriction.restrictedPeriods P U)) :=
  periodClass_comparison P U a

/-- The actual additive coefficient-to-neighborhood-class map. -/
def periodClassHom (P : HolomorphicPeriodMap V B) (U : Opens B) :
    Coefficients (V := V) U →+ neighborhoodCohomology P U 1 :=
  (neighborhoodCohomologyEquiv P U 1).symm.toAddMonoidHom.comp
    (Cocycle.periodClassHom (Restriction.restrictedPeriods P U))

@[simp] theorem periodClassHom_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : Coefficients (V := V) U) : periodClassHom P U a = periodClass P U a := rfl

@[simp] theorem periodClass_zero (P : HolomorphicPeriodMap V B) (U : Opens B) :
    periodClass P U (0 : Coefficients (V := V) U) = 0 := (periodClassHom P U).map_zero

theorem periodClass_add (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a a' : Coefficients (V := V) U) :
    periodClass P U (a + a') = periodClass P U a + periodClass P U a' :=
  (periodClassHom P U).map_add a a'

theorem periodClass_neg (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : Coefficients (V := V) U) : periodClass P U (-a) = -periodClass P U a :=
  (periodClassHom P U).map_neg a

theorem periodClass_sub (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a a' : Coefficients (V := V) U) :
    periodClass P U (a - a') = periodClass P U a - periodClass P U a' :=
  (periodClassHom P U).map_sub a a'

/-- Actual holomorphic complex-linear period characters vanish in the
original native neighborhood group. -/
@[simp] theorem periodClass_linearCoefficients (P : HolomorphicPeriodMap V B)
    (U : Opens B) (l : Cocycle.LinearCoefficients V U) :
    periodClass P U (Cocycle.linearCoefficients (Restriction.restrictedPeriods P U) l) = 0 := by
  apply (neighborhoodCohomologyEquiv P U 1).injective
  rw [periodClass_comparison, map_zero, Cocycle.periodClass_linearCoefficients]

/-- The original pointwise period-column formula suffices for native
neighborhood-class vanishing, for arbitrary holomorphic coefficients. -/
theorem periodClass_eq_zero_of_linear_periods (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : Coefficients (V := V) U) (l : Cocycle.LinearCoefficients V U)
    (h : ∀ j (b : U), a j b = ∑ k, l k b * (P.periodEquiv b (Pi.single j 1)) k) :
    periodClass P U a = 0 := by
  apply (neighborhoodCohomologyEquiv P U 1).injective
  rw [periodClass_comparison, map_zero]
  exact Cocycle.periodClass_eq_zero_of_linear_periods (Restriction.restrictedPeriods P U) a l h

/-- Adding an actual holomorphic linear period character leaves the
original neighborhood class unchanged. -/
theorem periodClass_add_linearCoefficients (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : Coefficients (V := V) U) (l : Cocycle.LinearCoefficients V U) :
    periodClass P U (a + Cocycle.linearCoefficients (Restriction.restrictedPeriods P U) l) =
      periodClass P U a := by
  rw [periodClass_add, periodClass_linearCoefficients, add_zero]

/-- Their classes still live in the original native neighborhood group. -/
def constantClass (P : HolomorphicPeriodMap V B) (U : Opens B) (a : Fin 4 → ℂ) :
    neighborhoodCohomology P U 1 := periodClass P U (constantCoefficients U a)

/-- The original neighborhood constant-character class compares to
the original restricted-family constant-character extension class. -/
@[simp] theorem constantClass_comparison (P : HolomorphicPeriodMap V B)
    (U : Opens B) (a : Fin 4 → ℂ) :
    neighborhoodCohomologyEquiv P U 1 (constantClass P U a) =
      Cocycle.periodClass (Restriction.restrictedPeriods P U) (constantCoefficients U a) :=
  periodClass_comparison P U _

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClasses
