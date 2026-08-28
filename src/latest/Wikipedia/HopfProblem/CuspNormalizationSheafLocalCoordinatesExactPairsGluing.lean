import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactPairsBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactPairsTables

/-!
# Actual analytic gluing for every source-oriented double-branch pair

The two branch germs glue by extending each to ambient three-space and
subtracting their common axis germ once. The coordinate identities used
here are genuine analytic-germ pullbacks in the actual signed lift charts.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricCharts ToricFan Triangle NormalizationCurves
open CuspNormalization.Germs CuspNormalization.SheafGermComplex

/-- The restrictions of one genuine ambient germ agree on the common axis. -/
theorem pairDifference_ambientRestriction (s : Triangle) (k : Fin 3)
    (φ : AmbientGerm) :
    pairDifference s k (pairAmbientRestriction s k φ) = 0 := by
  change axisRestriction (plusAxisIndex s k) (toBranch (plusBranch s k) φ) -
    axisRestriction (minusAxisIndex s k) (toBranch (minusBranch s k) φ) = 0
  rw [plusAxisRestriction_toBranch, minusAxisRestriction_toBranch, sub_self]

/-- A genuine ambient analytic extension of two compatible branch germs. -/
def pairGluingExtension (s : Triangle) (k : Fin 3)
    (f : Fin 2 → BranchGerm) : AmbientGerm :=
  extendBranch (plusBranch s k) (f 0) + extendBranch (minusBranch s k) (f 1) -
    ambientAxisExtension (s.axisIndex (sourceEdgeIndex k))
      (axisRestriction (plusAxisIndex s k) (f 0))

/-- Inclusion-exclusion restricts to the original two germs whenever their
actual source-positive and source-negative pullbacks agree. -/
theorem pairAmbientRestriction_gluingExtension (s : Triangle) (k : Fin 3)
    (f : Fin 2 → BranchGerm) (hf : pairDifference s k f = 0) :
    pairAmbientRestriction s k (pairGluingExtension s k f) = f := by
  have hpair := (pairDifference_eq_zero_iff s k f).mp hf
  funext i
  fin_cases i
  · change toBranch (plusBranch s k) (pairGluingExtension s k f) = f 0
    simp only [pairGluingExtension, map_add, map_sub, toBranch_extendBranch,
      toPlusBranch_extendMinusBranch, toPlusBranch_ambientAxisExtension]
    rw [← hpair]
    abel
  · change toBranch (minusBranch s k) (pairGluingExtension s k f) = f 1
    simp only [pairGluingExtension, map_add, map_sub, toBranch_extendBranch,
      toMinusBranch_extendPlusBranch, toMinusBranch_ambientAxisExtension]
    abel

/-- Exactness starts from the actual analytic-germ ring of the plane union. -/
theorem pairRestriction_exact (s : Triangle) (k : Fin 3) :
    Function.Exact (pairRestriction s k).toAddMonoidHom (pairDifference s k) := by
  intro f
  change pairDifference s k f = 0 ↔ f ∈ Set.range (pairRestriction s k)
  rw [range_pairRestriction]
  constructor
  · intro hf
    exact ⟨pairGluingExtension s k f, pairAmbientRestriction_gluingExtension s k f hf⟩
  · rintro ⟨φ, rfl⟩
    exact pairDifference_ambientRestriction s k φ

theorem pairDifference_ker (s : Triangle) (k : Fin 3) :
    (pairDifference s k).ker = (pairRestriction s k).toAddMonoidHom.range :=
  AddMonoidHom.exact_iff.mp (pairRestriction_exact s k)

theorem pairDifference_comp_restriction (s : Triangle) (k : Fin 3) :
    (pairDifference s k).comp (pairRestriction s k).toAddMonoidHom = 0 := by
  apply AddMonoidHom.ext
  exact (pairRestriction_exact s k).apply_apply_eq_zero

/-- Compatibility is equivalent to the existence of an actual ambient
analytic extension of the two source-ordered germs. -/
theorem pair_compatible_iff_ambient_extension (s : Triangle) (k : Fin 3)
    (f : Fin 2 → BranchGerm) :
    pairDifference s k f = 0 ↔
      ∃ φ : AmbientGerm, toBranch (plusBranch s k) φ = f 0 ∧
        toBranch (minusBranch s k) φ = f 1 := by
  constructor
  · intro hf
    have he := pairAmbientRestriction_gluingExtension s k f hf
    exact ⟨pairGluingExtension s k f, congrFun he 0, congrFun he 1⟩
  · rintro ⟨φ, hplus, hminus⟩
    apply (pairDifference_eq_zero_iff s k f).mpr
    rw [← hplus, ← hminus, plusAxisRestriction_toBranch, minusAxisRestriction_toBranch]

/-- Both endpoint properties and exactness hold uniformly for every actual
source edge in every toric triangle. -/
theorem pair_short_exact (s : Triangle) (k : Fin 3) :
    Function.Injective (pairRestriction s k) ∧
      Function.Exact (pairRestriction s k).toAddMonoidHom (pairDifference s k) ∧
      Function.Surjective (pairDifference s k) :=
  ⟨pairRestriction_injective s k, pairRestriction_exact s k,
    pairDifference_surjective s k⟩

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
