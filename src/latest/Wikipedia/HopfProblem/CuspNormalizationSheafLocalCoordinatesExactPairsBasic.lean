import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinates
import Wikipedia.HopfProblem.CuspNormalizationSheafGermComplex

/-!
# Signed restriction maps for every actual local double-branch pair

The source-positive and source-negative plane labels give a uniform ordering
of the two actual analytic branch germs along each source double curve. The
source of restriction is the existing ring of analytic germs restricted to
the actual union of these two planes. The difference map uses precisely the
axis coordinates of the signed lifts.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricCharts ToricFan Triangle NormalizationCurves
open CuspNormalization.Germs CuspNormalization.SheafGermComplex

/-- The actual two branches, ordered positive then negative by the source. -/
def pairLabel (s : Triangle) (k : Fin 3) : Fin 2 → sourcePair s k :=
  ![⟨plusBranch s k, (mem_sourcePair s k _).mpr (plusBranch_ne_axisIndex s k)⟩,
    ⟨minusBranch s k, (mem_sourcePair s k _).mpr (minusBranch_ne_axisIndex s k)⟩]

@[simp] theorem pairLabel_zero (s : Triangle) (k : Fin 3) :
    (pairLabel s k 0).val = plusBranch s k := rfl

@[simp] theorem pairLabel_one (s : Triangle) (k : Fin 3) :
    (pairLabel s k 1).val = minusBranch s k := rfl

theorem pairLabel_surjective (s : Triangle) (k : Fin 3) :
    Function.Surjective (pairLabel s k) := by
  rintro ⟨j, hj⟩
  have hj' : j = plusBranch s k ∨ j = minusBranch s k := by
    rw [sourcePair_eq_branches] at hj
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hj
  rcases hj' with hj' | hj'
  · exact ⟨0, Subtype.ext hj'.symm⟩
  · exact ⟨1, Subtype.ext hj'.symm⟩

/-- Genuine restriction from the local reduced two-plane analytic ring. -/
def pairRestriction (s : Triangle) (k : Fin 3) :
    RestrictedAnalyticGerm (sourcePair s k) →+* (Fin 2 → BranchGerm) :=
  labeledRestriction (sourcePair s k) (pairLabel s k)

/-- Actual ambient pullbacks to the two source-ordered coordinate planes. -/
def pairAmbientRestriction (s : Triangle) (k : Fin 3) :
    AmbientGerm →+* (Fin 2 → BranchGerm) :=
  labeledAmbientRestriction (sourcePair s k) (pairLabel s k)

@[simp] theorem pairAmbientRestriction_zero (s : Triangle) (k : Fin 3)
    (φ : AmbientGerm) :
    pairAmbientRestriction s k φ 0 = toBranch (plusBranch s k) φ := rfl

@[simp] theorem pairAmbientRestriction_one (s : Triangle) (k : Fin 3)
    (φ : AmbientGerm) :
    pairAmbientRestriction s k φ 1 = toBranch (minusBranch s k) φ := rfl

@[simp] theorem pairRestriction_rangeRestrict (s : Triangle) (k : Fin 3)
    (φ : AmbientGerm) :
    pairRestriction s k ((toPlaneUnion (sourcePair s k)).rangeRestrict φ) =
      pairAmbientRestriction s k φ :=
  labeledRestriction_rangeRestrict (sourcePair s k) (pairLabel s k) φ

/-- Covering both actual branch labels makes restriction injective. -/
theorem pairRestriction_injective (s : Triangle) (k : Fin 3) :
    Function.Injective (pairRestriction s k) :=
  labeledRestriction_injective (sourcePair s k) (pairLabel s k)
    (pairLabel_surjective s k)

theorem range_pairRestriction (s : Triangle) (k : Fin 3) :
    Set.range (pairRestriction s k) = Set.range (pairAmbientRestriction s k) :=
  range_labeledRestriction (sourcePair s k) (pairLabel s k)

/-- Difference of the genuine positive and negative axis pullbacks. -/
def pairDifference (s : Triangle) (k : Fin 3) :
    (Fin 2 → BranchGerm) →+ AxisGerm where
  toFun f := axisRestriction (plusAxisIndex s k) (f 0) -
    axisRestriction (minusAxisIndex s k) (f 1)
  map_zero' := by simp
  map_add' f g := by
    simp only [Pi.add_apply, map_add]
    abel

@[simp] theorem pairDifference_apply (s : Triangle) (k : Fin 3)
    (f : Fin 2 → BranchGerm) :
    pairDifference s k f = axisRestriction (plusAxisIndex s k) (f 0) -
      axisRestriction (minusAxisIndex s k) (f 1) := rfl

theorem pairDifference_eq_zero_iff (s : Triangle) (k : Fin 3)
    (f : Fin 2 → BranchGerm) :
    pairDifference s k f = 0 ↔
      axisRestriction (plusAxisIndex s k) (f 0) =
        axisRestriction (minusAxisIndex s k) (f 1) :=
  sub_eq_zero

/-- Every axis germ is a difference of genuine analytic branch germs. -/
theorem pairDifference_surjective (s : Triangle) (k : Fin 3) :
    Function.Surjective (pairDifference s k) := by
  intro g
  refine ⟨![axisExtension (plusAxisIndex s k) g, 0], ?_⟩
  change axisRestriction (plusAxisIndex s k) (axisExtension (plusAxisIndex s k) g) -
    axisRestriction (minusAxisIndex s k) 0 = g
  rw [axisRestriction_extension, map_zero, sub_zero]

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
