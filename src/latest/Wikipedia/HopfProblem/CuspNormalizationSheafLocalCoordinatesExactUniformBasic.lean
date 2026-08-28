import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactTriples

/-!
# Uniform restriction differences for any active branch set

The branch and curve terms are indexed by the actual active coordinate
planes and their incident source double curves. Thus the same map covers
smooth points, double points, and triple points without changing the
geometric labels or imposing formal compatibility as the source ring.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricFan NormalizationCurves
open CuspNormalization.Germs CuspNormalization.SheafGermComplex

/-- Source double-curve labels whose two actual planes are active. -/
abbrev IncidentCurve (s : Triangle) (S : Finset (Fin 3)) :=
  {k : Fin 3 // sourcePair s k ⊆ S}

/-- The active branch selected by the positive lift of an incident curve. -/
def selectedPlusBranch (s : Triangle) (S : Finset (Fin 3)) (k : IncidentCurve s S) : S :=
  ⟨plusBranch s k, k.property ((mem_sourcePair s k _).mpr (plusBranch_ne_axisIndex s k))⟩

/-- The active branch selected by the negative lift of an incident curve. -/
def selectedMinusBranch (s : Triangle) (S : Finset (Fin 3)) (k : IncidentCurve s S) : S :=
  ⟨minusBranch s k, k.property ((mem_sourcePair s k _).mpr (minusBranch_ne_axisIndex s k))⟩

/-- Actual axis restriction differences, uniformly for every active branch set. -/
def orientedDifference (s : Triangle) (S : Finset (Fin 3)) :
    (S → BranchGerm) →+ (IncidentCurve s S → AxisGerm) where
  toFun f k := axisRestriction (plusAxisIndex s k) (f (selectedPlusBranch s S k)) -
    axisRestriction (minusAxisIndex s k) (f (selectedMinusBranch s S k))
  map_zero' := by funext k; simp
  map_add' f g := by
    funext k
    simp only [Pi.add_apply, map_add]
    abel

@[simp] theorem orientedDifference_apply (s : Triangle) (S : Finset (Fin 3))
    (f : S → BranchGerm) (k : IncidentCurve s S) :
    orientedDifference s S f k =
      axisRestriction (plusAxisIndex s k) (f (selectedPlusBranch s S k)) -
        axisRestriction (minusAxisIndex s k) (f (selectedMinusBranch s S k)) := rfl

theorem orientedDifference_eq_zero_iff (s : Triangle) (S : Finset (Fin 3))
    (f : S → BranchGerm) :
    orientedDifference s S f = 0 ↔ ∀ k (hk : sourcePair s k ⊆ S),
      axisRestriction (plusAxisIndex s k) (f (selectedPlusBranch s S ⟨k, hk⟩)) -
        axisRestriction (minusAxisIndex s k) (f (selectedMinusBranch s S ⟨k, hk⟩)) = 0 := by
  constructor
  · intro hf k hk
    exact congrFun hf ⟨k, hk⟩
  · intro hf
    funext k
    exact hf k.val k.property

theorem orientedTripleDifference_ambientRestriction (s : Triangle) (φ : AmbientGerm) :
    orientedTripleDifference s (tripleAmbientRestriction φ) = 0 := by
  have h := (orientedTripleRestriction_exact s).apply_apply_eq_zero
    ((toPlaneUnion (Finset.univ : Finset (Fin 3))).rangeRestrict φ)
  change orientedTripleDifference s
    (tripleRestriction ((toPlaneUnion (Finset.univ : Finset (Fin 3))).rangeRestrict φ)) = 0 at h
  simpa only [tripleRestriction_rangeRestrict] using h

/-- Restricting one actual ambient analytic germ gives zero difference on
every actual incident axis. -/
theorem orientedDifference_ambientRestriction (s : Triangle) (S : Finset (Fin 3))
    (φ : AmbientGerm) : orientedDifference s S (toBranches S φ) = 0 := by
  funext k
  exact congrFun (orientedTripleDifference_ambientRestriction s φ) k.val

/-- The actual singular analytic restriction is killed by the uniform
oriented difference; this is proved using ambient representatives. -/
theorem orientedDifference_restriction (s : Triangle) (S : Finset (Fin 3))
    (φ : RestrictedAnalyticGerm S) : orientedDifference s S (restrictionToBranches S φ) = 0 := by
  obtain ⟨ψ, hψ⟩ := φ.property
  have he : (toPlaneUnion S).rangeRestrict ψ = φ := Subtype.ext hψ
  rw [← he, restrictionToBranches_rangeRestrict]
  exact orientedDifference_ambientRestriction s S ψ

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
