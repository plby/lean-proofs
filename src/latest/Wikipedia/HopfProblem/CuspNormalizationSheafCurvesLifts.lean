import Wikipedia.HopfProblem.CuspNormalizationSheafCurvesAffine
import Wikipedia.HopfProblem.CuspNormalizationSheafCurvesInjectivity

/-!
# The inverse boundary projections

The projection of either signed boundary curve to the corresponding actual
double curve is bijective. Its inverse defines the two lifts to the
normalization component; their affine formulas are the translated axis lifts.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves

open ToricCharts ToricFan ToricSpace ToricComponent Triangle

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual projection restricted to the positive boundary. -/
def boundaryProjection (i : Fin 3) (x : componentBoundary (edgeDirection i)) :
    doubleCurve C ε hε i :=
  ⟨componentProjection C ε hε x.1, ⟨x.1, x.2, rfl⟩⟩

theorem boundaryProjection_bijective (i : Fin 3) :
    Function.Bijective (boundaryProjection C ε hε i) := by
  constructor
  · intro x y h
    exact componentProjection_boundary_injective C ε hε i (congrArg Subtype.val h)
  · rintro ⟨x, y, hy, he⟩
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩

/-- The boundary-to-double-curve equivalence, obtained from the actual projection. -/
def boundaryEquiv (i : Fin 3) :
    componentBoundary (edgeDirection i) ≃ doubleCurve C ε hε i :=
  Equiv.ofBijective (boundaryProjection C ε hε i) (boundaryProjection_bijective C ε hε i)

/-- The inverse of the positive boundary projection. -/
def plusBoundaryLift (i : Fin 3) : doubleCurve C ε hε i → componentBoundary (edgeDirection i) :=
  (boundaryEquiv C ε hε i).symm

/-- The inverse of the opposite boundary projection, using the actual gluing shear. -/
def minusBoundaryLift (i : Fin 3) (x : doubleCurve C ε hε i) :
    componentBoundary (-edgeDirection i) :=
  oppositeBoundaryEquiv C (edgeDirection i) (plusBoundaryLift C ε hε i x)

/-- The positive double-curve lift to the actual normalization component. -/
def plusLift (i : Fin 3) (x : doubleCurve C ε hε i) : rayDivisor 0 :=
  (plusBoundaryLift C ε hε i x).1

/-- The negative double-curve lift to the actual normalization component. -/
def minusLift (i : Fin 3) (x : doubleCurve C ε hε i) : rayDivisor 0 :=
  (minusBoundaryLift C ε hε i x).1

@[simp] theorem componentProjection_plusLift (i : Fin 3) (x : doubleCurve C ε hε i) :
    componentProjection C ε hε (plusLift C ε hε i x) = x :=
  congrArg Subtype.val ((boundaryEquiv C ε hε i).apply_symm_apply x)

@[simp] theorem componentProjection_minusLift (i : Fin 3) (x : doubleCurve C ε hε i) :
    componentProjection C ε hε (minusLift C ε hε i x) = x := by
  change componentProjection C ε hε
    (oppositeBoundaryMap C (edgeDirection i) (plusBoundaryLift C ε hε i x)).1 = x
  rw [componentProjection_oppositeBoundaryMap]
  exact componentProjection_plusLift C ε hε i x

theorem plusLift_mem_boundary (i : Fin 3) (x : doubleCurve C ε hε i) :
    plusLift C ε hε i x ∈ componentBoundary (edgeDirection i) :=
  (plusBoundaryLift C ε hε i x).2

theorem minusLift_mem_boundary (i : Fin 3) (x : doubleCurve C ε hε i) :
    minusLift C ε hε i x ∈ componentBoundary (-edgeDirection i) :=
  (minusBoundaryLift C ε hε i x).2

theorem plusLift_range (i : Fin 3) :
    range (plusLift C ε hε i) = componentBoundary (edgeDirection i) := by
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩
    exact plusLift_mem_boundary C ε hε i x
  · intro x hx
    refine ⟨boundaryEquiv C ε hε i ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val ((boundaryEquiv C ε hε i).symm_apply_apply ⟨x, hx⟩)

theorem minusLift_range (i : Fin 3) :
    range (minusLift C ε hε i) = componentBoundary (-edgeDirection i) := by
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩
    exact minusLift_mem_boundary C ε hε i x
  · intro x hx
    let y := (oppositeBoundaryEquiv C (edgeDirection i)).symm ⟨x, hx⟩
    refine ⟨boundaryEquiv C ε hε i y, ?_⟩
    change ((oppositeBoundaryEquiv C (edgeDirection i))
      ((boundaryEquiv C ε hε i).symm (boundaryEquiv C ε hε i y))).1 = x
    rw [Equiv.symm_apply_apply]
    exact congrArg Subtype.val ((oppositeBoundaryEquiv C (edgeDirection i)).apply_symm_apply
      ⟨x, hx⟩)

theorem plusLift_eq_of_project (i : Fin 3) (x : doubleCurve C ε hε i) (y : rayDivisor 0)
    (hy : y ∈ componentBoundary (edgeDirection i))
    (he : componentProjection C ε hε y = x) : plusLift C ε hε i x = y := by
  have h := componentProjection_boundary_injective C ε hε i
    (a₁ := plusBoundaryLift C ε hε i x) (a₂ := ⟨y, hy⟩)
    ((componentProjection_plusLift C ε hε i x).trans he.symm)
  exact congrArg Subtype.val h

theorem minusLift_eq_of_project (i : Fin 3) (x : doubleCurve C ε hε i) (y : rayDivisor 0)
    (hy : y ∈ componentBoundary (-edgeDirection i))
    (he : componentProjection C ε hε y = x) : minusLift C ε hε i x = y := by
  have h := componentProjection_negativeBoundary_injective C ε hε i
    (a₁ := minusBoundaryLift C ε hε i x) (a₂ := ⟨y, hy⟩)
    ((componentProjection_minusLift C ε hε i x).trans he.symm)
  exact congrArg Subtype.val h

@[simp] theorem plusLift_axisMap (s : Triangle) (i : Fin 3) (z : ℂ) :
    plusLift C ε hε i ⟨axisMap C ε hε s i z, axisMap_mem_doubleCurve C ε hε s i z⟩ =
      affineLift C s i (s.edgeStart i) z :=
  plusLift_eq_of_project C ε hε i _ _ (affineLift_start_mem_boundary C s i z)
    (componentProjection_affineLift C ε hε s i _ (edgeStart_ne_axisIndex s i) z)

@[simp] theorem minusLift_axisMap (s : Triangle) (i : Fin 3) (z : ℂ) :
    minusLift C ε hε i ⟨axisMap C ε hε s i z, axisMap_mem_doubleCurve C ε hε s i z⟩ =
      affineLift C s i (s.edgeEnd i) z :=
  minusLift_eq_of_project C ε hε i _ _ (affineLift_end_mem_boundary C s i z)
    (componentProjection_affineLift C ε hε s i _ (edgeEnd_ne_axisIndex s i) z)

end Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves
