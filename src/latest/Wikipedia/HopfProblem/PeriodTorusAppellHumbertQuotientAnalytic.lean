import Wikipedia.HopfProblem.PeriodTorusAppellHumbertQuotient

/-!
# The analytic atlas of an Appell–Humbert associated quotient

The point-dependent holomorphic factors act on the actual vector space
`ℂ² × ℂ`.  Its covering quotient receives an analytic atlas.  The projection
is holomorphic into the existing discrete-quotient atlas of the period
torus; no replacement atlas is installed on the base.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

local notation "I₀" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₂" => modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)

/-- Every diagonal deck transformation is analytic, including its
point-dependent scalar multiplier. -/
theorem diagonalAction_contDiff (g : Multiplicative p.lattice) :
    ContDiff ℂ ω (fun u : ComplexPlane₂ × ℂ ↦
      (u.1 + (g.toAdd : ComplexPlane₂), (F.factor g.toAdd u.1 : ℂ) * u.2)) :=
  (contDiff_fst.add contDiff_const).prodMk
    (((F.holomorphic_factor g.toAdd).comp contDiff_fst).mul contDiff_snd)

theorem diagonalAction_holomorphic (g : Multiplicative p.lattice) :
    ContMDiff I₂ I₂ ω (fun u : ComplexPlane₂ × ℂ ↦
      (u.1 + (g.toAdd : ComplexPlane₂), (F.factor g.toAdd u.1 : ℂ) * u.2)) :=
  (diagonalAction_contDiff F g).contMDiff

/-- Only the associated total space receives a new covering-quotient atlas. -/
@[instance_reducible] def associatedChartedSpace :
    ChartedSpace (ComplexPlane₂ × ℂ) (AssociatedSpace F) :=
  letI := diagonalAction F
  CoveringQuotient.chartedSpace (E := ComplexPlane₂ × ℂ)
    (associatedMap_isQuotientCoveringMap F)

/-- The actual associated quotient is an analytic complex manifold. -/
theorem associatedSpace_isManifold :
    letI := associatedChartedSpace F
    IsManifold I₂ ω (AssociatedSpace F) := by
  let := diagonalAction F
  exact CoveringQuotient.isManifold
    (associatedMap_isQuotientCoveringMap F) ω (diagonalAction_holomorphic F)

/-- The quotient projection from the covering vector space is holomorphic. -/
theorem associatedMap_holomorphic :
    letI := associatedChartedSpace F
    ContMDiff I₂ I₂ ω (associatedMap F) := by
  let := diagonalAction F
  exact CoveringQuotient.contMDiff_project
    (associatedMap_isQuotientCoveringMap F) ω (diagonalAction_holomorphic F)

/-- The line-bundle projection is holomorphic for the base torus's original
`DiscreteQuotient` atlas from `PeriodTori.lean`. -/
theorem projection_holomorphic :
    letI := associatedChartedSpace F
    ContMDiff I₂ I₀ ω (projection F) := by
  let := diagonalAction F
  apply CoveringQuotient.contMDiff_of_comp
    (associatedMap_isQuotientCoveringMap F) I₀ ω
  have hfst : ContMDiff I₂ I₀ ω (fun u : ComplexPlane₂ × ℂ ↦ u.1) :=
    contDiff_fst.contMDiff
  simpa only [Function.comp_def, projection_associatedMap] using
    p.torus_projection_holomorphic.comp hfst

/-- Local lifts of the associated quotient map are holomorphic on their
actual open domains. -/
theorem associatedLocalInverse_holomorphic (u : ComplexPlane₂ × ℂ) :
    letI := associatedChartedSpace F
    letI := diagonalAction F
    ContMDiffOn I₂ I₂ ω
      (CoveringQuotient.localInverse (associatedMap_isQuotientCoveringMap F) u)
      (CoveringQuotient.localInverse (associatedMap_isQuotientCoveringMap F) u).source := by
  let := diagonalAction F
  exact CoveringQuotient.localInverse_holomorphic
    (associatedMap_isQuotientCoveringMap F) ω (diagonalAction_holomorphic F) u

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert
