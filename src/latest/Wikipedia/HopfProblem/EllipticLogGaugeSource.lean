import Wikipedia.HopfProblem.EllipticLogGaugeHolomorphic

/-!
# The displayed logarithmic section in period-matrix coordinates

The global quotient section is exactly
`[(z, (log z / (2 π i)) • Π(z)v)]`.  Every other logarithm with exponential
`z` gives the same actual family point, since the change is an integral
period.  This identifies the holomorphic construction with the source's
formula without assuming a global holomorphic logarithm.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods CuspUniformization

variable (P : HolomorphicPeriodMap ℂ Disc)

/-- The integral period vector has precisely the columns of the source's
period matrix.  This identity requires no covariance hypothesis. -/
theorem periodVector_matrix (v : Lattice) (z : Disc) :
    periodVector P v z = (P.point z).val.matrix *ᵥ (fun i => (v i : ℂ)) := by
  rw [periodVector, HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;>
    simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four, realCast]

/-- The actual holomorphic quotient section is the logarithmic section
displayed in the source. -/
theorem sectionMap_matrix_formula (v : Lattice) (z : BaseStar) :
    (sectionMap P v z : P.TotalSpace) =
      P.quotientMap (z.1, (Complex.log (z.1 : ℂ) / (2 * Real.pi * Complex.I)) •
        ((P.point z.1).val.matrix *ᵥ (fun i => (v i : ℂ)))) := by
  rw [sectionMap_formula, periodVector_matrix]
  rfl

/-- Any normalized logarithm at a point represents the same section. -/
theorem sectionMap_formula_of_exponential (v : Lattice) (z : BaseStar) (s : ℂ)
    (hs : exponential s = (z.1 : ℂ)) :
    (sectionMap P v z : P.TotalSpace) =
      P.quotientMap (z.1, s • periodVector P v z.1) := by
  rw [sectionMap_formula]
  have hlogs : ∃ n : ℤ, logarithm (z.1 : ℂ) = s + n :=
    (exponential_eq_iff _ _).mp ((exponential_logarithm z.2).trans hs.symm)
  simpa only [zero_add] using quotientMap_eq_of_scalar_int P v z.1 0 hlogs

/-- Every ordinary logarithm represents exactly the displayed period-
matrix section, including local holomorphic logarithms. -/
theorem sectionMap_matrix_formula_of_logarithm (v : Lattice) (z : BaseStar) (ℓ : ℂ)
    (hℓ : Complex.exp ℓ = (z.1 : ℂ)) :
    (sectionMap P v z : P.TotalSpace) =
      P.quotientMap (z.1, (ℓ / (2 * Real.pi * Complex.I)) •
        ((P.point z.1).val.matrix *ᵥ (fun i => (v i : ℂ)))) := by
  have hs : exponential (ℓ / (2 * Real.pi * Complex.I)) = (z.1 : ℂ) := by
    rw [exponential, mul_div_cancel₀ _ exponential_factor_ne_zero, hℓ]
  rw [sectionMap_formula_of_exponential P v z _ hs, periodVector_matrix]

/-- The global translation is also independent of the logarithmic
representative at every point of the covering space. -/
theorem gaugeMap_project_of_exponential (v : Lattice) (x : CoverStar) (s : ℂ)
    (hs : exponential s = (x.1.1 : ℂ)) :
    (gaugeMap P v (project P x) : P.TotalSpace) =
      P.quotientMap (x.1.1, x.1.2 + s • periodVector P v x.1.1) := by
  rw [gaugeMap_project]
  exact quotientMap_eq_of_scalar_int P v x.1.1 x.1.2
    ((exponential_eq_iff _ _).mp ((exponential_logarithm x.2).trans hs.symm))

/-- Local logarithmic formulas give one globally defined holomorphic
section of the inherited punctured-family atlas. -/
theorem logarithmic_section (v : Lattice) :
    letI := P.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ FamilyModel) ω
        (sectionMap P v) ∧
      (∀ z : BaseStar, (sectionMap P v z).1.1 = z.1) ∧
      (∀ (z : BaseStar) (ℓ : ℂ), Complex.exp ℓ = (z.1 : ℂ) →
        (sectionMap P v z : P.TotalSpace) =
          P.quotientMap (z.1, (ℓ / (2 * Real.pi * Complex.I)) •
            ((P.point z.1).val.matrix *ᵥ (fun i => (v i : ℂ))))) :=
  ⟨sectionMap_holomorphic P v, sectionMap_base P v,
    sectionMap_matrix_formula_of_logarithm P v⟩

end Wikipedia.HopfProblem.Elliptic.LogGauge
